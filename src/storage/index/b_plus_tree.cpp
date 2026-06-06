#include "storage/index/b_plus_tree.h"

#include <sstream>
#include <string>

#include "buffer/lru_k_replacer.h"
#include "common/config.h"
#include "common/exception.h"
#include "common/logger.h"
#include "common/macros.h"
#include "common/rid.h"
#include "storage/index/index_iterator.h"
#include "storage/page/b_plus_tree_header_page.h"
#include "storage/page/b_plus_tree_internal_page.h"
#include "storage/page/b_plus_tree_leaf_page.h"
#include "storage/page/b_plus_tree_page.h"
#include "storage/page/page_guard.h"

namespace bustub
{

INDEX_TEMPLATE_ARGUMENTS
BPLUSTREE_TYPE::BPlusTree(std::string name, page_id_t header_page_id,
                          BufferPoolManager* buffer_pool_manager,
                          const KeyComparator& comparator, int leaf_max_size,
                          int internal_max_size)
    : index_name_(std::move(name)),
      bpm_(buffer_pool_manager),
      comparator_(std::move(comparator)),
      leaf_max_size_(leaf_max_size),
      internal_max_size_(internal_max_size),
      header_page_id_(header_page_id)
{
  WritePageGuard guard = bpm_ -> FetchPageWrite(header_page_id_);
  // In the original bpt, I fetch the header page
  // thus there's at least one page now
  auto root_header_page = guard.template AsMut<BPlusTreeHeaderPage>();
  // reinterprete the data of the page into "HeaderPage"
  root_header_page -> root_page_id_ = INVALID_PAGE_ID;
  // set the root_id to INVALID
}

/*
 * Helper function to decide whether current b+tree is empty
 */
INDEX_TEMPLATE_ARGUMENTS
auto BPLUSTREE_TYPE::IsEmpty() const  ->  bool
{
  ReadPageGuard guard = bpm_ -> FetchPageRead(header_page_id_);
  auto root_header_page = guard.template As<BPlusTreeHeaderPage>();
  bool is_empty = root_header_page -> root_page_id_ == INVALID_PAGE_ID;
  // Just check if the root_page_id is INVALID
  // usage to fetch a page:
  // fetch the page guard   ->   call the "As" function of the page guard
  // to reinterprete the data of the page as "BPlusTreePage"
  return is_empty;
}
/*****************************************************************************
 * SEARCH
 *****************************************************************************/
/*
 * Return the only value that associated with input key
 * This method is used for point query
 * @return : true means key exists
 */
INDEX_TEMPLATE_ARGUMENTS
auto BPLUSTREE_TYPE::GetValue(const KeyType& key,
                              std::vector<ValueType>* result, Transaction* txn)
     ->  bool
{
  // Read-side latch crabbing: take the header read latch, find the root, then
  // descend acquiring the child's read latch before releasing the parent's.
  ReadPageGuard head_guard = bpm_->FetchPageRead(header_page_id_);
  auto header = head_guard.As<BPlusTreeHeaderPage>();
  if (header->root_page_id_ == INVALID_PAGE_ID)
  {
    return false;
  }

  ReadPageGuard guard = bpm_->FetchPageRead(header->root_page_id_);
  head_guard.Drop();

  auto page = guard.As<BPlusTreePage>();
  while (!page->IsLeafPage())
  {
    auto internal = reinterpret_cast<const InternalPage*>(page);
    int idx = BinaryFind(internal, key);
    page_id_t child_id = internal->ValueAt(idx);
    // Acquire the child latch first (inside the assignment's RHS) and only then
    // release the parent latch (when the old guard is overwritten). This keeps
    // the crab "hand-over-hand" along the search path.
    guard = bpm_->FetchPageRead(child_id);
    page = guard.As<BPlusTreePage>();
  }

  auto leaf = reinterpret_cast<const LeafPage*>(page);
  int idx = BinaryFind(leaf, key);
  if (idx >= 0 && comparator_(leaf->KeyAt(idx), key) == 0)
  {
    result->push_back(leaf->ValueAt(idx));
    return true;
  }
  return false;
}

/*****************************************************************************
 * INSERTION
 *****************************************************************************/
/*
 * Insert constant key & value pair into b+ tree
 * if current tree is empty, start new tree, update root page id and insert
 * entry, otherwise insert into leaf page.
 * @return: since we only support unique key, if user try to insert duplicate
 * keys return false, otherwise return true.
 */


INDEX_TEMPLATE_ARGUMENTS
auto BPLUSTREE_TYPE::Insert(const KeyType& key, const ValueType& value,
                            Transaction* txn)  ->  bool
{
  // ---- Optimistic fast path (advanced "crabbing"). -----------------------
  // Read-latch the search path and take a write latch only on the target leaf.
  // While we still hold the parent's read latch the leaf cannot split or merge
  // (those need the parent's write latch), so upgrading just the leaf is safe.
  // If the leaf turns out to be unsafe (would split) we drop everything and
  // retry with the pessimistic full-write path below.
  {
    ReadPageGuard head_guard = bpm_->FetchPageRead(header_page_id_);
    page_id_t root_id = head_guard.As<BPlusTreeHeaderPage>()->root_page_id_;
    if (root_id != INVALID_PAGE_ID)
    {
      ReadPageGuard cur_guard = bpm_->FetchPageRead(root_id);
      head_guard.Drop();
      // Only worth doing when the tree has an internal level; a single-leaf
      // root is handled by the pessimistic path.
      if (!cur_guard.As<BPlusTreePage>()->IsLeafPage())
      {
        while (true)
        {
          auto internal = cur_guard.As<InternalPage>();
          int idx = BinaryFind(internal, key);
          page_id_t child_id = internal->ValueAt(idx);
          ReadPageGuard child_guard = bpm_->FetchPageRead(child_id);
          if (child_guard.As<BPlusTreePage>()->IsLeafPage())
          {
            child_guard.Drop();
            WritePageGuard leaf_guard = bpm_->FetchPageWrite(child_id);
            cur_guard.Drop();  // parent read latch no longer needed
            auto leaf = leaf_guard.template AsMut<LeafPage>();
            int p = BinaryFind(leaf, key);
            if (p >= 0 && comparator_(leaf->KeyAt(p), key) == 0)
            {
              return false;  // duplicate key
            }
            if (leaf->GetSize() < leaf->GetMaxSize())
            {
              int pos = p + 1;
              leaf->IncreaseSize(1);
              for (int i = leaf->GetSize() - 1; i > pos; --i)
              {
                leaf->SetAt(i, leaf->KeyAt(i - 1), leaf->ValueAt(i - 1));
              }
              leaf->SetAt(pos, key, value);
              return true;
            }
            break;  // leaf is full -> fall back to the pessimistic path
          }
          cur_guard = std::move(child_guard);  // crab to the child
        }
      }
    }
  }

  Context ctx;
  ctx.header_page_ = bpm_->FetchPageWrite(header_page_id_);
  auto header = ctx.header_page_->template AsMut<BPlusTreeHeaderPage>();

  // Empty tree: start a new tree whose root is a single leaf page.
  if (header->root_page_id_ == INVALID_PAGE_ID)
  {
    page_id_t root_id;
    auto basic = bpm_->NewPageGuarded(&root_id);
    auto leaf = basic.template AsMut<LeafPage>();
    leaf->Init(leaf_max_size_);
    leaf->IncreaseSize(1);
    leaf->SetAt(0, key, value);
    header->root_page_id_ = root_id;
    return true;
  }
  ctx.root_page_id_ = header->root_page_id_;

  // Descend to the target leaf with write-latch crabbing. A node is "safe" for
  // insertion when it is not full (size < max), meaning inserting into it cannot
  // trigger a split that propagates to its ancestors. As soon as we reach a safe
  // node we may release every ancestor latch (and the header latch).
  WritePageGuard root_guard = bpm_->FetchPageWrite(header->root_page_id_);
  {
    auto root_page = root_guard.template AsMut<BPlusTreePage>();
    if (root_page->GetSize() < root_page->GetMaxSize())
    {
      ctx.header_page_ = std::nullopt;  // root cannot split -> root id is stable
    }
  }
  ctx.write_set_.push_back(std::move(root_guard));

  while (true)
  {
    auto page = ctx.write_set_.back().template AsMut<BPlusTreePage>();
    if (page->IsLeafPage())
    {
      break;
    }
    auto internal = reinterpret_cast<InternalPage*>(page);
    int idx = BinaryFind(internal, key);
    page_id_t child_id = internal->ValueAt(idx);

    WritePageGuard child_guard = bpm_->FetchPageWrite(child_id);
    auto child_page = child_guard.template AsMut<BPlusTreePage>();
    if (child_page->GetSize() < child_page->GetMaxSize())
    {
      // Child is safe: no split can reach its ancestors, drop all of them.
      ctx.write_set_.clear();
      ctx.header_page_ = std::nullopt;
    }
    ctx.write_set_.push_back(std::move(child_guard));
  }

  // Insert the entry into the leaf, keeping keys sorted.
  auto leaf = ctx.write_set_.back().template AsMut<LeafPage>();
  int idx = BinaryFind(leaf, key);
  if (idx >= 0 && comparator_(leaf->KeyAt(idx), key) == 0)
  {
    return false;  // duplicate key, we only support unique keys
  }
  int insert_pos = idx + 1;
  leaf->IncreaseSize(1);
  for (int i = leaf->GetSize() - 1; i > insert_pos; --i)
  {
    leaf->SetAt(i, leaf->KeyAt(i - 1), leaf->ValueAt(i - 1));
  }
  leaf->SetAt(insert_pos, key, value);

  if (leaf->GetSize() <= leaf->GetMaxSize())
  {
    return true;  // still within capacity, no split needed
  }

  // ---- Leaf overflowed: split it and propagate the separator upward. ----
  // New pages are kept pinned (but unlatched) until the operation finishes.
  std::vector<BasicPageGuard> new_pages;

  page_id_t new_leaf_id;
  auto new_leaf_basic = bpm_->NewPageGuarded(&new_leaf_id);
  auto new_leaf = new_leaf_basic.template AsMut<LeafPage>();
  new_leaf->Init(leaf_max_size_);

  int total = leaf->GetSize();
  int left = total / 2;
  new_leaf->IncreaseSize(total - left);
  for (int i = left; i < total; ++i)
  {
    new_leaf->SetAt(i - left, leaf->KeyAt(i), leaf->ValueAt(i));
  }
  leaf->SetSize(left);
  new_leaf->SetNextPageId(leaf->GetNextPageId());
  leaf->SetNextPageId(new_leaf_id);

  KeyType up_key = new_leaf->KeyAt(0);
  page_id_t up_child = new_leaf_id;
  new_pages.push_back(std::move(new_leaf_basic));

  while (true)
  {
    if (ctx.write_set_.size() == 1)
    {
      // The node that just split is the root: grow the tree by one level.
      page_id_t old_root_id = ctx.write_set_.back().PageId();
      page_id_t new_root_id;
      auto root_basic = bpm_->NewPageGuarded(&new_root_id);
      auto root = root_basic.template AsMut<InternalPage>();
      root->Init(internal_max_size_);
      root->SetValueAt(0, old_root_id);
      root->SetKeyAt(1, up_key);
      root->SetValueAt(1, up_child);
      root->SetSize(2);
      ctx.header_page_->template AsMut<BPlusTreeHeaderPage>()->root_page_id_ = new_root_id;
      new_pages.push_back(std::move(root_basic));
      break;
    }

    // Drop the just-split child; its parent becomes the current node.
    ctx.write_set_.pop_back();
    auto parent = ctx.write_set_.back().template AsMut<InternalPage>();

    // Insert (up_key, up_child) into the parent at the sorted position.
    int pos = parent->GetSize();
    for (int j = 1; j < parent->GetSize(); ++j)
    {
      if (comparator_(parent->KeyAt(j), up_key) > 0)
      {
        pos = j;
        break;
      }
    }
    parent->IncreaseSize(1);
    for (int i = parent->GetSize() - 1; i > pos; --i)
    {
      parent->SetKeyAt(i, parent->KeyAt(i - 1));
      parent->SetValueAt(i, parent->ValueAt(i - 1));
    }
    parent->SetKeyAt(pos, up_key);
    parent->SetValueAt(pos, up_child);

    if (parent->GetSize() <= internal_max_size_)
    {
      break;  // parent absorbed the new child without overflowing
    }

    // Parent overflowed: split it and keep propagating.
    page_id_t new_internal_id;
    auto new_internal_basic = bpm_->NewPageGuarded(&new_internal_id);
    auto new_internal = new_internal_basic.template AsMut<InternalPage>();
    new_internal->Init(internal_max_size_);

    int tot = parent->GetSize();
    int lc = tot / 2;
    up_key = parent->KeyAt(lc);
    int cnt = tot - lc;
    for (int j = 0; j < cnt; ++j)
    {
      new_internal->SetKeyAt(j, parent->KeyAt(lc + j));
      new_internal->SetValueAt(j, parent->ValueAt(lc + j));
    }
    new_internal->SetSize(cnt);
    parent->SetSize(lc);
    up_child = new_internal_id;
    new_pages.push_back(std::move(new_internal_basic));
  }

  return true;
}


/*****************************************************************************
 * REMOVE
 *****************************************************************************/
/*
 * Delete key & value pair associated with input key
 * If current tree is empty, return immediately.
 * If not, User needs to first find the right leaf page as deletion target, then
 * delete entry from leaf page. Remember to deal with redistribute or merge if
 * necessary.
 */

INDEX_TEMPLATE_ARGUMENTS
void BPLUSTREE_TYPE::Remove(const KeyType& key, Transaction* txn)
{
  // ---- Optimistic fast path (see Insert for the rationale). --------------
  // Read-latch the path, write-latch only the leaf. Proceed in place if the
  // leaf stays at or above the minimum after the delete; otherwise fall back
  // to the pessimistic path that can borrow / merge.
  {
    ReadPageGuard head_guard = bpm_->FetchPageRead(header_page_id_);
    page_id_t root_id = head_guard.As<BPlusTreeHeaderPage>()->root_page_id_;
    if (root_id != INVALID_PAGE_ID)
    {
      ReadPageGuard cur_guard = bpm_->FetchPageRead(root_id);
      head_guard.Drop();
      if (!cur_guard.As<BPlusTreePage>()->IsLeafPage())
      {
        while (true)
        {
          auto internal = cur_guard.As<InternalPage>();
          int idx = BinaryFind(internal, key);
          page_id_t child_id = internal->ValueAt(idx);
          ReadPageGuard child_guard = bpm_->FetchPageRead(child_id);
          if (child_guard.As<BPlusTreePage>()->IsLeafPage())
          {
            child_guard.Drop();
            WritePageGuard leaf_guard = bpm_->FetchPageWrite(child_id);
            cur_guard.Drop();
            auto leaf = leaf_guard.template AsMut<LeafPage>();
            int p = BinaryFind(leaf, key);
            if (p < 0 || comparator_(leaf->KeyAt(p), key) != 0)
            {
              return;  // key not present
            }
            if (leaf->GetSize() > leaf->GetMinSize())
            {
              for (int i = p; i < leaf->GetSize() - 1; ++i)
              {
                leaf->SetAt(i, leaf->KeyAt(i + 1), leaf->ValueAt(i + 1));
              }
              leaf->IncreaseSize(-1);
              return;
            }
            break;  // would underflow -> fall back to pessimistic path
          }
          cur_guard = std::move(child_guard);
        }
      }
    }
  }

  Context ctx;
  ctx.header_page_ = bpm_->FetchPageWrite(header_page_id_);
  auto header = ctx.header_page_->template AsMut<BPlusTreeHeaderPage>();
  if (header->root_page_id_ == INVALID_PAGE_ID)
  {
    return;  // empty tree, nothing to remove
  }
  ctx.root_page_id_ = header->root_page_id_;

  // Descend with write-latch crabbing. A node is "safe" for deletion when it
  // stays at or above the minimum after removing one entry (size > min), so a
  // merge / redistribute cannot propagate to its ancestors.
  WritePageGuard root_guard = bpm_->FetchPageWrite(header->root_page_id_);
  {
    auto root_page = root_guard.template AsMut<BPlusTreePage>();
    if (root_page->GetSize() > root_page->GetMinSize())
    {
      ctx.header_page_ = std::nullopt;
    }
  }
  ctx.write_set_.push_back(std::move(root_guard));

  while (true)
  {
    auto page = ctx.write_set_.back().template AsMut<BPlusTreePage>();
    if (page->IsLeafPage())
    {
      break;
    }
    auto internal = reinterpret_cast<InternalPage*>(page);
    int idx = BinaryFind(internal, key);
    page_id_t child_id = internal->ValueAt(idx);

    WritePageGuard child_guard = bpm_->FetchPageWrite(child_id);
    auto child_page = child_guard.template AsMut<BPlusTreePage>();
    if (child_page->GetSize() > child_page->GetMinSize())
    {
      ctx.write_set_.clear();
      ctx.header_page_ = std::nullopt;
    }
    ctx.write_set_.push_back(std::move(child_guard));
  }

  // Remove the key from the leaf.
  auto leaf = ctx.write_set_.back().template AsMut<LeafPage>();
  int idx = BinaryFind(leaf, key);
  if (idx < 0 || comparator_(leaf->KeyAt(idx), key) != 0)
  {
    return;  // key not present
  }
  for (int i = idx; i < leaf->GetSize() - 1; ++i)
  {
    leaf->SetAt(i, leaf->KeyAt(i + 1), leaf->ValueAt(i + 1));
  }
  leaf->IncreaseSize(-1);

  // Resolve underflow, possibly cascading toward the root.
  while (true)
  {
    auto& cur_guard = ctx.write_set_.back();
    auto cur = cur_guard.template AsMut<BPlusTreePage>();
    bool is_root = (cur_guard.PageId() == ctx.root_page_id_);

    if (is_root)
    {
      if (!cur->IsLeafPage() && cur->GetSize() == 1)
      {
        // Root internal page collapsed to a single child: promote that child.
        auto root_internal = reinterpret_cast<InternalPage*>(cur);
        ctx.header_page_->template AsMut<BPlusTreeHeaderPage>()->root_page_id_ =
            root_internal->ValueAt(0);
      }
      else if (cur->IsLeafPage() && cur->GetSize() == 0)
      {
        ctx.header_page_->template AsMut<BPlusTreeHeaderPage>()->root_page_id_ =
            INVALID_PAGE_ID;
      }
      break;
    }

    if (cur->GetSize() >= cur->GetMinSize())
    {
      break;  // no underflow
    }

    // The current node underflowed: borrow from a sibling if possible,
    // otherwise merge with one.
    auto parent =
        ctx.write_set_[ctx.write_set_.size() - 2].template AsMut<InternalPage>();
    int node_index = GetChildIndex(parent, cur_guard.PageId());

    // Try to borrow from the left sibling.
    if (node_index > 0)
    {
      WritePageGuard left_guard =
          bpm_->FetchPageWrite(parent->ValueAt(node_index - 1));
      auto left = left_guard.template AsMut<BPlusTreePage>();
      if (left->GetSize() > left->GetMinSize())
      {
        BorrowFromLeft(cur, left, parent, node_index);
        break;
      }
    }
    // Try to borrow from the right sibling.
    if (node_index < parent->GetSize() - 1)
    {
      WritePageGuard right_guard =
          bpm_->FetchPageWrite(parent->ValueAt(node_index + 1));
      auto right = right_guard.template AsMut<BPlusTreePage>();
      if (right->GetSize() > right->GetMinSize())
      {
        BorrowFromRight(cur, right, parent, node_index);
        break;
      }
    }

    // Neither sibling can spare an entry: merge. We always merge into the left
    // node of the pair and drop the right one, then delete the now-stale
    // separator from the parent.
    if (node_index > 0)
    {
      WritePageGuard left_guard =
          bpm_->FetchPageWrite(parent->ValueAt(node_index - 1));
      auto left = left_guard.template AsMut<BPlusTreePage>();
      MergeNodes(left, cur, parent, node_index);
    }
    else
    {
      WritePageGuard right_guard =
          bpm_->FetchPageWrite(parent->ValueAt(node_index + 1));
      auto right = right_guard.template AsMut<BPlusTreePage>();
      MergeNodes(cur, right, parent, node_index + 1);
    }
    // Release the current node's latch and continue checking the parent.
    ctx.write_set_.pop_back();
  }
}

/*****************************************************************************
 * REMOVE HELPERS
 *****************************************************************************/

INDEX_TEMPLATE_ARGUMENTS
auto BPLUSTREE_TYPE::GetChildIndex(InternalPage* parent, page_id_t child_id)
     ->  int
{
  for (int i = 0; i < parent->GetSize(); ++i)
  {
    if (parent->ValueAt(i) == child_id)
    {
      return i;
    }
  }
  return -1;
}

INDEX_TEMPLATE_ARGUMENTS
void BPLUSTREE_TYPE::RemoveFromInternal(InternalPage* parent, int index)
{
  for (int i = index; i < parent->GetSize() - 1; ++i)
  {
    parent->SetKeyAt(i, parent->KeyAt(i + 1));
    parent->SetValueAt(i, parent->ValueAt(i + 1));
  }
  parent->IncreaseSize(-1);
}

INDEX_TEMPLATE_ARGUMENTS
void BPLUSTREE_TYPE::BorrowFromLeft(BPlusTreePage* node, BPlusTreePage* left,
                                    InternalPage* parent, int node_index)
{
  if (node->IsLeafPage())
  {
    auto n = reinterpret_cast<LeafPage*>(node);
    auto l = reinterpret_cast<LeafPage*>(left);
    int lsz = l->GetSize();
    n->IncreaseSize(1);
    for (int i = n->GetSize() - 1; i > 0; --i)
    {
      n->SetAt(i, n->KeyAt(i - 1), n->ValueAt(i - 1));
    }
    n->SetAt(0, l->KeyAt(lsz - 1), l->ValueAt(lsz - 1));
    l->IncreaseSize(-1);
    parent->SetKeyAt(node_index, n->KeyAt(0));
  }
  else
  {
    auto n = reinterpret_cast<InternalPage*>(node);
    auto l = reinterpret_cast<InternalPage*>(left);
    int lsz = l->GetSize();
    KeyType sep = parent->KeyAt(node_index);
    n->IncreaseSize(1);
    for (int i = n->GetSize() - 1; i > 0; --i)
    {
      n->SetKeyAt(i, n->KeyAt(i - 1));
      n->SetValueAt(i, n->ValueAt(i - 1));
    }
    n->SetValueAt(0, l->ValueAt(lsz - 1));
    n->SetKeyAt(1, sep);
    parent->SetKeyAt(node_index, l->KeyAt(lsz - 1));
    l->IncreaseSize(-1);
  }
}

INDEX_TEMPLATE_ARGUMENTS
void BPLUSTREE_TYPE::BorrowFromRight(BPlusTreePage* node, BPlusTreePage* right,
                                     InternalPage* parent, int node_index)
{
  if (node->IsLeafPage())
  {
    auto n = reinterpret_cast<LeafPage*>(node);
    auto r = reinterpret_cast<LeafPage*>(right);
    n->IncreaseSize(1);
    n->SetAt(n->GetSize() - 1, r->KeyAt(0), r->ValueAt(0));
    for (int i = 0; i < r->GetSize() - 1; ++i)
    {
      r->SetAt(i, r->KeyAt(i + 1), r->ValueAt(i + 1));
    }
    r->IncreaseSize(-1);
    parent->SetKeyAt(node_index + 1, r->KeyAt(0));
  }
  else
  {
    auto n = reinterpret_cast<InternalPage*>(node);
    auto r = reinterpret_cast<InternalPage*>(right);
    KeyType sep = parent->KeyAt(node_index + 1);
    int nsz = n->GetSize();
    n->IncreaseSize(1);
    n->SetValueAt(nsz, r->ValueAt(0));
    n->SetKeyAt(nsz, sep);
    parent->SetKeyAt(node_index + 1, r->KeyAt(1));
    for (int i = 0; i < r->GetSize() - 1; ++i)
    {
      r->SetKeyAt(i, r->KeyAt(i + 1));
      r->SetValueAt(i, r->ValueAt(i + 1));
    }
    r->IncreaseSize(-1);
  }
}

INDEX_TEMPLATE_ARGUMENTS
void BPLUSTREE_TYPE::MergeNodes(BPlusTreePage* left, BPlusTreePage* right,
                                InternalPage* parent, int right_index)
{
  if (left->IsLeafPage())
  {
    auto l = reinterpret_cast<LeafPage*>(left);
    auto r = reinterpret_cast<LeafPage*>(right);
    int lsz = l->GetSize();
    int rsz = r->GetSize();
    l->IncreaseSize(rsz);
    for (int i = 0; i < rsz; ++i)
    {
      l->SetAt(lsz + i, r->KeyAt(i), r->ValueAt(i));
    }
    l->SetNextPageId(r->GetNextPageId());
  }
  else
  {
    auto l = reinterpret_cast<InternalPage*>(left);
    auto r = reinterpret_cast<InternalPage*>(right);
    KeyType sep = parent->KeyAt(right_index);
    int lsz = l->GetSize();
    int rsz = r->GetSize();
    l->IncreaseSize(rsz);
    l->SetKeyAt(lsz, sep);
    l->SetValueAt(lsz, r->ValueAt(0));
    for (int j = 1; j < rsz; ++j)
    {
      l->SetKeyAt(lsz + j, r->KeyAt(j));
      l->SetValueAt(lsz + j, r->ValueAt(j));
    }
  }
  RemoveFromInternal(parent, right_index);
}

/*****************************************************************************
 * INDEX ITERATOR
 *****************************************************************************/


INDEX_TEMPLATE_ARGUMENTS
auto BPLUSTREE_TYPE::BinaryFind(const LeafPage* leaf_page, const KeyType& key)
     ->  int
{
  int l = 0;
  int r = leaf_page -> GetSize() - 1;
  while (l < r)
  {
    int mid = (l + r + 1) >> 1;
    if (comparator_(leaf_page -> KeyAt(mid), key) != 1)
    {
      l = mid;
    }
    else
    {
      r = mid - 1;
    }
  }

  if (r >= 0 && comparator_(leaf_page -> KeyAt(r), key) == 1)
  {
    r = -1;
  }

  return r;
}

INDEX_TEMPLATE_ARGUMENTS
auto BPLUSTREE_TYPE::BinaryFind(const InternalPage* internal_page,
                                const KeyType& key)  ->  int
{
  int l = 1;
  int r = internal_page -> GetSize() - 1;
  while (l < r)
  {
    int mid = (l + r + 1) >> 1;
    if (comparator_(internal_page -> KeyAt(mid), key) != 1)
    {
      l = mid;
    }
    else
    {
      r = mid - 1;
    }
  }

  if (r == -1 || comparator_(internal_page -> KeyAt(r), key) == 1)
  {
    r = 0;
  }

  return r;
}

/*
 * Input parameter is void, find the leftmost leaf page first, then construct
 * index iterator
 * @return : index iterator
 */
INDEX_TEMPLATE_ARGUMENTS
auto BPLUSTREE_TYPE::Begin()  ->  INDEXITERATOR_TYPE
//Just go left forever
{
  ReadPageGuard head_guard = bpm_ -> FetchPageRead(header_page_id_);
  if (head_guard.template As<BPlusTreeHeaderPage>() -> root_page_id_ == INVALID_PAGE_ID)
  {
    return End();
  }
  ReadPageGuard guard = bpm_ -> FetchPageRead(head_guard.As<BPlusTreeHeaderPage>() -> root_page_id_);
  head_guard.Drop();

  auto tmp_page = guard.template As<BPlusTreePage>();
  while (!tmp_page -> IsLeafPage())
  {
    int slot_num = 0;
    guard = bpm_ -> FetchPageRead(reinterpret_cast<const InternalPage*>(tmp_page) -> ValueAt(slot_num));
    tmp_page = guard.template As<BPlusTreePage>();
  }
  int slot_num = 0;
  if (slot_num != -1)
  {
    return INDEXITERATOR_TYPE(bpm_, guard.PageId(), 0);
  }
  return End();
}


/*
 * Input parameter is low key, find the leaf page that contains the input key
 * first, then construct index iterator
 * @return : index iterator
 */
INDEX_TEMPLATE_ARGUMENTS
auto BPLUSTREE_TYPE::Begin(const KeyType& key)  ->  INDEXITERATOR_TYPE
{
  ReadPageGuard head_guard = bpm_ -> FetchPageRead(header_page_id_);

  if (head_guard.template As<BPlusTreeHeaderPage>() -> root_page_id_ == INVALID_PAGE_ID)
  {
    return End();
  }
  ReadPageGuard guard = bpm_ -> FetchPageRead(head_guard.As<BPlusTreeHeaderPage>() -> root_page_id_);
  head_guard.Drop();
  auto tmp_page = guard.template As<BPlusTreePage>();
  while (!tmp_page -> IsLeafPage())
  {
    auto internal = reinterpret_cast<const InternalPage*>(tmp_page);
    int slot_num = BinaryFind(internal, key);
    if (slot_num == -1)
    {
      return End();
    }
    guard = bpm_ -> FetchPageRead(reinterpret_cast<const InternalPage*>(tmp_page) -> ValueAt(slot_num));
    tmp_page = guard.template As<BPlusTreePage>();
  }
  auto* leaf_page = reinterpret_cast<const LeafPage*>(tmp_page);

  int slot_num = BinaryFind(leaf_page, key);
  if (slot_num != -1)
  {
    return INDEXITERATOR_TYPE(bpm_, guard.PageId(), slot_num);
  }
  return End();
}

/*
 * Input parameter is void, construct an index iterator representing the end
 * of the key/value pair in the leaf node
 * @return : index iterator
 */
INDEX_TEMPLATE_ARGUMENTS
auto BPLUSTREE_TYPE::End()  ->  INDEXITERATOR_TYPE
{
  return INDEXITERATOR_TYPE(bpm_, -1, -1);
}

/**
 * @return Page id of the root of this tree
 */
INDEX_TEMPLATE_ARGUMENTS
auto BPLUSTREE_TYPE::GetRootPageId()  ->  page_id_t
{
  ReadPageGuard guard = bpm_ -> FetchPageRead(header_page_id_);
  auto root_header_page = guard.template As<BPlusTreeHeaderPage>();
  page_id_t root_page_id = root_header_page -> root_page_id_;
  return root_page_id;
}

/*****************************************************************************
 * UTILITIES AND DEBUG
 *****************************************************************************/

/*
 * This method is used for test only
 * Read data from file and insert one by one
 */
INDEX_TEMPLATE_ARGUMENTS
void BPLUSTREE_TYPE::InsertFromFile(const std::string& file_name,
                                    Transaction* txn)
{
  int64_t key;
  std::ifstream input(file_name);
  while (input >> key)
  {
    KeyType index_key;
    index_key.SetFromInteger(key);
    RID rid(key);
    Insert(index_key, rid, txn);
  }
}
/*
 * This method is used for test only
 * Read data from file and remove one by one
 */
INDEX_TEMPLATE_ARGUMENTS
void BPLUSTREE_TYPE::RemoveFromFile(const std::string& file_name,
                                    Transaction* txn)
{
  int64_t key;
  std::ifstream input(file_name);
  while (input >> key)
  {
    KeyType index_key;
    index_key.SetFromInteger(key);
    Remove(index_key, txn);
  }
}

/*
 * This method is used for test only
 * Read data from file and insert/remove one by one
 */
INDEX_TEMPLATE_ARGUMENTS
void BPLUSTREE_TYPE::BatchOpsFromFile(const std::string& file_name,
                                      Transaction* txn)
{
  int64_t key;
  char instruction;
  std::ifstream input(file_name);
  while (input)
  {
    input >> instruction >> key;
    RID rid(key);
    KeyType index_key;
    index_key.SetFromInteger(key);
    switch (instruction)
    {
      case 'i':
        Insert(index_key, rid, txn);
        break;
      case 'd':
        Remove(index_key, txn);
        break;
      default:
        break;
    }
  }
}

INDEX_TEMPLATE_ARGUMENTS
void BPLUSTREE_TYPE::Print(BufferPoolManager* bpm)
{
  auto root_page_id = GetRootPageId();
  auto guard = bpm -> FetchPageBasic(root_page_id);
  PrintTree(guard.PageId(), guard.template As<BPlusTreePage>());
}

INDEX_TEMPLATE_ARGUMENTS
void BPLUSTREE_TYPE::PrintTree(page_id_t page_id, const BPlusTreePage* page)
{
  if (page -> IsLeafPage())
  {
    auto* leaf = reinterpret_cast<const LeafPage*>(page);
    std::cout << "Leaf Page: " << page_id << "\tNext: " << leaf -> GetNextPageId() << std::endl;

    // Print the contents of the leaf page.
    std::cout << "Contents: ";
    for (int i = 0; i < leaf -> GetSize(); i++)
    {
      std::cout << leaf -> KeyAt(i);
      if ((i + 1) < leaf -> GetSize())
      {
        std::cout << ", ";
      }
    }
    std::cout << std::endl;
    std::cout << std::endl;
  }
  else
  {
    auto* internal = reinterpret_cast<const InternalPage*>(page);
    std::cout << "Internal Page: " << page_id << std::endl;

    // Print the contents of the internal page.
    std::cout << "Contents: ";
    for (int i = 0; i < internal -> GetSize(); i++)
    {
      std::cout << internal -> KeyAt(i) << ": " << internal -> ValueAt(i);
      if ((i + 1) < internal -> GetSize())
      {
        std::cout << ", ";
      }
    }
    std::cout << std::endl;
    std::cout << std::endl;
    for (int i = 0; i < internal -> GetSize(); i++)
    {
      auto guard = bpm_ -> FetchPageBasic(internal -> ValueAt(i));
      PrintTree(guard.PageId(), guard.template As<BPlusTreePage>());
    }
  }
}

/**
 * This method is used for debug only, You don't need to modify
 */
INDEX_TEMPLATE_ARGUMENTS
void BPLUSTREE_TYPE::Draw(BufferPoolManager* bpm, const std::string& outf)
{
  if (IsEmpty())
  {
    LOG_WARN("Drawing an empty tree");
    return;
  }

  std::ofstream out(outf);
  out << "digraph G {" << std::endl;
  auto root_page_id = GetRootPageId();
  auto guard = bpm -> FetchPageBasic(root_page_id);
  ToGraph(guard.PageId(), guard.template As<BPlusTreePage>(), out);
  out << "}" << std::endl;
  out.close();
}

/**
 * This method is used for debug only, You don't need to modify
 */
INDEX_TEMPLATE_ARGUMENTS
void BPLUSTREE_TYPE::ToGraph(page_id_t page_id, const BPlusTreePage* page,
                             std::ofstream& out)
{
  std::string leaf_prefix("LEAF_");
  std::string internal_prefix("INT_");
  if (page -> IsLeafPage())
  {
    auto* leaf = reinterpret_cast<const LeafPage*>(page);
    // Print node name
    out << leaf_prefix << page_id;
    // Print node properties
    out << "[shape=plain color=green ";
    // Print data of the node
    out << "label=<<TABLE BORDER=\"0\" CELLBORDER=\"1\" CELLSPACING=\"0\" "
           "CELLPADDING=\"4\">\n";
    // Print data
    out << "<TR><TD COLSPAN=\"" << leaf -> GetSize() << "\">P=" << page_id
        << "</TD></TR>\n";
    out << "<TR><TD COLSPAN=\"" << leaf -> GetSize() << "\">"
        << "max_size=" << leaf -> GetMaxSize()
        << ",min_size=" << leaf -> GetMinSize() << ",size=" << leaf -> GetSize()
        << "</TD></TR>\n";
    out << "<TR>";
    for (int i = 0; i < leaf -> GetSize(); i++)
    {
      out << "<TD>" << leaf -> KeyAt(i) << "</TD>\n";
    }
    out << "</TR>";
    // Print table end
    out << "</TABLE>>];\n";
    // Print Leaf node link if there is a next page
    if (leaf -> GetNextPageId() != INVALID_PAGE_ID)
    {
      out << leaf_prefix << page_id << "   ->   " << leaf_prefix
          << leaf -> GetNextPageId() << ";\n";
      out << "{rank=same " << leaf_prefix << page_id << " " << leaf_prefix
          << leaf -> GetNextPageId() << "};\n";
    }
  }
  else
  {
    auto* inner = reinterpret_cast<const InternalPage*>(page);
    // Print node name
    out << internal_prefix << page_id;
    // Print node properties
    out << "[shape=plain color=pink ";  // why not?
    // Print data of the node
    out << "label=<<TABLE BORDER=\"0\" CELLBORDER=\"1\" CELLSPACING=\"0\" "
           "CELLPADDING=\"4\">\n";
    // Print data
    out << "<TR><TD COLSPAN=\"" << inner -> GetSize() << "\">P=" << page_id
        << "</TD></TR>\n";
    out << "<TR><TD COLSPAN=\"" << inner -> GetSize() << "\">"
        << "max_size=" << inner -> GetMaxSize()
        << ",min_size=" << inner -> GetMinSize() << ",size=" << inner -> GetSize()
        << "</TD></TR>\n";
    out << "<TR>";
    for (int i = 0; i < inner -> GetSize(); i++)
    {
      out << "<TD PORT=\"p" << inner -> ValueAt(i) << "\">";
      // if (i > 0) {
      out << inner -> KeyAt(i) << "  " << inner -> ValueAt(i);
      // } else {
      // out << inner  ->  ValueAt(0);
      // }
      out << "</TD>\n";
    }
    out << "</TR>";
    // Print table end
    out << "</TABLE>>];\n";
    // Print leaves
    for (int i = 0; i < inner -> GetSize(); i++)
    {
      auto child_guard = bpm_ -> FetchPageBasic(inner -> ValueAt(i));
      auto child_page = child_guard.template As<BPlusTreePage>();
      ToGraph(child_guard.PageId(), child_page, out);
      if (i > 0)
      {
        auto sibling_guard = bpm_ -> FetchPageBasic(inner -> ValueAt(i - 1));
        auto sibling_page = sibling_guard.template As<BPlusTreePage>();
        if (!sibling_page -> IsLeafPage() && !child_page -> IsLeafPage())
        {
          out << "{rank=same " << internal_prefix << sibling_guard.PageId()
              << " " << internal_prefix << child_guard.PageId() << "};\n";
        }
      }
      out << internal_prefix << page_id << ":p" << child_guard.PageId()
          << "   ->   ";
      if (child_page -> IsLeafPage())
      {
        out << leaf_prefix << child_guard.PageId() << ";\n";
      }
      else
      {
        out << internal_prefix << child_guard.PageId() << ";\n";
      }
    }
  }
}

INDEX_TEMPLATE_ARGUMENTS
auto BPLUSTREE_TYPE::DrawBPlusTree()  ->  std::string
{
  if (IsEmpty())
  {
    return "()";
  }

  PrintableBPlusTree p_root = ToPrintableBPlusTree(GetRootPageId());
  std::ostringstream out_buf;
  p_root.Print(out_buf);

  return out_buf.str();
}

INDEX_TEMPLATE_ARGUMENTS
auto BPLUSTREE_TYPE::ToPrintableBPlusTree(page_id_t root_id)
     ->  PrintableBPlusTree
{
  auto root_page_guard = bpm_ -> FetchPageBasic(root_id);
  auto root_page = root_page_guard.template As<BPlusTreePage>();
  PrintableBPlusTree proot;

  if (root_page -> IsLeafPage())
  {
    auto leaf_page = root_page_guard.template As<LeafPage>();
    proot.keys_ = leaf_page -> ToString();
    proot.size_ = proot.keys_.size() + 4;  // 4 more spaces for indent

    return proot;
  }

  // draw internal page
  auto internal_page = root_page_guard.template As<InternalPage>();
  proot.keys_ = internal_page -> ToString();
  proot.size_ = 0;
  for (int i = 0; i < internal_page -> GetSize(); i++)
  {
    page_id_t child_id = internal_page -> ValueAt(i);
    PrintableBPlusTree child_node = ToPrintableBPlusTree(child_id);
    proot.size_ += child_node.size_;
    proot.children_.push_back(child_node);
  }

  return proot;
}

template class BPlusTree<GenericKey<4>, RID, GenericComparator<4>>;

template class BPlusTree<GenericKey<8>, RID, GenericComparator<8>>;

template class BPlusTree<GenericKey<16>, RID, GenericComparator<16>>;

template class BPlusTree<GenericKey<32>, RID, GenericComparator<32>>;

template class BPlusTree<GenericKey<64>, RID, GenericComparator<64>>;

}  // namespace bustub