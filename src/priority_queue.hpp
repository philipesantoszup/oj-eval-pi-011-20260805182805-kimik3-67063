#ifndef SJTU_PRIORITY_QUEUE_HPP
#define SJTU_PRIORITY_QUEUE_HPP

#include <cstddef>
#include <functional>
#include "exceptions.hpp"

namespace sjtu {
/**
 * @brief a container like std::priority_queue which is a heap internal.
 *
 * Implemented with a pairing heap (child / sibling representation):
 *   - push  : O(1)      (a single link after one comparison)
 *   - merge : O(1)      (a single link after one comparison, <= O(log n))
 *   - pop   : O(log n)  amortized (two-pass pairing meld of the children)
 *
 * **Exception Safety**: The `Compare` operation might throw exceptions for
 * certain data. In such cases, any ongoing operation is terminated, and the
 * priority queue is restored to its original state before the operation
 * began. This is achieved by always performing the (possibly throwing)
 * comparison *before* any pointer is modified, so a throwing comparison
 * leaves every involved tree untouched. For `pop`, the two-pass meld keeps
 * track of every subtree so that, upon an exception, all of them can be
 * re-attached under the old root (which is known to be the maximum, so the
 * heap order is preserved) without performing any further comparison.
 */
template<typename T, class Compare = std::less<T>>
class priority_queue {
private:
	struct Node {
		T data;
		Node *child;   // first child
		Node *sibling; // next sibling (also used to link meld pools)
		Node(const T &value) : data(value), child(nullptr), sibling(nullptr) {}
	};

	Node *root_;
	size_t size_;
	Compare comp_;

	/**
	 * @brief merge two heap-ordered trees and return the winner root.
	 * The comparison is performed before any linking, so if Compare throws
	 * both trees are left completely untouched (transactional behaviour).
	 * The `sibling` fields of `a` and `b` are owned by the caller and are
	 * expected to be nullptr (they are never read here).
	 */
	Node *mergeTree(Node *a, Node *b) {
		if (a == nullptr) return b;
		if (b == nullptr) return a;
		if (comp_(a->data, b->data)) { // a < b : b should be on top
			Node *t = a; a = b; b = t;
		}
		// no comparison below this point -> cannot throw
		b->sibling = a->child;
		a->child = b;
		return a;
	}

	/**
	 * @brief meld a sibling-linked list of subtrees (two-pass pairing).
	 * `pool` is consumed during the process. If Compare throws at any
	 * point, every subtree that belonged to the pool is put back into
	 * `pool` (each of them still a valid heap-ordered tree) and the
	 * exception is rethrown, so the caller can restore the previous state.
	 */
	Node *meldChildren(Node *&pool) {
		Node *pairs = nullptr;
		// pass 1: pair up neighbouring trees from left to right
		while (pool != nullptr) {
			Node *a = pool;
			pool = a->sibling;
			Node *b = nullptr;
			if (pool != nullptr) {
				b = pool;
				pool = b->sibling;
			}
			a->sibling = nullptr;
			if (b != nullptr) b->sibling = nullptr;
			Node *m;
			try {
				m = mergeTree(a, b);
			} catch (...) {
				// a and b were not modified; put everything back
				a->sibling = pool;
				pool = a;
				if (b != nullptr) {
					b->sibling = pool;
					pool = b;
				}
				while (pairs != nullptr) {
					Node *t = pairs;
					pairs = t->sibling;
					t->sibling = pool;
					pool = t;
				}
				throw;
			}
			m->sibling = pairs;
			pairs = m;
		}
		// pass 2: meld the pairs from right to left
		Node *result = nullptr; // invariant: result->sibling == nullptr
		while (pairs != nullptr) {
			Node *t = pairs;
			pairs = t->sibling;
			t->sibling = nullptr;
			try {
				result = mergeTree(t, result);
			} catch (...) {
				t->sibling = pool;
				pool = t;
				if (result != nullptr) {
					result->sibling = pool;
					pool = result;
				}
				while (pairs != nullptr) {
					Node *u = pairs;
					pairs = u->sibling;
					u->sibling = pool;
					pool = u;
				}
				throw;
			}
		}
		return result;
	}

	/** @brief iteratively destroy a whole tree (no recursion, O(n)). */
	static void destroyTree(Node *r) {
		Node *st = r; // stack linked through `sibling`
		while (st != nullptr) {
			Node *n = st;
			st = n->sibling;
			Node *c = n->child;
			while (c != nullptr) {
				Node *nx = c->sibling;
				c->sibling = st;
				st = c;
				c = nx;
			}
			delete n;
		}
	}

	/** @brief iteratively deep-copy a whole tree (no recursion, O(n)). */
	static Node *copyTree(const Node *srcRoot) {
		if (srcRoot == nullptr) return nullptr;
		struct Task {
			const Node *src; // head of the source sibling list to copy
			Node *parent;    // destination parent whose child list is filled
			Task *next;
		};
		Node *dstRoot = nullptr;
		Task *stack = nullptr;
		try {
			dstRoot = new Node(srcRoot->data);
			if (srcRoot->child != nullptr) {
				Task *t = new Task;
				t->src = srcRoot->child;
				t->parent = dstRoot;
				t->next = nullptr;
				stack = t;
			}
			while (stack != nullptr) {
				Task *t = stack;
				stack = stack->next;
				Node **tail = &(t->parent->child);
				for (const Node *s = t->src; s != nullptr; s = s->sibling) {
					Node *c = new Node(s->data);
					*tail = c;
					tail = &(c->sibling);
					if (s->child != nullptr) {
						Task *nt = new Task;
						nt->src = s->child;
						nt->parent = c;
						nt->next = stack;
						stack = nt;
					}
				}
				delete t;
			}
		} catch (...) {
			while (stack != nullptr) {
				Task *t = stack;
				stack = stack->next;
				delete t;
			}
			destroyTree(dstRoot);
			throw;
		}
		return dstRoot;
	}

public:
	/**
	 * @brief default constructor
	 */
	priority_queue() : root_(nullptr), size_(0), comp_() {}

	/**
	 * @brief copy constructor
	 * @param other the priority_queue to be copied
	 */
	priority_queue(const priority_queue &other)
		: root_(copyTree(other.root_)), size_(other.size_), comp_(other.comp_) {}

	/**
	 * @brief deconstructor
	 */
	~priority_queue() {
		destroyTree(root_);
	}

	/**
	 * @brief Assignment operator
	 * @param other the priority_queue to be assigned from
	 * @return a reference to this priority_queue after assignment
	 */
	priority_queue &operator=(const priority_queue &other) {
		if (this == &other) return *this;
		Node *newRoot = copyTree(other.root_); // may throw; *this unchanged
		destroyTree(root_);
		root_ = newRoot;
		size_ = other.size_;
		comp_ = other.comp_;
		return *this;
	}

	/**
	 * @brief get the top element of the priority queue.
	 * @return a reference of the top element.
	 * @throws container_is_empty if empty() returns true
	 */
	const T & top() const {
		if (root_ == nullptr) throw container_is_empty();
		return root_->data;
	}

	/**
	 * @brief push new element to the priority queue.
	 * If Compare throws, the queue is left unchanged and a
	 * runtime_error is thrown.
	 * @param e the element to be pushed
	 */
	void push(const T &e) {
		Node *n = new Node(e);
		try {
			root_ = mergeTree(root_, n);
		} catch (...) {
			delete n; // the old heap was not touched
			throw runtime_error();
		}
		++size_;
	}

	/**
	 * @brief delete the top element from the priority queue.
	 * If Compare throws during the meld, the heap is restored to its
	 * previous state and a runtime_error is thrown.
	 * @throws container_is_empty if empty() returns true
	 */
	void pop() {
		if (root_ == nullptr) throw container_is_empty();
		Node *oldRoot = root_;
		Node *pool = oldRoot->child;
		oldRoot->child = nullptr;
		try {
			root_ = meldChildren(pool);
		} catch (...) {
			// `pool` holds every former subtree again; since oldRoot is
			// the maximum of the whole heap, re-attaching them directly
			// under oldRoot keeps the heap order (no comparison needed).
			oldRoot->child = pool;
			root_ = oldRoot;
			throw runtime_error();
		}
		--size_;
		delete oldRoot;
	}

	/**
	 * @brief return the number of elements in the priority queue.
	 * @return the number of elements.
	 */
	size_t size() const {
		return size_;
	}

	/**
	 * @brief check if the container is empty.
	 * @return true if it is empty, false otherwise.
	 */
	bool empty() const {
		return size_ == 0;
	}

	/**
	 * @brief merge another priority_queue into this one.
	 * The other priority_queue will be cleared after merging.
	 * The complexity is O(1) (a single comparison and one link), which is
	 * within the required O(log n) bound.
	 * If Compare throws, both queues are left unchanged and a
	 * runtime_error is thrown.
	 * @param other the priority_queue to be merged.
	 */
	void merge(priority_queue &other) {
		if (this == &other) return;
		Node *newRoot;
		try {
			newRoot = mergeTree(root_, other.root_);
		} catch (...) {
			// comparison happens before linking: both heaps untouched
			throw runtime_error();
		}
		root_ = newRoot;
		size_ += other.size_;
		other.root_ = nullptr;
		other.size_ = 0;
	}
};

}

#endif
