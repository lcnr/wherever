use core::iter::FusedIterator;
use core::marker::PhantomData;
use core::mem;
use core::ptr::NonNull;

/// A node of a `LinkedList`.
#[derive(Debug, Clone)]
pub struct Node<T: ?Sized> {
    prev: Option<NonNull<Node<T>>>,
    next: Option<NonNull<Node<T>>>,
    value: T,
}

impl<T: Eq + ?Sized> Eq for Node<T> {}

impl<T: PartialEq + ?Sized> PartialEq for Node<T> {
    fn eq(&self, other: &Self) -> bool {
        self.value == other.value
    }
}

impl<T> Node<T> {
    /// Creates a new node on the stack.
    ///
    /// # Examples
    ///
    /// ```
    /// use wherever::Node;
    /// 
    /// let node = Node::new(3);
    /// assert_eq!(node.into_inner(), 3);
    /// ```
    pub const fn new(value: T) -> Self {
        Node {
            prev: None,
            next: None,
            value,
        }
    }

    /// Consumes `self` and returns the contained value.
    pub fn into_inner(self) -> T {
        self.value
    }
}

impl<T: ?Sized> Node<T> {
    /// Returns a reference to the contained value.
    pub fn value(&self) -> &T {
        &self.value
    }

    /// Returns a mutable reference to the contained value.
    pub fn value_mut(&mut self) -> &mut T {
        &mut self.value
    }
}

/// An intrusive linked list holding elements for at most the duration `'a`.
///
/// `Node`s which were added to a list cannot be used until the list is dropped, even if
/// the element was removed from the list.
///
/// # Examples
///
/// ```
/// use wherever::{LinkedList, Node};
///
/// let mut list = LinkedList::new();
///
/// let element = 14;
/// let mut node = Node::new(element);
/// list.push_front(&mut node);
/// assert_eq!(list.len(), 1);
/// assert_eq!(list.back(), Some(&14));
/// ```
///
/// Trying to reuse an element while the list is still alive results in an error at compile time.
///
/// ```compile_fail
/// use wherever::{LinkedList, Node};
///
/// let mut list = LinkedList::new();
///
/// let mut a = Node::new(7);
/// list.push_front(&mut a);
/// list.pop_front();
///
/// // `a` is still borrowed as `push_front` requires a reference which lives
/// // for at least as long as the `LinkedList` is still alive.
/// assert_eq!(a.into_inner(), 7);
///
/// list.clear();
/// ```
pub struct LinkedList<'a, T: ?Sized> {
    head: Option<NonNull<Node<T>>>,
    tail: Option<NonNull<Node<T>>>,
    len: usize,
    _marker: PhantomData<&'a T>,
}

impl<'a, T: ?Sized> Default for LinkedList<'a, T> {
    fn default() -> Self {
        LinkedList {
            head: None,
            tail: None,
            len: 0,
            _marker: PhantomData,
        }
    }
}

impl<'a, T: ?Sized> LinkedList<'a, T> {
    /// Split the list after the given node.
    ///
    /// # Safety
    ///
    /// - `split_node` must be an element of `self`
    /// - `at` must be to index of `split_node` in `self`
    unsafe fn split_off_after_node(
        &mut self,
        split_node: Option<NonNull<Node<T>>>,
        at: usize,
    ) -> Self {
        // The split node is the new tail node of the first part and owns
        // the head of the second part.
        if let Some(mut split_node) = split_node {
            let second_part_head;
            let second_part_tail;
            second_part_head = split_node.as_mut().next.take();
            if let Some(mut head) = second_part_head {
                head.as_mut().prev = None;
                second_part_tail = self.tail;
            } else {
                second_part_tail = None;
            }

            let second_part = LinkedList {
                head: second_part_head,
                tail: second_part_tail,
                len: self.len - at,
                _marker: PhantomData,
            };

            // Fix the tail ptr of the first part
            self.tail = Some(split_node);
            self.len = at;

            second_part
        } else {
            mem::replace(self, LinkedList::new())
        }
    }
}

impl<'a, T: ?Sized> LinkedList<'a, T> {
    /// Creates an empty `LinkedList`.
    ///
    /// # Examples
    ///
    /// ```
    /// use wherever::LinkedList;
    ///
    /// let list: LinkedList<u32> = LinkedList::new();
    /// ```
    pub fn new() -> Self {
        LinkedList::default()
    }

    /// Returns the length of the `LinkedList`.
    ///
    /// This operation should compute in O(1) time.
    ///
    /// # Examples
    ///
    /// ```
    /// use wherever::{LinkedList, Node};
    ///
    /// let mut dl = LinkedList::new();
    ///
    /// let mut two = Node::new(2);
    /// dl.push_front(&mut two);
    /// assert_eq!(dl.len(), 1);
    ///
    /// let mut one = Node::new(1);
    /// dl.push_front(&mut one);
    /// assert_eq!(dl.len(), 2);
    ///
    /// let mut three = Node::new(3);
    /// dl.push_back(&mut three);
    /// assert_eq!(dl.len(), 3);
    /// ```
    pub fn len(&self) -> usize {
        self.len
    }

    /// Returns `true` if the `LinkedList` is empty.
    ///
    /// This operation should compute in O(1) time.
    ///
    /// # Examples
    ///
    /// ```
    /// use wherever::{LinkedList, Node};
    ///
    /// let mut dl = LinkedList::new();
    /// assert!(dl.is_empty());
    ///
    /// let mut node = Node::new("foo");
    /// dl.push_front(&mut node);
    /// assert!(!dl.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        self.head.is_none()
    }

    /// Removes all elements from the `LinkedList`.
    ///
    /// This operation should compute in `O(1)` time, as no element will actually be dropped.
    ///
    /// # Examples
    ///
    /// ```
    /// use wherever::{LinkedList, Node};
    ///
    /// let mut dl = LinkedList::new();
    ///
    /// let mut a = Node::new(2);
    /// let mut b = Node::new(1);
    /// dl.push_front(&mut a);
    /// dl.push_front(&mut b);
    /// assert_eq!(dl.len(), 2);
    /// assert_eq!(dl.front(), Some(&1));
    ///
    /// dl.clear();
    /// assert_eq!(dl.len(), 0);
    /// assert_eq!(dl.front(), None);
    /// ```
    pub fn clear(&mut self) {
        self.len = 0;
        self.head = None;
        self.tail = None;
    }

    /// Provides a reference to the front element, or `None` if the list is empty.
    ///
    /// # Examples
    ///
    /// ```
    /// use wherever::{LinkedList, Node};
    ///
    /// let mut dl = LinkedList::new();
    /// assert_eq!(dl.front(), None);
    ///
    /// let mut node = Node::new(1);
    /// dl.push_front(&mut node);
    /// assert_eq!(dl.front(), Some(&1));
    /// ```
    pub fn front(&self) -> Option<&T> {
        // SAFETY: `self.head` cannot be mutated while `self` is immutably borrowed
        self.head.map(|v| unsafe { (&*v.as_ptr()).value() })
    }

    /// Provides a mutable reference to the front element, or `None` if the list
    /// is empty.
    ///
    /// # Examples
    ///
    /// ```
    /// use wherever::{LinkedList, Node};
    ///
    /// let mut dl = LinkedList::new();
    /// assert_eq!(dl.front(), None);
    ///
    /// let mut node = Node::new(1);
    /// dl.push_front(&mut node);
    /// assert_eq!(dl.front(), Some(&1));
    ///
    /// match dl.front_mut() {
    ///     None => {}
    ///     Some(x) => *x = 5,
    /// }
    /// assert_eq!(dl.front(), Some(&5));
    /// ```
    pub fn front_mut(&mut self) -> Option<&mut T> {
        // SAFETY: `self.head` cannot be aliased while `self` ismutably borrowed
        self.head.map(|v| unsafe { (&mut *v.as_ptr()).value_mut() })
    }

    /// Provides a reference to the back element, or `None` if the list is empty.
    ///
    /// # Examples
    ///
    /// ```
    /// use wherever::{LinkedList, Node};
    ///
    /// let mut dl = LinkedList::new();
    /// assert_eq!(dl.back(), None);
    ///
    /// let mut node = Node::new(1);
    /// dl.push_back(&mut node);
    /// assert_eq!(dl.back(), Some(&1));
    /// ```
    pub fn back(&self) -> Option<&T> {
        // SAFETY: `self.tail` cannot be mutated while `self` is immutably borrowed
        self.tail.map(|v| unsafe { (&*v.as_ptr()).value() })
    }

    /// Provides a mutable reference to the back element, or `None` if the list
    /// is empty.
    ///
    /// # Examples
    ///
    /// ```
    /// use wherever::{LinkedList, Node};
    ///
    /// let mut dl = LinkedList::new();
    /// assert_eq!(dl.back(), None);
    ///
    /// let mut node = Node::new(1);
    /// dl.push_back(&mut node);
    /// assert_eq!(dl.back(), Some(&1));
    ///
    /// match dl.back_mut() {
    ///     None => {}
    ///     Some(x) => *x = 5,
    /// }
    /// assert_eq!(dl.back(), Some(&5));
    /// ```
    pub fn back_mut(&mut self) -> Option<&mut T> {
        // SAFETY: `self.tail` cannot be aliased while `self` ismutably borrowed
        self.tail.map(|v| unsafe { (&mut *v.as_ptr()).value_mut() })
    }

    /// Returns `true` if the `LinkedList` contains an element equal to the
    /// given value.
    ///
    /// # Examples
    ///
    /// ```
    /// use wherever::{LinkedList, Node};
    ///
    /// let mut list: LinkedList<u32> = LinkedList::new();
    ///
    /// let mut zero = Node::new(0);
    /// let mut one = Node::new(1);
    /// let mut two = Node::new(2);
    /// list.push_back(&mut zero);
    /// list.push_back(&mut one);
    /// list.push_back(&mut two);
    ///
    /// assert_eq!(list.contains(&0), true);
    /// assert_eq!(list.contains(&10), false);
    /// ```
    pub fn contains(&self, x: &T) -> bool
    where
        T: PartialEq<T>,
    {
        self.iter().any(|e| e == x)
    }

    /// Provides a forward iterator.
    ///
    /// # Examples
    ///
    /// ```
    /// use wherever::{LinkedList, Node};
    ///
    /// let mut list: LinkedList<u32> = LinkedList::new();
    ///
    /// let mut zero = Node::new(0);
    /// let mut one = Node::new(1);
    /// let mut two = Node::new(2);
    /// list.push_back(&mut zero);
    /// list.push_back(&mut one);
    /// list.push_back(&mut two);
    ///
    /// let mut iter = list.iter();
    /// assert_eq!(iter.next(), Some(&0));
    /// assert_eq!(iter.next(), Some(&1));
    /// assert_eq!(iter.next(), Some(&2));
    /// assert_eq!(iter.next(), None);
    /// ```
    pub fn iter<'b>(&'b self) -> Iter<'b, T> {
        Iter {
            head: self.head,
            tail: self.tail,
            len: self.len,
            _marker: PhantomData,
        }
    }

    /// Provides a forward iterator with mutable references.
    ///
    /// # Examples
    ///
    /// ```
    /// use wherever::{LinkedList, Node};
    ///
    /// let mut list: LinkedList<u32> = LinkedList::new();
    ///
    /// let mut zero = Node::new(0);
    /// let mut one = Node::new(1);
    /// let mut two = Node::new(2);
    /// list.push_back(&mut zero);
    /// list.push_back(&mut one);
    /// list.push_back(&mut two);
    ///
    /// for element in list.iter_mut() {
    ///     *element += 10;
    /// }
    ///
    /// let mut iter = list.iter();
    /// assert_eq!(iter.next(), Some(&10));
    /// assert_eq!(iter.next(), Some(&11));
    /// assert_eq!(iter.next(), Some(&12));
    /// assert_eq!(iter.next(), None);
    /// ```
    pub fn iter_mut<'b>(&mut self) -> IterMut<'b, T> {
        IterMut {
            head: self.head,
            tail: self.tail,
            len: self.len,
            _marker: PhantomData,
        }
    }

    /// Moves all elements from other to the end of the list.
    ///
    /// This reuses all the nodes from other and moves them into self. After this operation, other becomes empty.
    ///
    /// This operation should compute in O(1) time and O(1) memory.
    pub fn append(&mut self, other: &mut LinkedList<'a, T>) {
        match self.tail {
            None => mem::swap(self, other),
            Some(mut tail) => {
                if let Some(mut other_head) = other.head.take() {
                    unsafe {
                        tail.as_mut().next = Some(other_head);
                        other_head.as_mut().prev = Some(tail);
                    }

                    self.tail = other.tail.take();
                    self.len += mem::replace(&mut other.len, 0);
                }
            }
        }
    }

    /// Adds a node to the back of the list, the node is mutable borrowed
    /// until the list is dropped.
    ///
    /// This operation should compute in O(1) time.
    ///
    /// # Examples
    ///
    /// ```
    /// use wherever::{LinkedList, Node};
    ///
    /// let mut list = LinkedList::new();
    ///
    /// let mut a = Node::new(42);
    /// list.push_back(&mut a);
    ///
    /// assert_eq!(list.back(), Some(&42));
    /// ```
    pub fn push_back(&mut self, node: &'a mut Node<T>) {
        unsafe {
            node.next = None;
            node.prev = self.tail;

            let node_ptr = Some(NonNull::from(node));

            match self.tail {
                None => self.head = node_ptr,
                Some(tail) => (*tail.as_ptr()).next = node_ptr,
            }

            self.tail = node_ptr;
            self.len += 1;
        }
    }

    /// Removes the last element from a list and returns it, or None if it is empty.
    ///
    /// This operation should compute in O(1) time.
    ///
    /// # Examples
    ///
    /// ```
    /// use wherever::{LinkedList, Node};
    ///
    /// let mut d = LinkedList::new();
    /// assert_eq!(d.pop_back(), None);
    ///
    /// let mut one = Node::new(1);
    /// let mut three = Node::new(3);
    /// d.push_back(&mut one);
    /// d.push_back(&mut three);
    /// assert_eq!(d.pop_back().map(|n| n.value()), Some(&3));
    /// assert_eq!(d.pop_back().map(|n| n.value()), Some(&1));
    /// assert_eq!(d.pop_back(), None);
    /// ```
    pub fn pop_back(&mut self) -> Option<&'a mut Node<T>> {
        self.tail.map(|node| unsafe {
            let node = &mut *node.as_ptr();
            self.tail = node.prev;

            match self.tail {
                None => self.head = None,
                Some(tail) => (*tail.as_ptr()).next = None,
            }

            self.len -= 1;
            node
        })
    }

    /// Adds an element to the front of the list.
    ///
    /// This operation should compute in O(1) time.
    ///
    /// # Examples
    ///
    /// ```
    /// use wherever::{LinkedList, Node};
    ///
    /// let mut list = LinkedList::new();
    ///
    /// let mut a = Node::new(7);
    /// list.push_front(&mut a);
    /// assert_eq!(list.front(), Some(&7));
    ///
    /// let mut b = Node::new(10);
    /// list.push_front(&mut b);
    /// assert_eq!(list.front(), Some(&10));
    /// assert_eq!(list.back(), Some(&7));
    /// ```
    pub fn push_front(&mut self, node: &'a mut Node<T>) {
        unsafe {
            node.next = self.head;
            node.prev = None;

            let node_ptr = Some(NonNull::from(node));

            match self.head {
                None => self.tail = node_ptr,
                Some(head) => (*head.as_ptr()).prev = node_ptr,
            }

            self.head = node_ptr;
            self.len += 1;
        }
    }

    /// Removes the first element from a list and returns it, or `None` if it is empty.
    ///
    /// This operation should compute in O(1) time.
    ///
    /// # Examples
    ///
    /// ```
    /// use wherever::{LinkedList, Node};
    ///
    /// let mut d = LinkedList::new();
    /// assert_eq!(d.pop_front(), None);
    ///
    /// let mut one = Node::new(1);
    /// let mut three = Node::new(3);
    /// d.push_front(&mut one);
    /// d.push_front(&mut three);
    /// assert_eq!(d.pop_front().map(|n| n.value()), Some(&3));
    /// assert_eq!(d.pop_front().map(|n| n.value()), Some(&1));
    /// assert_eq!(d.pop_front(), None);
    /// ```
    pub fn pop_front(&mut self) -> Option<&'a mut Node<T>> {
        self.head.map(|node| unsafe {
            let node = &mut *node.as_ptr();
            self.head = node.next;

            match self.head {
                None => self.tail = None,
                // Not creating new mutable (unique!) references overlapping `element`.
                Some(head) => (*head.as_ptr()).prev = None,
            }

            self.len -= 1;
            node
        })
    }

    /// Splits the list into two at the given index. Returns everything after the given index,
    /// including the index.
    ///
    /// This operation should compute in O(n) time.
    ///
    /// # Panics
    ///
    /// Panics if `at > len`.
    ///
    /// # Examples
    ///
    /// ```
    /// use wherever::{LinkedList, Node};
    ///
    /// let mut d = LinkedList::new();
    ///
    /// let mut zero = Node::new(0);
    /// let mut one = Node::new(1);
    /// let mut two = Node::new(2);
    /// d.push_back(&mut zero);
    /// d.push_back(&mut one);
    /// d.push_back(&mut two);
    ///
    /// let mut split = d.split_off(2);
    ///
    /// assert_eq!(d.pop_back().map(|n| n.value()), Some(&1));
    /// assert_eq!(d.pop_back().map(|n| n.value()), Some(&0));
    /// //assert_eq!(d.pop_back(), None);
    ///
    /// assert_eq!(split.pop_back().map(|n| n.value()), Some(&2));
    /// assert_eq!(split.pop_back(), None);
    /// ```
    pub fn split_off(&mut self, at: usize) -> LinkedList<'a, T> {
        let len = self.len();
        assert!(at <= len, "Cannot split off at a nonexistent index");
        if at == 0 {
            return mem::take(self);
        } else if at == len {
            return Self::new();
        }

        // Below, we iterate towards the `i-1`th node, either from the start or the end,
        // depending on which would be faster.
        let split_node = if at - 1 <= len - 1 - (at - 1) {
            let mut iter = self.iter_mut();
            // instead of skipping using .skip() (which creates a new struct),
            // we skip manually so we can access the head field without
            // depending on implementation details of Skip
            for _ in 0..at - 1 {
                iter.next();
            }
            iter.head
        } else {
            // better off starting from the end
            let mut iter = self.iter_mut();
            for _ in 0..len - 1 - (at - 1) {
                iter.next_back();
            }
            iter.tail
        };
        unsafe { self.split_off_after_node(split_node, at) }
    }
}

/// An iterator over the elements of a `LinkedList`.
///
/// This `struct` is created by the `iter` method on `LinkedList`. See its
/// documentation for more.
#[derive(Debug)]
pub struct Iter<'a, T: 'a + ?Sized> {
    head: Option<NonNull<Node<T>>>,
    tail: Option<NonNull<Node<T>>>,
    len: usize,
    _marker: PhantomData<&'a Node<T>>,
}

impl<T: ?Sized> Clone for Iter<'_, T> {
    fn clone(&self) -> Self {
        Iter { ..*self }
    }
}

impl<'a, T: ?Sized> Iterator for Iter<'a, T> {
    type Item = &'a T;

    #[inline]
    fn next(&mut self) -> Option<&'a T> {
        if self.len == 0 {
            None
        } else {
            self.head.map(|node| unsafe {
                // Need an unbound lifetime to get 'a
                let node = &*node.as_ptr();
                self.len -= 1;
                self.head = node.next;
                node.value()
            })
        }
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.len, Some(self.len))
    }

    #[inline]
    fn last(mut self) -> Option<&'a T> {
        self.next_back()
    }
}

impl<'a, T: ?Sized> DoubleEndedIterator for Iter<'a, T> {
    #[inline]
    fn next_back(&mut self) -> Option<&'a T> {
        if self.len == 0 {
            None
        } else {
            self.tail.map(|node| unsafe {
                // Need an unbound lifetime to get 'a
                let node = &*node.as_ptr();
                self.len -= 1;
                self.tail = node.prev;
                node.value()
            })
        }
    }
}

impl<T: ?Sized> ExactSizeIterator for Iter<'_, T> {}

impl<T: ?Sized> FusedIterator for Iter<'_, T> {}

/// A mutable iterator over the elements of a `LinkedList`.
///
/// This `struct` is created by the `iter_mut` method on `LinkedList`. See its
/// documentation for more.
pub struct IterMut<'a, T: 'a + ?Sized> {
    head: Option<NonNull<Node<T>>>,
    tail: Option<NonNull<Node<T>>>,
    len: usize,
    _marker: PhantomData<&'a Node<T>>,
}

impl<'a, T: ?Sized> Iterator for IterMut<'a, T> {
    type Item = &'a mut T;

    #[inline]
    fn next(&mut self) -> Option<&'a mut T> {
        if self.len == 0 {
            None
        } else {
            self.head.map(|node| unsafe {
                // Need an unbound lifetime to get 'a
                let node = &mut *node.as_ptr();
                self.len -= 1;
                self.head = node.next;
                node.value_mut()
            })
        }
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.len, Some(self.len))
    }

    #[inline]
    fn last(mut self) -> Option<&'a mut T> {
        self.next_back()
    }
}

impl<'a, T: ?Sized> DoubleEndedIterator for IterMut<'a, T> {
    #[inline]
    fn next_back(&mut self) -> Option<&'a mut T> {
        if self.len == 0 {
            None
        } else {
            self.tail.map(|node| unsafe {
                // Need an unbound lifetime to get 'a
                let node = &mut *node.as_ptr();
                self.len -= 1;
                self.tail = node.prev;
                node.value_mut()
            })
        }
    }
}

impl<T: ?Sized> ExactSizeIterator for IterMut<'_, T> {}

impl<T: ?Sized> FusedIterator for IterMut<'_, T> {}
