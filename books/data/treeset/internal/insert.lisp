; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "TREESET")

(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)
(include-book "xdoc/constructors" :dir :system)

(include-book "data/utilities/fixed-size-words/u32-defs" :dir :system)
(include-book "data/utilities/total-order-defs" :dir :system)

(include-book "../hash-defs")
(include-book "tree-defs")
(include-book "rotate-defs")
(include-book "count-defs")
(include-book "in-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(local (include-book "kestrel/utilities/ordinals" :dir :system))

(local (include-book "data/utilities/fixed-size-words/u32" :dir :system))
(local (include-book "data/utilities/total-order" :dir :system))

(local (include-book "../hash"))
(local (include-book "tree"))
(local (include-book "bst"))
(local (include-book "heap"))
(local (include-book "heap-order"))
(local (include-book "count"))
(local (include-book "rotate"))
(local (include-book "in"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tree-insert
  (x
   (hash (unsigned-byte-p 32 hash))
   (tree treep))
  :parents (implementation)
  :short "Insert a value into the tree."
  :long
  (xdoc::topstring
   (xdoc::p
     "The element is inserted with respect to the binary search tree ordering
      and then rebalanced with respect to the @(tsee heapp) property."))
  :guard (mbe :logic (equal (hash x) hash)
              :exec (data::u32-equal (hash x) hash))
  :returns (tree$ treep)
  (if (tree-empty-p tree)
      (tree-node (tagged-element hash x) nil nil)
    (let* ((hash (mbe :logic (hash x) :exec hash))
           (head (tree->head tree))
           (head-elem (tagged-element->elem head)))
      (cond ((equal x head-elem)
             (tree-fix tree))
            ((<< x head-elem)
             (let* ((left$ (tree-insert x hash (tree->left tree)))
                    ;; TODO: return boolean flag indicating whether insertion
                    ;; was redundant. If it was, just exit.
                    (head-left$ (tree->head left$))
                    (tree$ (tree-node head
                                      left$
                                      (tree->right tree))))
               (if (heap<-with-hashes head-elem
                                      (tagged-element->elem head-left$)
                                      (tagged-element->hash head)
                                      (tagged-element->hash head-left$))
                   (rotate-right tree$)
                 tree$)))
            (t
             (let* ((right$ (tree-insert x hash (tree->right tree)))
                    ;; TODO: same comment as above.
                    (head-right$ (tree->head right$))
                    (tree$ (tree-node head
                                      (tree->left tree)
                                      right$)))
               (if (heap<-with-hashes head-elem
                                      (tagged-element->elem head-right$)
                                      (tagged-element->hash head)
                                      (tagged-element->hash head-right$))
                   (rotate-left tree$)
                 tree$))))))
  ;; Verified below
  :verify-guards nil)

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t tree-insert)))

(defrule tree-empty-p-of-tree-insert
  (not (tree-empty-p (tree-insert x hash tree)))
  :induct t
  :enable tree-insert)

(verify-guards tree-insert
  :hints (("Goal" :in-theory (enable data::u32-equal))))

(defrule tree-insert-type-prescription
  (consp (tree-insert x hash tree))
  :rule-classes :type-prescription
  :use tree-empty-p-of-tree-insert
  :enable tree-empty-p
  :disable tree-empty-p-of-tree-insert)

(defrule tree-insert-when-tree-equiv-congruence
  (implies (tree-equiv tree0 tree1)
           (equal (tree-insert x hash tree0)
                  (tree-insert x hash tree1)))
  :rule-classes :congruence
  :induct t
  :enable tree-insert)

;; Logically, the second argument is ignored. We choose to arbitrarily
;; normalize it to nil.
(defruled tree-insert-arg2-becomes-nil
  (equal (tree-insert x hash tree)
         (tree-insert x nil tree))
  :induct t
  :enable tree-insert)

(defrule tree-insert-when-arg2-not-nil-syntaxp
  (implies (syntaxp (not (equal hash ''nil)))
           (equal (tree-insert x hash tree)
                  (tree-insert x nil tree)))
  :by tree-insert-arg2-becomes-nil)

;;;;;;;;;;;;;;;;;;;;

(defrule tree-in-of-tree-insert
  (equal (tree-in x (tree-insert y hash tree))
         (or (equal x y)
             (tree-in x tree)))
  :induct t
  :enable tree-insert)

;;;;;;;;;;;;;;;;;;;;

(defrule <<-all-l-of-tree-insert
  (equal (<<-all-l (tree-insert y hash tree) x)
         (and (<< y x)
              (<<-all-l tree x)))
  :induct t
  :enable (<<-all-l
           tree-insert))

(defrule <<-all-r-of-tree-insert
  (equal (<<-all-r x (tree-insert y hash tree))
         (and (<< x y)
              (<<-all-r x tree)))
  :induct t
  :enable (<<-all-r
           tree-insert))

(defrule bst-of-tree-insert-when-bst
  (implies (bstp tree)
           (bstp (tree-insert x hash tree)))
  :induct t
  :enable (tree-insert
           bstp
           data::<<-rules))

;;;;;;;;;;;;;;;;;;;;

(defrule heap<-all-l-of-tree-insert
  (equal (heap<-all-l (tree-insert y hash tree) x)
         (and (heap< y x)
              (heap<-all-l tree x)))
  :induct t
  :enable (heap<-all-l
           tree-insert))

;;;;;;;;;;;;;;;;;;;;

(defruledl tree-insert-hmax-heap-invariants
  (implies (and (heapp tree)
                ;; In subsequent proofs, `a` will be the head of the parent node
                (heap<-all-l tree a))
           (if (or (tree-empty-p tree)
                   (heap< (tagged-element->elem (tree->head tree)) x))
               (and (equal (tagged-element->elem (tree->head (tree-insert x hash tree)))
                           x)
                    (heap<-all-l (tree->left (tree-insert x hash tree))
                                 a)
                    (heap<-all-l (tree->right (tree-insert x hash tree))
                                 a))
             (heap<-all-l (tree-insert x hash tree) a)))
  :induct t
  :enable (tree-insert
           heapp
           heap<-all-l-extra-rules))

;;;;;;;;;;;;;;;;;;;;

;; TODO: break off some of these lemmas into standalone rules?
(encapsulate ()
  (defrulel lemma0
    (implies (and (not (equal x (tagged-element->elem (tree->head tree))))
                  (not (heap< (tagged-element->elem (tree->head tree))
                              (tagged-element->elem
                                (tree->head (tree-insert x hash (tree->right tree))))))
                  (heapp tree))
             (heap< x (tagged-element->elem (tree->head tree))))
    :enable heap<-rules
    :use ((:instance tree-insert-hmax-heap-invariants
                     (a (tagged-element->elem (tree->head tree)))
                     (tree (tree->right tree)))))

  (defrulel lemma1
    (implies (and (not (equal x (tagged-element->elem (tree->head tree))))
                  (not (heap< (tagged-element->elem (tree->head tree))
                              (tagged-element->elem
                                (tree->head (tree-insert x hash (tree->left tree))))))
                  (heapp tree))
             (heap< x (tagged-element->elem (tree->head tree))))
    :enable heap<-rules
    :use ((:instance tree-insert-hmax-heap-invariants
                     (a (tagged-element->elem (tree->head tree)))
                     (tree (tree->left tree)))))

  (defrulel lemma2
    (implies (heapp tree)
             (heap<-all-l (tree->left (tree-insert x hash (tree->right tree)))
                          (tagged-element->elem (tree->head tree))))
    :enable heap<-all-l-extra-rules
    :use ((:instance tree-insert-hmax-heap-invariants
                     (a (tagged-element->elem (tree->head tree)))
                     (tree (tree->right tree)))))

  (defrulel lemma3
    (implies (and (not (equal x (tagged-element->elem (tree->head tree))))
                  (heapp tree))
             (heap<-all-l (tree->right (tree-insert x hash (tree->left tree)))
                          (tagged-element->elem (tree->head tree))))
    :enable heap<-all-l-extra-rules
    :use ((:instance tree-insert-hmax-heap-invariants
                     (a (tagged-element->elem (tree->head tree)))
                     (tree (tree->left tree)))))

  (defrule heapp-of-tree-insert-when-heapp
    (implies (heapp tree)
             (heapp (tree-insert x hash tree)))
    :induct t
    :enable tree-insert))

;;;;;;;;;;;;;;;;;;;;

(defrule tree-nodes-count-of-tree-insert
  (implies (bstp tree)
           (equal (tree-nodes-count (tree-insert x hash tree))
                  (if (tree-in x tree)
                      (tree-nodes-count tree)
                    (+ 1 (tree-nodes-count tree)))))
  :induct t
  :enable (tree-insert
           tree-nodes-count
           bstp
           data::<<-rules))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tree-singleton
  (x
   (hash (unsigned-byte-p 32 hash)))
  :guard (mbe :logic (equal (hash x) hash)
              :exec (data::u32-equal (hash x) hash))
  (mbe :logic (tree-insert x nil nil)
       :exec (tree-node (tagged-element hash x) nil nil))
  :enabled t
  :inline t
  :guard-hints (("Goal" :in-theory (enable data::u32-equal
                                           tree-insert))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define acl2-number-tree-insert
  ((x acl2-numberp)
   (hash (unsigned-byte-p 32 hash))
   (tree acl2-number-treep))
  :guard (mbe :logic (equal (hash x) hash)
              :exec (data::u32-equal (hash x) hash))
  (mbe :logic (tree-insert x hash tree)
       :exec
       (if (tree-empty-p tree)
           (tree-node (tagged-element hash x) nil nil)
         (let* ((hash (mbe :logic (hash x) :exec hash))
                (head (tree->head tree))
                (head-elem (tagged-element->elem head)))
           (cond ((= x head-elem)
                  (tree-fix tree))
                 ((data::acl2-number-<< x head-elem)
                  (let* ((left$ (acl2-number-tree-insert
                                  x hash (tree->left tree)))
                         (head-left$ (tree->head left$))
                         (tree$ (tree-node head
                                           left$
                                           (tree->right tree))))
                    (if (heap<-with-hashes head-elem
                                           (tagged-element->elem head-left$)
                                           (tagged-element->hash head)
                                           (tagged-element->hash head-left$))
                        (rotate-right tree$)
                      tree$)))
                 (t
                  (let* ((right$ (acl2-number-tree-insert
                                   x hash (tree->right tree)))
                         (head-right$ (tree->head right$))
                         (tree$ (tree-node head
                                           (tree->left tree)
                                           right$)))
                    (if (heap<-with-hashes head-elem
                                           (tagged-element->elem head-right$)
                                           (tagged-element->hash head)
                                           (tagged-element->hash head-right$))
                        (rotate-left tree$)
                      tree$)))))))
  :enabled t
  :guard-hints (("Goal" :in-theory (enable data::u32-equal
                                           tree-insert
                                           acl2-number-tree-insert
                                           tree-all-acl2-numberp)
                        ;; TODO: avoid expand hint
                        :expand (tree-insert x nil tree))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define symbol-tree-insert
  ((x symbolp)
   (hash (unsigned-byte-p 32 hash))
   (tree symbol-treep))
  :guard (mbe :logic (equal (hash x) hash)
              :exec (data::u32-equal (hash x) hash))
  (mbe :logic (tree-insert x hash tree)
       :exec
       (if (tree-empty-p tree)
           (tree-node (tagged-element hash x) nil nil)
         (let* ((hash (mbe :logic (hash x) :exec hash))
                (head (tree->head tree))
                (head-elem (tagged-element->elem head)))
           (cond ((eq x head-elem)
                  (tree-fix tree))
                 ((data::symbol-<< x head-elem)
                  (let* ((left$ (symbol-tree-insert
                                  x hash (tree->left tree)))
                         (head-left$ (tree->head left$))
                         (tree$ (tree-node head
                                           left$
                                           (tree->right tree))))
                    (if (heap<-with-hashes head-elem
                                           (tagged-element->elem head-left$)
                                           (tagged-element->hash head)
                                           (tagged-element->hash head-left$))
                        (rotate-right tree$)
                      tree$)))
                 (t
                  (let* ((right$ (symbol-tree-insert
                                   x hash (tree->right tree)))
                         (head-right$ (tree->head right$))
                         (tree$ (tree-node head
                                           (tree->left tree)
                                           right$)))
                    (if (heap<-with-hashes head-elem
                                           (tagged-element->elem head-right$)
                                           (tagged-element->hash head)
                                           (tagged-element->hash head-right$))
                        (rotate-left tree$)
                      tree$)))))))
  :enabled t
  :guard-hints (("Goal" :in-theory (enable data::u32-equal
                                           tree-insert
                                           symbol-tree-insert
                                           tree-all-symbolp)
                        ;; TODO: avoid expand hint
                        :expand (tree-insert x nil tree))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define eqlable-tree-insert
  ((x eqlablep)
   (hash (unsigned-byte-p 32 hash))
   (tree eqlable-treep))
  :guard (mbe :logic (equal (hash x) hash)
              :exec (data::u32-equal (hash x) hash))
  (mbe :logic (tree-insert x hash tree)
       :exec
       (if (tree-empty-p tree)
           (tree-node (tagged-element hash x) nil nil)
         (let* ((hash (mbe :logic (hash x) :exec hash))
                (head (tree->head tree))
                (head-elem (tagged-element->elem head)))
           (cond ((eql x head-elem)
                  (tree-fix tree))
                 ((data::eqlable-<< x head-elem)
                  (let* ((left$ (eqlable-tree-insert
                                  x hash (tree->left tree)))
                         (head-left$ (tree->head left$))
                         (tree$ (tree-node head
                                           left$
                                           (tree->right tree))))
                    (if (heap<-with-hashes head-elem
                                           (tagged-element->elem head-left$)
                                           (tagged-element->hash head)
                                           (tagged-element->hash head-left$))
                        (rotate-right tree$)
                      tree$)))
                 (t
                  (let* ((right$ (eqlable-tree-insert
                                   x hash (tree->right tree)))
                         (head-right$ (tree->head right$))
                         (tree$ (tree-node head
                                           (tree->left tree)
                                           right$)))
                    (if (heap<-with-hashes head-elem
                                           (tagged-element->elem head-right$)
                                           (tagged-element->hash head)
                                           (tagged-element->hash head-right$))
                        (rotate-left tree$)
                      tree$)))))))
  :enabled t
  :guard-hints (("Goal" :in-theory (enable data::u32-equal
                                           tree-insert
                                           eqlable-tree-insert
                                           tree-all-eqlablep)
                        ;; TODO: avoid expand hint
                        :expand (tree-insert x nil tree))))
