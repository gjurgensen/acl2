; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "TREESET")

(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)

(include-book "tree-defs")
(include-book "bst-order-defs")
(include-book "rotate-defs")
(include-book "in-defs")
(include-book "count-defs")
(include-book "subset-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(local (include-book "kestrel/utilities/ordinals" :dir :system))

(local (include-book "tree"))
(local (include-book "bst-order"))
(local (include-book "bst"))
(local (include-book "heap-order"))
(local (include-book "heap"))
(local (include-book "in"))
(local (include-book "count"))
(local (include-book "rotate"))
(local (include-book "subset"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tree-split
  (x
   (tree treep))
  :parents (implementation)
  :short "Split a tree into two disjoint subtrees."
  :long
  (xdoc::topstring
   (xdoc::p
     "When @('tree') is a @('set'), @('(tree-split x tree)') yields
      @('(mv in left right)') where:")
   (xdoc::ul
     (xdoc::li "@('in') is a boolean representing @('(tree-in x tree)').")
     (xdoc::li "@('left') is a @('set') containing all elements of @('tree')
                less than @('x') (with respect to @('bst<')).")
     (xdoc::li "@('right') is a @('set') containing all elements of @('tree')
                greater than @('x') (with respect to @('bst<'))."))
   (xdoc::p
     "The implementation is comparable to @('tree-insert') if we were to
      pretend @('x') is maximal with respect to @('heap<')."))
  :returns (mv (in booleanp :rule-classes :type-prescription)
               (left treep)
               (right treep))
  (cond ((tree-empty-p tree)
         (mv nil nil nil))
        ((equal x (tagged-element->elem (tree->head tree)))
         (mv t (tree->left tree) (tree->right tree)))
        ((bst< x (tagged-element->elem (tree->head tree)))
         ;; Interpret as a tree-node (use x instead of in)
         ;; (may violate heapp)
         (mv-let (in left$ right$)
                 (tree-split x (tree->left tree))
           (mbe :logic (let ((tree$ (rotate-right
                                      (tree-node (tree->head tree)
                                                 (tree-node x left$ right$)
                                                 (tree->right tree)))))
                         (mv in (tree->left tree$) (tree->right tree$)))
                ;; TODO: not clear this isn't simpler than the :logic branch
                ;; Also not clear whether the compiler couldn't just make this
                ;;   simplification (since rotate is inlined).
                :exec (mv in
                          left$
                          (tree-node (tree->head tree)
                                     right$
                                     (tree->right tree))))))
        (t
         (mv-let (in left$ right$)
                 (tree-split x (tree->right tree))
           (mbe :logic (let ((tree$ (rotate-left
                                      (tree-node (tree->head tree)
                                                 (tree->left tree)
                                                 (tree-node x left$ right$)))))
                         (mv in (tree->left tree$) (tree->right tree$)))
                :exec (mv in
                          (tree-node (tree->head tree)
                                     (tree->left tree)
                                     left$)
                          right$)))))
  :verify-guards :after-returns)

;;;;;;;;;;;;;;;;;;;;

(defrule tree-split.left-when-type-prescription
  (or (consp (mv-nth 1 (tree-split x tree)))
      (equal (mv-nth 1 (tree-split x tree)) nil))
  :rule-classes :type-prescription
  :induct t
  :enable tree-split)

(defrule tree-split.right-when-type-prescription
  (or (consp (mv-nth 2 (tree-split x tree)))
      (equal (mv-nth 2 (tree-split x tree)) nil))
  :rule-classes :type-prescription
  :induct t
  :enable tree-split)

(defrule tree-split-when-tree-equiv-congruence
  (implies (tree-equiv tree0 tree1)
           (equal (tree-split x tree0)
                  (tree-split x tree1)))
  :rule-classes :congruence
  :induct t
  :enable tree-split)

;;;;;;;;;;;;;;;;;;;;

(defruled tree-split.in-when-tree-empty-p
  (implies (tree-empty-p tree)
           (not (mv-nth 0 (tree-split x tree))))
  :enable tree-split)

(defrule tree-split.in-when-tree-empty-p-cheap
  (implies (tree-empty-p tree)
           (not (mv-nth 0 (tree-split x tree))))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :enable tree-split.in-when-tree-empty-p)

;;;;;;;;;;;;;;;;;;;;

(defruled tree-empty-p-of-tree-split.left-when-tree-empty-p
  (implies (tree-empty-p tree)
           (tree-empty-p (mv-nth 1 (tree-split x tree))))
  :enable tree-split)

(defrule tree-empty-p-of-tree-split.left-when-tree-empty-p-cheap
  (implies (tree-empty-p tree)
           (tree-empty-p (mv-nth 1 (tree-split x tree))))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :enable tree-empty-p-of-tree-split.left-when-tree-empty-p)

;;;;;;;;;;;;;;;;;;;;

(defruled tree-empty-p-of-tree-split.right-when-tree-empty-p
  (implies (tree-empty-p tree)
           (tree-empty-p (mv-nth 2 (tree-split x tree))))
  :enable tree-split)

(defrule tree-empty-p-of-tree-split.right-when-tree-empty-p-cheap
  (implies (tree-empty-p tree)
           (tree-empty-p (mv-nth 2 (tree-split x tree))))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :enable tree-empty-p-of-tree-split.right-when-tree-empty-p)

;;;;;;;;;;;;;;;;;;;;

(defrule tree-split.in-when-bstp
  (implies (bstp tree)
           (equal (mv-nth 0 (tree-split x tree))
                  (tree-in x tree)))
  :induct t
  :enable (tree-split
           tree-in
           bstp
           bst<-rules))

;;;;;;;;;;;;;;;;;;;;

(defruled bst<-all-l-of-tree-split.left-when-bst<-all-l
  (implies (bst<-all-l tree y)
           (bst<-all-l (mv-nth 1 (tree-split x tree)) y))
  :induct t
  :enable tree-split)

(defrule bst<-all-l-of-tree-split.left-when-bst<-all-l-cheap
  (implies (bst<-all-l tree y)
           (bst<-all-l (mv-nth 1 (tree-split x tree)) y))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by bst<-all-l-of-tree-split.left-when-bst<-all-l)

;;;;;;;;;;;;;;;;;;;;

(defruled bst<-all-l-of-tree-split.right-when-bst<-all-l
  (implies (bst<-all-l tree y)
           (bst<-all-l (mv-nth 2 (tree-split x tree)) y))
  :induct t
  :enable tree-split)

(defrule bst<-all-l-of-tree-split.right-when-bst<-all-l-cheap
  (implies (bst<-all-l tree y)
           (bst<-all-l (mv-nth 2 (tree-split x tree)) y))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by bst<-all-l-of-tree-split.right-when-bst<-all-l)

;;;;;;;;;;;;;;;;;;;;

(defruled bst<-all-r-of-arg1-and-tree-split.left-when-bst<-all-r
  (implies (bst<-all-r x tree)
           (bst<-all-r x (mv-nth 1 (tree-split y tree))))
  :induct t
  :enable tree-split)

(defrule bst<-all-r-of-arg1-and-tree-split.left-when-bst<-all-r-cheap
  (implies (bst<-all-r x tree)
           (bst<-all-r x (mv-nth 1 (tree-split y tree))))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by bst<-all-r-of-arg1-and-tree-split.left-when-bst<-all-r)

;;;;;;;;;;;;;;;;;;;;

(defruled bst<-all-r-of-arg1-and-tree-split.right-when-bst<-all-r
  (implies (bst<-all-r x tree)
           (bst<-all-r x (mv-nth 2 (tree-split y tree))))
  :induct t
  :enable tree-split)

(defrule bst<-all-r-of-arg1-and-tree-split.right-when-bst<-all-r-cheap
  (implies (bst<-all-r x tree)
           (bst<-all-r x (mv-nth 2 (tree-split y tree))))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by bst<-all-r-of-arg1-and-tree-split.right-when-bst<-all-r)

;;;;;;;;;;;;;;;;;;;;

(defruled bst<-all-l-when-bst<-all-l-of-tree-split.left-and-tree-split.right
  (implies (and (bst<-all-l (mv-nth 1 (tree-split x tree)) y)
                (bst<-all-l (mv-nth 2 (tree-split x tree)) y)
                (bst< x y))
           (bst<-all-l tree y))
  :induct t
  :enable tree-split)

(defruled bst<-all-r-when-bst<-all-l-of-arg1-and-tree-split.left-and-tree-split.right
  (implies (and (bst<-all-r x (mv-nth 1 (tree-split y tree)))
                (bst<-all-r x (mv-nth 2 (tree-split y tree)))
                (bst< x y))
           (bst<-all-r x tree))
  :induct t
  :enable tree-split)

;;;;;;;;;;;;;;;;;;;;

(defrule bstp-of-tree-split.left-when-bstp
  (implies (bstp tree)
           (bstp (mv-nth 1 (tree-split x tree))))
  :induct t
  :enable (tree-split
           bstp))

(defrule bstp-of-tree-split.right-when-bstp
  (implies (bstp tree)
           (bstp (mv-nth 2 (tree-split x tree))))
  :induct t
  :enable (tree-split
           bstp))

;;;;;;;;;;;;;;;;;;;;

(defrule bst<-all-l-of-tree-split.left-of-arg1-and-arg1
  (implies (bstp tree)
           (bst<-all-l (mv-nth 1 (tree-split x tree)) x))
  :induct t
  :enable (tree-split
           bstp
           bst<-all-extra-rules
           bst<-rules))

(defrule bst<-all-r-of-arg1-and-tree-split.right-of-arg1
  (implies (bstp tree)
           (bst<-all-r x (mv-nth 2 (tree-split x tree))))
  :induct t
  :enable (tree-split
           bstp
           bst<-all-extra-rules
           bst<-rules))

;;;;;;;;;;;;;;;;;;;;

(defruled heap<-all-l-of-tree-split.left-when-heap<-all-l
  (implies (heap<-all-l tree y)
           (heap<-all-l (mv-nth 1 (tree-split x tree)) y))
  :induct t
  :enable tree-split)

(defrule heap<-all-l-of-tree-split.left-when-heap<-all-l-cheap
  (implies (heap<-all-l tree y)
           (heap<-all-l (mv-nth 1 (tree-split x tree)) y))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :enable heap<-all-l-of-tree-split.left-when-heap<-all-l)

;;;;;;;;;;;;;;;;;;;;

(defruled heap<-all-l-of-tree-split.right-when-heap<-all-l
  (implies (heap<-all-l tree y)
           (heap<-all-l (mv-nth 2 (tree-split x tree)) y))
  :induct t
  :enable tree-split)

(defrule heap<-all-l-of-tree-split.right-when-heap<-all-l-cheap
  (implies (heap<-all-l tree y)
           (heap<-all-l (mv-nth 2 (tree-split x tree)) y))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :enable heap<-all-l-of-tree-split.right-when-heap<-all-l)

;;;;;;;;;;;;;;;;;;;;

(defruled heap<-all-l-when-heap<-all-l-of-tree-split.left-and-tree-split.right
  (implies (and (heap<-all-l (mv-nth 1 (tree-split x tree)) y)
                (heap<-all-l (mv-nth 2 (tree-split x tree)) y)
                (heap< x y))
           (heap<-all-l tree y))
  :induct t
  :enable tree-split)

;;;;;;;;;;;;;;;;;;;;

(defrule heapp-of-tree-split.left-when-heapp
  (implies (heapp tree)
           (heapp (mv-nth 1 (tree-split x tree))))
  :induct t
  :enable tree-split)

(defrule heapp-of-tree-split.right-when-heapp
  (implies (heapp tree)
           (heapp (mv-nth 2 (tree-split x tree))))
  :induct t
  :enable tree-split)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled tree-in-when-tree-in-of-tree-split.left
  (implies (tree-in x (mv-nth 1 (tree-split y tree)))
           (tree-in x tree))
  :induct t
  :enable tree-split)

(defrule tree-in-when-tree-in-of-tree-split.left-forward-chaining
  (implies (tree-in x (mv-nth 1 (tree-split y tree)))
           (tree-in x tree))
  :rule-classes :forward-chaining
  :enable tree-in-when-tree-in-of-tree-split.left)

;;;;;;;;;;;;;;;;;;;;

(defruled tree-in-when-tree-in-of-tree-split.right
  (implies (tree-in x (mv-nth 2 (tree-split y tree)))
           (tree-in x tree))
  :induct t
  :enable tree-split)

(defrule tree-in-when-tree-in-of-tree-split.right-forward-chaining
  (implies (tree-in x (mv-nth 2 (tree-split y tree)))
           (tree-in x tree))
  :rule-classes :forward-chaining
  :enable tree-in-when-tree-in-of-tree-split.right)

;;;;;;;;;;;;;;;;;;;;

(defrule tree-in-of-tree-split.left
  (implies (bstp tree)
           (equal (tree-in x (mv-nth 1 (tree-split y tree)))
                  (and (tree-in x tree)
                       (bst< x y))))
  :induct t
  :enable (tree-split
           tree-in-extra-rules
           bst<-rules
           bst<-all-extra-rules))

(defrule tree-in-of-tree-split.right
  (implies (bstp tree)
           (equal (tree-in x (mv-nth 2 (tree-split y tree)))
                  (and (tree-in x tree)
                       (bst< y x))))
  :induct t
  :enable (tree-split
           tree-in-extra-rules
           bst<-rules
           bst<-all-extra-rules))

;;;;;;;;;;;;;;;;;;;;

;; TODO: useful?
(defruled tree-in-becomes-tree-in-of-tree-split
  (equal (tree-in x tree)
         (or (and (equal x y)
                  (mv-nth 0 (tree-split y tree)))
             (tree-in x (mv-nth 1 (tree-split y tree)))
             (tree-in x (mv-nth 2 (tree-split y tree)))))
  :induct t
  :enable tree-split)

;;;;;;;;;;;;;;;;;;;;

(defruled bst<-all-r-when-tree-empty-p-of-tree-split.left
  (implies (and (bstp tree)
                (bst< x y)
                (tree-empty-p (mv-nth 1 (tree-split y tree))))
           (bst<-all-r x tree))
  :induct t
  :enable (tree-split
           bst<-rules
           bst<-all-extra-rules))

;; TODO: is this a reasonable rule?
(defrule bst<-all-r-when-tree-empty-p-of-tree-split.left-forward-chaining
  (implies (and (tree-empty-p (mv-nth 1 (tree-split y tree)))
                (bst< x y)
                (bstp tree))
           (bst<-all-r x tree))
  :rule-classes :forward-chaining
  :by bst<-all-r-when-tree-empty-p-of-tree-split.left)

;;;;;;;;;;;;;;;;;;;;

(defruled bst<-all-l-when-tree-empty-p-of-tree-split.right
  (implies (and (bstp tree)
                (bst< y x)
                (tree-empty-p (mv-nth 2 (tree-split y tree))))
           (bst<-all-l tree x))
  :induct t
  :enable (tree-split
           bst<-all-extra-rules)
  :prep-lemmas
  ((defrule lemma0
     (implies (and (not (bst< y (tagged-element->elem (tree->head tree))))
                   (bst<-all-l (tree->right tree) x)
                   (bstp tree)
                   (bst< y x))
              (bst<-all-l tree x))
     :enable (bst<-rules
              bst<-all-extra-rules)
     :disable bst<-trichotomy
     :use ((:instance bst<-trichotomy
                      (x (tagged-element->elem (tree->head tree))))))))

;; TODO: is this a reasonable rule?
(defrule bst<-all-l-when-tree-empty-p-of-tree-split.right-forward-chaining
  (implies (and (tree-empty-p (mv-nth 2 (tree-split y tree)))
                (bst< y x)
                (bstp tree))
           (bst<-all-l tree x))
  :rule-classes :forward-chaining
  :by bst<-all-l-when-tree-empty-p-of-tree-split.right)

;;;;;;;;;;;;;;;;;;;;

(defrule tree-empty-p-of-tree-split.left-when-bst<-all-r
  (implies (bst<-all-r x tree)
           (tree-empty-p (mv-nth 1 (tree-split x tree))))
  :induct t
  :enable tree-split)

(defrule tree-empty-p-of-tree-split.right-when-bst<-all-r
  (implies (bst<-all-l tree x)
           (tree-empty-p (mv-nth 2 (tree-split x tree))))
  :induct t
  :enable (tree-split
           bst<-rules))

;;;;;;;;;;;;;;;;;;;;

;; (defrule subset-of-tree-split.left
;;   (implies (setp set)
;;            (subset (mv-nth 1 (tree-split x set))
;;                    set))
;;   :enable (tree-split
;;            pick-a-point
;;            subset))
;;
;; (defrule subset-of-tree-split.right
;;   (implies (setp set)
;;            (subset (mv-nth 2 (tree-split x set))
;;                    set))
;;   :enable (tree-split
;;            pick-a-point
;;            subset))

;;;;;;;;;;;;;;;;;;;;

(defrule acl2-count-of-tree-split.left-linear
  (implies (treep tree)
           (<= (acl2-count (mv-nth 1 (tree-split x tree)))
               (acl2-count tree)))
  :rule-classes :linear
  :induct t
  :enable tree-split)

(defrule acl2-count-of-tree-split.right-linear
  (<= (acl2-count (mv-nth 2 (tree-split x tree)))
      (acl2-count tree))
  :rule-classes :linear
  :induct t
  :enable tree-split)

;;;;;;;;;;;;;;;;;;;;

(defruled tree-nodes-count-becomes-tree-nodes-count-of-tree-split-when-not-tree-in
  (implies (not (tree-in x tree))
           (equal (tree-nodes-count tree)
                  (+ (tree-nodes-count (mv-nth 1 (tree-split x tree)))
                     (tree-nodes-count (mv-nth 2 (tree-split x tree))))))
  :induct t
  :enable (tree-split
           tree-nodes-count))

(defruled tree-nodes-count-becomes-tree-nodes-count-of-tree-split
  (implies (bstp tree)
           (equal (tree-nodes-count tree)
                  (if (tree-in x tree)
                      (+ (tree-nodes-count (mv-nth 1 (tree-split x tree)))
                         (tree-nodes-count (mv-nth 2 (tree-split x tree)))
                         1)
                    (+ (tree-nodes-count (mv-nth 1 (tree-split x tree)))
                       (tree-nodes-count (mv-nth 2 (tree-split x tree)))))))
  :induct t
  :enable (tree-split
           tree-nodes-count
           bst<-rules))

;; Very awkward rule
;; (defrule tree-nodes-count-becomes-tree-nodes-count-of-tree-split-forward-chaining
;;   (implies (bstp tree)
;;            (equal (tree-nodes-count tree)
;;                   (if (tree-in x tree)
;;                       (+ (tree-nodes-count (mv-nth 1 (tree-split x tree)))
;;                          (tree-nodes-count (mv-nth 2 (tree-split x tree)))
;;                          1)
;;                     (+ (tree-nodes-count (mv-nth 1 (tree-split x tree)))
;;                        (tree-nodes-count (mv-nth 2 (tree-split x tree)))))))
;;   :rule-classes ((:forward-chaining :trigger-terms
;;                   ((tree-nodes-count (mv-nth 1 (tree-split x tree)))
;;                    (tree-nodes-count (mv-nth 2 (tree-split x tree))))))
;;   :use tree-nodes-count-becomes-tree-nodes-count-of-tree-split)

;; Very awkward rule
(defrule tree-nodes-count-becomes-tree-nodes-count-of-tree-split-linear
  (implies (bstp tree)
           (equal (tree-nodes-count tree)
                  (if (tree-in x tree)
                      (+ (tree-nodes-count (mv-nth 1 (tree-split x tree)))
                         (tree-nodes-count (mv-nth 2 (tree-split x tree)))
                         1)
                    (+ (tree-nodes-count (mv-nth 1 (tree-split x tree)))
                       (tree-nodes-count (mv-nth 2 (tree-split x tree)))))))
  :rule-classes ((:linear :trigger-terms
                  ((tree-nodes-count (mv-nth 1 (tree-split x tree)))
                   (tree-nodes-count (mv-nth 2 (tree-split x tree))))))
  :use tree-nodes-count-becomes-tree-nodes-count-of-tree-split)

;;;;;;;;;;;;;;;;;;;;

(defrule tree-nodes-count-of-tree-split.left-and-tree-split.right-linear
  (implies (bstp tree)
           (<= (tree-nodes-count tree)
               (+ (tree-nodes-count (mv-nth 1 (tree-split x tree)))
                  (tree-nodes-count (mv-nth 2 (tree-split x tree)))
                  1)))
  :rule-classes ((:linear :trigger-terms
                  ((tree-nodes-count (mv-nth 1 (tree-split x tree)))
                   (tree-nodes-count (mv-nth 2 (tree-split x tree))))))
  :use tree-nodes-count-becomes-tree-nodes-count-of-tree-split)

(defruled tree-nodes-count-of-tree-split.left-linear
  (<= (tree-nodes-count (mv-nth 1 (tree-split x tree)))
      (tree-nodes-count tree))
  :rule-classes :linear
  :induct t
  :enable (tree-split
           tree-nodes-count))

(defruled tree-nodes-count-of-tree-split.right-linear
  (<= (tree-nodes-count (mv-nth 2 (tree-split x tree)))
      (tree-nodes-count tree))
  :rule-classes :linear
  :induct t
  :enable (tree-split
           tree-nodes-count))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule tree-split-of-tree->head
  (equal (tree-split (tagged-element->elem (tree->head tree)) tree)
         (mv (not (tree-empty-p tree))
             (tree->left tree)
             (tree->right tree)))
  :enable tree-split)

(defrule tree-split-of-bind-tree->head-cheap
  (implies (equal x (tagged-element->elem (tree->head tree)))
           (equal (tree-split x tree)
                  (mv (not (tree-empty-p tree))
                      (tree->left tree)
                      (tree->right tree))))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :use tree-split-of-tree->head
  :disable tree-split-of-tree->head)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthy tree-split-extra-rules
  '(tree-split.in-when-tree-empty-p
    tree-empty-p-of-tree-split.left-when-tree-empty-p
    tree-empty-p-of-tree-split.right-when-tree-empty-p
    bst<-all-l-of-tree-split.left-when-bst<-all-l
    bst<-all-l-of-tree-split.right-when-bst<-all-l
    bst<-all-r-of-arg1-and-tree-split.left-when-bst<-all-r
    bst<-all-r-of-arg1-and-tree-split.right-when-bst<-all-r
    bst<-all-l-when-bst<-all-l-of-tree-split.left-and-tree-split.right
    bst<-all-r-when-bst<-all-l-of-arg1-and-tree-split.left-and-tree-split.right
    heap<-all-l-of-tree-split.left-when-heap<-all-l
    heap<-all-l-of-tree-split.right-when-heap<-all-l
    heap<-all-l-when-heap<-all-l-of-tree-split.left-and-tree-split.right
    tree-in-when-tree-in-of-tree-split.left
    tree-in-when-tree-in-of-tree-split.right))
