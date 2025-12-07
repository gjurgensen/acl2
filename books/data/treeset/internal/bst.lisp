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

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(local (include-book "kestrel/utilities/ordinals" :dir :system))

(local (include-book "tree"))
(local (include-book "bst-order"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define bst<-all-l
  ((tree treep)
   x)
  (declare (xargs :type-prescription (booleanp (bst<-all-l tree x))))
  :parents (tree)
  :short "Check that all members of a tree are @(tsee bst<) some value."
  (or (tree-empty-p tree)
      (and (bst< (tagged-element->elem (tree->head tree)) x)
           (bst<-all-l (tree->left tree) x)
           (bst<-all-l (tree->right tree) x))))

(define bst<-all-r
  (x
   (tree treep))
  (declare (xargs :type-prescription (booleanp (bst<-all-r x tree))))
  :parents (tree)
  :short "Check that some value is @(tsee bst<) all members of a tree."
  (or (tree-empty-p tree)
      (and (bst< x (tagged-element->elem (tree->head tree)))
           (bst<-all-r x (tree->left tree))
           (bst<-all-r x (tree->right tree)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule bst<-all-l-when-tree-equiv-congruence
  (implies (tree-equiv x y)
           (equal (bst<-all-l x a)
                  (bst<-all-l y a)))
  :rule-classes :congruence
  :enable tree-equiv
  :expand ((bst<-all-l x a)
           (bst<-all-l y a)))

(defrule bst<-all-r-when-tree-equiv-congruence
  (implies (tree-equiv x y)
           (equal (bst<-all-r a x)
                  (bst<-all-r a y)))
  :rule-classes :congruence
  :enable tree-equiv
  :expand ((bst<-all-r a x)
           (bst<-all-r a y)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule bst<-all-l-of-nil
  (bst<-all-l nil tree)
  :enable bst<-all-l)

(defrule bst<-all-r-of-arg1-and-nil
  (bst<-all-r tree nil)
  :enable bst<-all-r)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled bst<-all-l-when-tree-empty-p
  (implies (tree-empty-p tree)
           (bst<-all-l tree x))
  :enable bst<-all-l)

(defrule bst<-all-l-when-tree-empty-p-cheap
  (implies (tree-empty-p tree)
           (bst<-all-l tree x))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by bst<-all-l-when-tree-empty-p)

(defruled bst<-all-r-when-tree-empty-p
  (implies (tree-empty-p tree)
           (bst<-all-r x tree))
  :enable bst<-all-r)

(defrule bst<-all-r-when-tree-empty-p-cheap
  (implies (tree-empty-p tree)
           (bst<-all-r x tree))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by bst<-all-r-when-tree-empty-p)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled bst<-all-l-when-bst<-all-r
  (implies (bst<-all-r x tree)
           (equal (bst<-all-l tree x)
                  (tree-empty-p tree)))
  :induct t
  :enable (bst<-all-r
           bst<-all-l
           bst<-rules))

(defruled bst<-all-l-when-bst<-all-r-forward-chaining
  (implies (bst<-all-r x tree)
           (equal (bst<-all-l tree x)
                  (tree-empty-p tree)))
  :rule-classes :forward-chaining
  :by bst<-all-l-when-bst<-all-r)

(defrule bst<-all-l-when-bst<-all-r-and-not-tree-empty-p-forward-chaining
  (implies (and (bst<-all-r x tree)
                (not (tree-empty-p tree)))
           (not (bst<-all-l tree x)))
  :rule-classes :forward-chaining
  :enable bst<-all-l-when-bst<-all-r)

;;;;;;;;;;;;;;;;;;;;

(defruled bst<-all-r-when-bst<-all-l
  (implies (bst<-all-l tree x)
           (equal (bst<-all-r x tree)
                  (tree-empty-p tree)))
  :induct t
  :enable (bst<-all-l
           bst<-all-r
           bst<-rules))

(defruled bst<-all-r-when-bst<-all-l-forward-chaining
  (implies (bst<-all-l tree x)
           (equal (bst<-all-r x tree)
                  (tree-empty-p tree)))
  :rule-classes :forward-chaining
  :by bst<-all-r-when-bst<-all-l)

(defrule bst<-all-r-when-bst<-all-l-and-not-tree-empty-p-forward-chaining
  (implies (and (bst<-all-l tree x)
                (not (tree-empty-p tree)))
           (not (bst<-all-r x tree)))
  :rule-classes :forward-chaining
  :enable bst<-all-r-when-bst<-all-l)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule tree-empty-p-when-not-bst<-all-l-forward-chaining
  (implies (not (bst<-all-l tree x))
           (not (tree-empty-p tree)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :enable bst<-all-l)

(defrule tree-empty-p-when-not-bst<-all-r-forward-chaining
  (implies (not (bst<-all-r x tree))
           (not (tree-empty-p tree)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :enable bst<-all-r)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule bst<-all-l-of-arg1-and-tree->head
  (equal (bst<-all-l tree (tagged-element->elem (tree->head tree)))
         (tree-empty-p tree))
  :enable (bst<-all-l
           tree->head
           bst<-rules))

(defrule bst<-all-r-of-tree->head
  (equal (bst<-all-r (tagged-element->elem (tree->head tree)) tree)
         (tree-empty-p tree))
  :enable (bst<-all-r
           tree->head
           bst<-rules))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled bst<-all-l-of-tree->left-when-bst<-all-l
  (implies (bst<-all-l tree x)
           (bst<-all-l (tree->left tree) x))
  :enable bst<-all-l)

(defrule bst<-all-l-of-tree->left-when-bst<-all-l-cheap
  (implies (bst<-all-l tree x)
           (bst<-all-l (tree->left tree) x))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by bst<-all-l-of-tree->left-when-bst<-all-l)

(defruled bst<-all-l-of-tree->right-when-bst<-all-l
  (implies (bst<-all-l tree x)
           (bst<-all-l (tree->right tree) x))
  :enable bst<-all-l)

(defrule bst<-all-l-of-tree->right-when-bst<-all-l-cheap
  (implies (bst<-all-l tree x)
           (bst<-all-l (tree->right tree) x))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by bst<-all-l-of-tree->right-when-bst<-all-l)

;;;;;;;;;;;;;;;;;;;;

(defruled bst<-all-r-of-arg1-and-tree->left-when-bst<-all-r
  (implies (bst<-all-r x tree)
           (bst<-all-r x (tree->left tree)))
  :enable bst<-all-r)

(defrule bst<-all-r-of-arg1-and-tree->left-when-bst<-all-r-cheap
  (implies (bst<-all-r x tree)
           (bst<-all-r x (tree->left tree)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by bst<-all-r-of-arg1-and-tree->left-when-bst<-all-r)

(defruled bst<-all-r-of-arg1-and-tree->right-when-bst<-all-r
  (implies (bst<-all-r x tree)
           (bst<-all-r x (tree->right tree)))
  :enable bst<-all-r)

(defrule bst<-all-r-of-arg1-and-tree->right-when-bst<-all-r-cheap
  (implies (bst<-all-r x tree)
           (bst<-all-r x (tree->right tree)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by bst<-all-r-of-arg1-and-tree->right-when-bst<-all-r)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule bst<-all-l-of-tree-node
  (equal (bst<-all-l (tree-node head left right) x)
         (and (bst< (tagged-element->elem head) x)
              (bst<-all-l left x)
              (bst<-all-l right x)))
  :enable bst<-all-l)

(defrule bst<-all-r-of-arg1-and-tree-node
  (equal (bst<-all-r x (tree-node head left right))
         (and (bst< x (tagged-element->elem head))
              (bst<-all-r x left)
              (bst<-all-r x right)))
  :enable bst<-all-r)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled bst<-all-l-weaken
  (implies (and (bst< x y)
                (bst<-all-l tree x))
           (bst<-all-l tree y))
  :induct t
  :enable (bst<-all-l
           bst<-rules))

(defruled bst<-all-l-weaken2
  (implies (and (not (bst< x y))
                (bst<-all-l tree y))
           (bst<-all-l tree x))
  :enable (bst<-all-l-weaken
           bst<-rules)
  :disable bst<-trichotomy
  :use ((:instance bst<-trichotomy
                   (x y)
                   (y x))))

;;;;;;;;;;;;;;;;;;;;

(defruled bst<-all-r-weaken
  (implies (and (bst< x y)
                (bst<-all-r y tree))
           (bst<-all-r x tree))
  :induct t
  :enable (bst<-all-r
           bst<-rules))

(defruled bst<-all-r-weaken2
  (implies (and (not (bst< x y))
                (bst<-all-r x tree))
           (bst<-all-r y tree))
  :enable (bst<-all-r-weaken
            bst<-rules)
  :disable bst<-trichotomy
  :use ((:instance bst<-trichotomy
                   (x y)
                   (y x))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule bst<-of-tree->head-when-bst<-all-l
  (implies (and (bst<-all-l tree x)
                (not (tree-empty-p tree)))
           (bst< (tagged-element->elem (tree->head tree)) x))
  :rule-classes ((:rewrite :backchain-limit-lst (0 nil)))
  :enable bst<-all-l)

(defrule bst<-of-arg1-and-tree->head-when-bst<-all-r-arg1
  (implies (and (bst<-all-r x tree)
                (not (tree-empty-p tree)))
           (bst< x (tagged-element->elem (tree->head tree))))
  :rule-classes ((:rewrite :backchain-limit-lst (0 nil)))
  :enable bst<-all-r)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define bstp
  ((tree treep))
  (declare (xargs :type-prescription (booleanp (bstp tree))))
  :parents (tree)
  :short "Check the binary search tree property."
  :long
  (xdoc::topstring
   (xdoc::p
     "This recognizer is currently inefficient, operating in @($O(n^2)$) time
      instead of @($O(n)$). Eventually we hope to add an @(tsee mbe) with a
      linear-time executable version."))
  (or (tree-empty-p tree)
      (and (bstp (tree->left tree))
           (bstp (tree->right tree))
           (bst<-all-l (tree->left tree)
                       (tagged-element->elem (tree->head tree)))
           (bst<-all-r (tagged-element->elem (tree->head tree))
                       (tree->right tree)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule bstp-when-tree-equiv-congruence
  (implies (tree-equiv tree0 tree1)
           (equal (bstp tree0)
                  (bstp tree1)))
  :rule-classes :congruence
  :enable tree-equiv
  :expand ((bstp tree0)
           (bstp tree1)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled bstp-of-tree->left-when-tree-orderdp
  (implies (bstp tree)
           (bstp (tree->left tree)))
  :enable bstp)

(defrule bstp-of-tree->left-when-tree-orderdp-cheap
  (implies (bstp tree)
           (bstp (tree->left tree)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by bstp-of-tree->left-when-tree-orderdp)

(defruled bstp-of-tree->right-when-bstp
  (implies (bstp tree)
           (bstp (tree->right tree)))
  :enable bstp)

(defrule bstp-of-tree->right-when-bstp-cheap
  (implies (bstp tree)
           (bstp (tree->right tree)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by bstp-of-tree->right-when-bstp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled bstp-when-tree-empty-p
  (implies (tree-empty-p tree)
           (bstp tree))
  :enable bstp)

(defrule bstp-when-tree-empty-p-cheap
  (implies (tree-empty-p tree)
           (bstp tree))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by bstp-when-tree-empty-p)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled bstp-when-not-tree-empty-p
  (implies (not (tree-empty-p tree))
           (equal (bstp tree)
                  (and (bstp (tree->left tree))
                       (bstp (tree->right tree))
                       (bst<-all-l (tree->left tree)
                                   (tagged-element->elem (tree->head tree)))
                       (bst<-all-r (tagged-element->elem (tree->head tree))
                                   (tree->right tree)))))
  :enable bstp)

(defrule bstp-when-not-tree-empty-p-cheap
  (implies (not (tree-empty-p tree))
           (equal (bstp tree)
                  (and (bstp (tree->left tree))
                       (bstp (tree->right tree))
                       (bst<-all-l (tree->left tree)
                                   (tagged-element->elem (tree->head tree)))
                       (bst<-all-r (tagged-element->elem (tree->head tree))
                                   (tree->right tree)))))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by bstp-when-not-tree-empty-p)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule bstp-of-tree-node
  (equal (bstp (tree-node head left right))
         (and (bstp left)
              (bstp right)
              (bst<-all-l left (tagged-element->elem head))
              (bst<-all-r (tagged-element->elem head) right)))
  :enable bstp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled bst<-of-tree->head-tree->left-and-tree->head
  (implies (and (bstp tree)
                (not (tree-empty-p (tree->left tree))))
           (bst< (tagged-element->elem (tree->head (tree->left tree)))
                 (tagged-element->elem (tree->head tree)))))

(defruled bst<-of-tree->head-and-tree->head-tree->right
  (implies (and (bstp tree)
                (not (tree-empty-p (tree->right tree))))
           (bst< (tagged-element->elem (tree->head tree))
                 (tagged-element->elem (tree->head (tree->right tree))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule bst<-all-l-of-tree->left-and-tree->head-when-bstp
  (implies (bstp set)
           (bst<-all-l (tree->left set)
                       (tagged-element->elem (tree->head set)))))

(defrule bst<-all-r-of-tree->head-and-tree->right-when-bstp
  (implies (bstp tree)
           (bst<-all-r (tagged-element->elem (tree->head tree))
                       (tree->right tree))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthy bst<-all-extra-rules
  '(bst<-all-l-when-tree-empty-p
    bst<-all-r-when-tree-empty-p
    bst<-all-l-when-bst<-all-r-forward-chaining
    bst<-all-r-when-bst<-all-l-forward-chaining
    bst<-all-l-of-tree->left-when-bst<-all-l
    bst<-all-l-of-tree->right-when-bst<-all-l
    bst<-all-r-of-arg1-and-tree->left-when-bst<-all-r
    bst<-all-r-of-arg1-and-tree->right-when-bst<-all-r
    bst<-all-l-weaken
    bst<-all-l-weaken2
    bst<-all-r-weaken
    bst<-all-r-weaken2))

(defthy bstp-extra-rules
  '(bstp-of-tree->left-when-tree-orderdp
    bstp-of-tree->right-when-bstp
    bstp-when-tree-empty-p
    bstp-when-not-tree-empty-p
    bst<-of-tree->head-tree->left-and-tree->head
    bst<-of-tree->head-and-tree->head-tree->right))
