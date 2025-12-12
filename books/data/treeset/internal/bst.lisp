; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "TREESET")

(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)

(include-book "data/utilities/total-order-defs" :dir :system)

(include-book "tree-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(local (include-book "kestrel/utilities/ordinals" :dir :system))

(local (include-book "data/utilities/total-order" :dir :system))

(local (include-book "tree"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define <<-all-l
  ((tree treep)
   x)
  (declare (xargs :type-prescription (booleanp (<<-all-l tree x))))
  :parents (tree)
  :short "Check that all members of a tree are @(tsee <<) some value."
  (or (tree-empty-p tree)
      (and (<< (tagged-element->elem (tree->head tree)) x)
           (<<-all-l (tree->left tree) x)
           (<<-all-l (tree->right tree) x))))

(define <<-all-r
  (x
   (tree treep))
  (declare (xargs :type-prescription (booleanp (<<-all-r x tree))))
  :parents (tree)
  :short "Check that some value is @(tsee <<) all members of a tree."
  (or (tree-empty-p tree)
      (and (<< x (tagged-element->elem (tree->head tree)))
           (<<-all-r x (tree->left tree))
           (<<-all-r x (tree->right tree)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule <<-all-l-when-tree-equiv-congruence
  (implies (tree-equiv x y)
           (equal (<<-all-l x a)
                  (<<-all-l y a)))
  :rule-classes :congruence
  :enable tree-equiv
  :expand ((<<-all-l x a)
           (<<-all-l y a)))

(defrule <<-all-r-when-tree-equiv-congruence
  (implies (tree-equiv x y)
           (equal (<<-all-r a x)
                  (<<-all-r a y)))
  :rule-classes :congruence
  :enable tree-equiv
  :expand ((<<-all-r a x)
           (<<-all-r a y)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule <<-all-l-of-nil
  (<<-all-l nil tree)
  :enable <<-all-l)

(defrule <<-all-r-of-arg1-and-nil
  (<<-all-r tree nil)
  :enable <<-all-r)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled <<-all-l-when-tree-empty-p
  (implies (tree-empty-p tree)
           (<<-all-l tree x))
  :enable <<-all-l)

(defrule <<-all-l-when-tree-empty-p-cheap
  (implies (tree-empty-p tree)
           (<<-all-l tree x))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by <<-all-l-when-tree-empty-p)

(defruled <<-all-r-when-tree-empty-p
  (implies (tree-empty-p tree)
           (<<-all-r x tree))
  :enable <<-all-r)

(defrule <<-all-r-when-tree-empty-p-cheap
  (implies (tree-empty-p tree)
           (<<-all-r x tree))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by <<-all-r-when-tree-empty-p)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled <<-all-l-when-<<-all-r
  (implies (<<-all-r x tree)
           (equal (<<-all-l tree x)
                  (tree-empty-p tree)))
  :induct t
  :enable (<<-all-r
           <<-all-l
           data::<<-rules))

(defruled <<-all-l-when-<<-all-r-forward-chaining
  (implies (<<-all-r x tree)
           (equal (<<-all-l tree x)
                  (tree-empty-p tree)))
  :rule-classes :forward-chaining
  :by <<-all-l-when-<<-all-r)

(defrule <<-all-l-when-<<-all-r-and-not-tree-empty-p-forward-chaining
  (implies (and (<<-all-r x tree)
                (not (tree-empty-p tree)))
           (not (<<-all-l tree x)))
  :rule-classes :forward-chaining
  :enable <<-all-l-when-<<-all-r)

;;;;;;;;;;;;;;;;;;;;

(defruled <<-all-r-when-<<-all-l
  (implies (<<-all-l tree x)
           (equal (<<-all-r x tree)
                  (tree-empty-p tree)))
  :induct t
  :enable (<<-all-l
           <<-all-r
           data::<<-rules))

(defruled <<-all-r-when-<<-all-l-forward-chaining
  (implies (<<-all-l tree x)
           (equal (<<-all-r x tree)
                  (tree-empty-p tree)))
  :rule-classes :forward-chaining
  :by <<-all-r-when-<<-all-l)

(defrule <<-all-r-when-<<-all-l-and-not-tree-empty-p-forward-chaining
  (implies (and (<<-all-l tree x)
                (not (tree-empty-p tree)))
           (not (<<-all-r x tree)))
  :rule-classes :forward-chaining
  :enable <<-all-r-when-<<-all-l)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule tree-empty-p-when-not-<<-all-l-forward-chaining
  (implies (not (<<-all-l tree x))
           (not (tree-empty-p tree)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :enable <<-all-l)

(defrule tree-empty-p-when-not-<<-all-r-forward-chaining
  (implies (not (<<-all-r x tree))
           (not (tree-empty-p tree)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :enable <<-all-r)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule <<-all-l-of-arg1-and-tree->head
  (equal (<<-all-l tree (tagged-element->elem (tree->head tree)))
         (tree-empty-p tree))
  :enable (<<-all-l
           tree->head
           data::<<-rules))

(defrule <<-all-r-of-tree->head
  (equal (<<-all-r (tagged-element->elem (tree->head tree)) tree)
         (tree-empty-p tree))
  :enable (<<-all-r
           tree->head
           data::<<-rules))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled <<-all-l-of-tree->left-when-<<-all-l
  (implies (<<-all-l tree x)
           (<<-all-l (tree->left tree) x))
  :enable <<-all-l)

(defrule <<-all-l-of-tree->left-when-<<-all-l-cheap
  (implies (<<-all-l tree x)
           (<<-all-l (tree->left tree) x))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by <<-all-l-of-tree->left-when-<<-all-l)

(defruled <<-all-l-of-tree->right-when-<<-all-l
  (implies (<<-all-l tree x)
           (<<-all-l (tree->right tree) x))
  :enable <<-all-l)

(defrule <<-all-l-of-tree->right-when-<<-all-l-cheap
  (implies (<<-all-l tree x)
           (<<-all-l (tree->right tree) x))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by <<-all-l-of-tree->right-when-<<-all-l)

;;;;;;;;;;;;;;;;;;;;

(defruled <<-all-r-of-arg1-and-tree->left-when-<<-all-r
  (implies (<<-all-r x tree)
           (<<-all-r x (tree->left tree)))
  :enable <<-all-r)

(defrule <<-all-r-of-arg1-and-tree->left-when-<<-all-r-cheap
  (implies (<<-all-r x tree)
           (<<-all-r x (tree->left tree)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by <<-all-r-of-arg1-and-tree->left-when-<<-all-r)

(defruled <<-all-r-of-arg1-and-tree->right-when-<<-all-r
  (implies (<<-all-r x tree)
           (<<-all-r x (tree->right tree)))
  :enable <<-all-r)

(defrule <<-all-r-of-arg1-and-tree->right-when-<<-all-r-cheap
  (implies (<<-all-r x tree)
           (<<-all-r x (tree->right tree)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by <<-all-r-of-arg1-and-tree->right-when-<<-all-r)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule <<-all-l-of-tree-node
  (equal (<<-all-l (tree-node head left right) x)
         (and (<< (tagged-element->elem head) x)
              (<<-all-l left x)
              (<<-all-l right x)))
  :enable <<-all-l)

(defrule <<-all-r-of-arg1-and-tree-node
  (equal (<<-all-r x (tree-node head left right))
         (and (<< x (tagged-element->elem head))
              (<<-all-r x left)
              (<<-all-r x right)))
  :enable <<-all-r)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled <<-all-l-weaken
  (implies (and (<< x y)
                (<<-all-l tree x))
           (<<-all-l tree y))
  :induct t
  :enable (<<-all-l
           data::<<-rules))

(defruled <<-all-l-weaken2
  (implies (and (not (<< x y))
                (<<-all-l tree y))
           (<<-all-l tree x))
  :enable (<<-all-l-weaken
           data::<<-rules)
  :disable acl2::<<-trichotomy
  :use ((:instance acl2::<<-trichotomy
                   (acl2::x y)
                   (acl2::y x))))

;;;;;;;;;;;;;;;;;;;;

(defruled <<-all-r-weaken
  (implies (and (<< x y)
                (<<-all-r y tree))
           (<<-all-r x tree))
  :induct t
  :enable (<<-all-r
           data::<<-rules))

(defruled <<-all-r-weaken2
  (implies (and (not (<< x y))
                (<<-all-r x tree))
           (<<-all-r y tree))
  :enable (<<-all-r-weaken
           data::<<-rules)
  :disable acl2::<<-trichotomy
  :use ((:instance acl2::<<-trichotomy
                   (acl2::x y)
                   (acl2::y x))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule <<-of-tree->head-when-<<-all-l
  (implies (and (<<-all-l tree x)
                (not (tree-empty-p tree)))
           (<< (tagged-element->elem (tree->head tree)) x))
  :rule-classes ((:rewrite :backchain-limit-lst (0 nil)))
  :enable <<-all-l)

(defrule <<-of-arg1-and-tree->head-when-<<-all-r-arg1
  (implies (and (<<-all-r x tree)
                (not (tree-empty-p tree)))
           (<< x (tagged-element->elem (tree->head tree))))
  :rule-classes ((:rewrite :backchain-limit-lst (0 nil)))
  :enable <<-all-r)

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
           (<<-all-l (tree->left tree)
                       (tagged-element->elem (tree->head tree)))
           (<<-all-r (tagged-element->elem (tree->head tree))
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
                       (<<-all-l (tree->left tree)
                                   (tagged-element->elem (tree->head tree)))
                       (<<-all-r (tagged-element->elem (tree->head tree))
                                   (tree->right tree)))))
  :enable bstp)

(defrule bstp-when-not-tree-empty-p-cheap
  (implies (not (tree-empty-p tree))
           (equal (bstp tree)
                  (and (bstp (tree->left tree))
                       (bstp (tree->right tree))
                       (<<-all-l (tree->left tree)
                                   (tagged-element->elem (tree->head tree)))
                       (<<-all-r (tagged-element->elem (tree->head tree))
                                   (tree->right tree)))))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by bstp-when-not-tree-empty-p)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule bstp-of-tree-node
  (equal (bstp (tree-node head left right))
         (and (bstp left)
              (bstp right)
              (<<-all-l left (tagged-element->elem head))
              (<<-all-r (tagged-element->elem head) right)))
  :enable bstp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled <<-of-tree->head-tree->left-and-tree->head
  (implies (and (bstp tree)
                (not (tree-empty-p (tree->left tree))))
           (<< (tagged-element->elem (tree->head (tree->left tree)))
                 (tagged-element->elem (tree->head tree)))))

(defruled <<-of-tree->head-and-tree->head-tree->right
  (implies (and (bstp tree)
                (not (tree-empty-p (tree->right tree))))
           (<< (tagged-element->elem (tree->head tree))
                 (tagged-element->elem (tree->head (tree->right tree))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule <<-all-l-of-tree->left-and-tree->head-when-bstp
  (implies (bstp set)
           (<<-all-l (tree->left set)
                       (tagged-element->elem (tree->head set)))))

(defrule <<-all-r-of-tree->head-and-tree->right-when-bstp
  (implies (bstp tree)
           (<<-all-r (tagged-element->elem (tree->head tree))
                       (tree->right tree))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthy <<-all-extra-rules
  '(<<-all-l-when-tree-empty-p
    <<-all-r-when-tree-empty-p
    <<-all-l-when-<<-all-r-forward-chaining
    <<-all-r-when-<<-all-l-forward-chaining
    <<-all-l-of-tree->left-when-<<-all-l
    <<-all-l-of-tree->right-when-<<-all-l
    <<-all-r-of-arg1-and-tree->left-when-<<-all-r
    <<-all-r-of-arg1-and-tree->right-when-<<-all-r
    <<-all-l-weaken
    <<-all-l-weaken2
    <<-all-r-weaken
    <<-all-r-weaken2))

(defthy bstp-extra-rules
  '(bstp-of-tree->left-when-tree-orderdp
    bstp-of-tree->right-when-bstp
    bstp-when-tree-empty-p
    bstp-when-not-tree-empty-p
    <<-of-tree->head-tree->left-and-tree->head
    <<-of-tree->head-and-tree->head-tree->right))
