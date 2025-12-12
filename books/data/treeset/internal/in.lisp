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

(include-book "tree-defs")
(include-book "bst-defs")
(include-book "heap-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(local (include-book "kestrel/utilities/ordinals" :dir :system))

(local (include-book "tree"))
(local (include-book "bst-order"))
(local (include-book "bst"))
(local (include-book "heap-order"))
(local (include-book "heap"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tree-in
  (x
   (tree treep))
  (declare (xargs :type-prescription (booleanp (tree-in x tree))))
  :parents (implementation)
  :short "Determine if a value appears in the tree."
  :long
  (xdoc::topstring
   (xdoc::p
     "No assumptions are made about the structure of the tree, so this search
      takes linear time. In practice, this function is only used as part of the
      logical definition of @(tsee in) (which is provided a more efficient
      implementation with @(tsee mbe))."))
  (if (tree-empty-p tree)
      nil
    (or (equal x (tagged-element->elem (tree->head tree)))
        (tree-in x (tree->left tree))
        (tree-in x (tree->right tree)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule tree-in-when-tree-equiv-congruence
  (implies (tree-equiv tree0 tree1)
           (equal (tree-in x tree0)
                  (tree-in x tree1)))
  :rule-classes :congruence
  :expand ((tree-in x tree0)
           (tree-in x tree1))
  :enable tree-equiv)

(defrule tree-in-of-tree-node
  (equal (tree-in x (tree-node head left right))
         (or (equal x (tagged-element->elem head))
             (tree-in x left)
             (tree-in x right)))
  :enable tree-in)

(defruled tree-in-when-tree-empty-p
  (implies (tree-empty-p tree)
           (not (tree-in x tree)))
  :enable tree-in)

(defrule tree-in-when-tree-empty-p-cheap
  (implies (tree-empty-p tree)
           (not (tree-in x tree)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by tree-in-when-tree-empty-p)

(defrule tree-in-of-arg1-and-nil
  (not (tree-in x nil))
  :enable tree-in-when-tree-empty-p)

(defruled tree-in-when-tree-empty-p
  (implies (tree-empty-p tree)
           (not (tree-in x tree)))
  :enable tree-in)

(defrule tree-in-when-tree-empty-p-cheap
  (implies (tree-empty-p tree)
           (not (tree-in x tree)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by tree-in-when-tree-empty-p)

(defrule tree-in-of-tree->head
  (equal (tree-in (tagged-element->elem (tree->head tree)) tree)
         (not (tree-empty-p tree))))

(defruled tree-in-when-tree-in-of-tree->left
  (implies (tree-in x (tree->left tree))
           (tree-in x tree))
  :enable tree-in)

(defrule tree-in-when-tree-in-of-tree->left-forward-chaining
  (implies (tree-in x (tree->left tree))
           (tree-in x tree))
  :rule-classes :forward-chaining
  :by tree-in-when-tree-in-of-tree->left)

(defrule tree-in-of-tree->left-when-not-tree-in-cheap
  (implies (not (tree-in x tree))
           (not (tree-in x (tree->left tree))))
  :rule-classes ((:rewrite :backchain-limit-lst (0))))

(defruled tree-in-when-tree-in-of-tree->right
  (implies (tree-in x (tree->right tree))
           (tree-in x tree))
  :enable tree-in)

(defrule tree-in-when-tree-in-of-tree->right-forward-chaining
  (implies (tree-in x (tree->right tree))
           (tree-in x tree))
  :rule-classes :forward-chaining
  :by tree-in-when-tree-in-of-tree->right)

(defrule tree-in-of-tree->right-when-not-tree-in-cheap
  (implies (not (tree-in x tree))
           (not (tree-in x (tree->right tree))))
  :rule-classes ((:rewrite :backchain-limit-lst (0))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled tree-in-when-bst<-all-r
  (implies (bst<-all-r x tree)
           (not (tree-in x tree)))
  :induct t
  :enable (tree-in
           bst<-all-r))

(defrule tree-in-when-bst<-all-r-forward-chaining
  (implies (bst<-all-r x tree)
           (not (tree-in x tree)))
  :rule-classes :forward-chaining
  :by tree-in-when-bst<-all-r)

(defruled tree-in-when-bst<-all-l
  (implies (bst<-all-l tree x)
           (not (tree-in x tree)))
  :induct t
  :enable (tree-in
           bst<-all-l))

(defrule tree-in-when-bst<-all-l-forward-chaining
  (implies (bst<-all-l tree x)
           (not (tree-in x tree)))
  :rule-classes :forward-chaining
  :by tree-in-when-bst<-all-l)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled bst<-when-bst<-all-r-and-tree-in
  (implies (and (bst<-all-r x tree)
                (tree-in y tree))
           (bst< x y))
  :induct t
  :enable tree-in)

(defrule bst<-when-bst<-all-r-and-tree-in-forward-chaining
  (implies (and (bst<-all-r x tree)
                (tree-in y tree))
           (bst< x y))
  :rule-classes :forward-chaining
  :by bst<-when-bst<-all-r-and-tree-in)

(defruled bst<-when-bst<-all-l-and-tree-in
  (implies (and (bst<-all-l tree y)
                (tree-in x tree))
           (bst< x y))
  :induct t
  :enable tree-in)

(defrule bst<-when-bst<-all-l-and-tree-in-forward-chaining
  (implies (and (bst<-all-l tree y)
                (tree-in x tree))
           (bst< x y))
  :rule-classes :forward-chaining
  :by bst<-when-bst<-all-l-and-tree-in)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrulel tree-in-tree->right-when-not-bst<-of-tree->head
  (implies (and (bstp tree)
                (not (tree-empty-p tree))
                (not (bst< (tagged-element->elem (tree->head tree)) x)))
           (not (tree-in x (tree->right tree))))
  :enable tree-in-when-bst<-all-r)

(defrulel tree-in-tree->right-when-not-bst<-of-tree->head-weak
  (implies (and (bstp tree)
                (not (tree-empty-p tree))
                (bst< x (tagged-element->elem (tree->head tree))))
           (not (tree-in x (tree->right tree))))
  :enable bst<-rules)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrulel tree-in-tree->left-when-not->>-of-tree->head
  (implies (and (bstp tree)
                (not (tree-empty-p tree))
                (not (bst< x (tagged-element->elem (tree->head tree)))))
           (not (tree-in x (tree->left tree))))
  :enable tree-in-when-bst<-all-l)

(defrulel tree-in-tree->left-when-not->>-of-tree->head-weak
  (implies (and (bstp tree)
                (not (tree-empty-p tree))
                (bst< (tagged-element->elem (tree->head tree)) x))
           (not (tree-in x (tree->left tree))))
  :enable bst<-rules)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule heap<-of-tree->head-and-arg2-when-tree-in-of-arg2
  (implies (and (heapp tree)
                (tree-in x tree))
           (not (heap< (tagged-element->elem (tree->head tree)) x)))
  :induct (tree-in x tree)
  :enable (tree-in
           heapp
           heap<-rules))

(defrule heap<-of-arg1-and-tree->head-when-tree-in-of-arg1
  (implies (and (heapp tree)
                (tree-in x tree))
           (equal (heap< x (tagged-element->elem (tree->head tree)))
                  (not (equal x (tagged-element->elem (tree->head tree))))))
  :induct (tree-in x tree)
  :enable (tree-in
           heapp
           heap<-rules))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule tree-in-of-tree->head-and-tree->left
  (implies (bstp tree)
           (not (tree-in (tagged-element->elem (tree->head tree))
                         (tree->left tree)))))

(defrule tree-in-of-tree->head-and-tree->right
  (implies (bstp tree)
           (not (tree-in (tagged-element->elem (tree->head tree))
                         (tree->right tree)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled tree->head-when-heapp-and-tree-in-tree->head
  (implies (and (heapp x)
                (heapp y)
                (tree-in (tagged-element->elem (tree->head x)) y)
                (tree-in (tagged-element->elem (tree->head y)) x))
           (equal (tagged-element->elem (tree->head x))
                  (tagged-element->elem (tree->head y))))
  :use ((:instance heap<-of-arg1-and-tree->head-when-tree-in-of-arg1
                   (x (tagged-element->elem (tree->head x)))
                   (tree y))
        (:instance heap<-of-arg1-and-tree->head-when-tree-in-of-arg1
                   (x (tagged-element->elem (tree->head y)))
                   (tree x)))
  :enable heap<-rules
  :disable heap<-of-arg1-and-tree->head-when-tree-in-of-arg1)

(defruled tree->head-when-heapp-and-tree-in-tree->head-syntaxp
  (implies (and (tree-in (tagged-element->elem (tree->head x)) y)
                (syntaxp (<< y x))
                (heapp x)
                (heapp y)
                (tree-in (tagged-element->elem (tree->head y)) x))
           (equal (tagged-element->elem (tree->head x))
                  (tagged-element->elem (tree->head y))))
  :by tree->head-when-heapp-and-tree-in-tree->head)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; TODO: document
(define tree-search-in
  (x
   (tree treep))
  (declare (xargs :type-prescription (booleanp (tree-search-in x tree))))
  (if (tree-empty-p tree)
      nil
    (let ((head-elem (tagged-element->elem (tree->head tree))))
      (or (equal x head-elem)
          (if (bst< x head-elem)
              (tree-search-in x (tree->left tree))
            (tree-search-in x (tree->right tree)))))))

;;;;;;;;;;;;;;;;;;;;

(defrule tree-search-in-when-tree-equiv-congruence
  (implies (tree-equiv tree0 tree1)
           (equal (tree-search-in x tree0)
                  (tree-search-in x tree1)))
  :rule-classes :congruence
  :induct t
  :enable tree-search-in)

(defrule tree-search-in-becomes-tree-in-when
  (implies (bstp tree)
           (equal (tree-search-in x tree)
                  (tree-in x tree)))
  :induct t
  :enable (tree-search-in
           tree-in))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define acl2-number-tree-search-in
  ((x acl2-numberp)
   (tree acl2-number-treep))
  (mbe :logic (tree-search-in x tree)
       :exec (if (tree-empty-p tree)
                 nil
               (let ((head-elem (tagged-element->elem (tree->head tree))))
                 (or (= x head-elem)
                     (if (acl2-number-bst< x head-elem)
                         (acl2-number-tree-search-in x (tree->left tree))
                       (acl2-number-tree-search-in x (tree->right tree)))))))
  :enabled t
  ;; Verified below
  :verify-guards nil)

;;;;;;;;;;;;;;;;;;;;

(defruled tree-search-in-becomes-acl2-number-tree-search-in-exec
  (equal (tree-search-in x tree)
         (if (tree-empty-p tree)
             nil
           (let ((head-elem (tagged-element->elem (tree->head tree))))
             (or (equal x head-elem)
                 (if (bst< x head-elem)
                     (acl2-number-tree-search-in x (tree->left tree))
                   (acl2-number-tree-search-in x (tree->right tree)))))))
  :induct t
  :enable tree-search-in)

(verify-guards acl2-number-tree-search-in
  :hints
  (("Goal" :use tree-search-in-becomes-acl2-number-tree-search-in-exec
           :in-theory (enable tree-all-acl2-numberp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define symbol-tree-search-in
  ((x symbolp)
   (tree symbol-treep))
  (mbe :logic (tree-search-in x tree)
       :exec (if (tree-empty-p tree)
                 nil
               (let ((head-elem (tagged-element->elem (tree->head tree))))
                 (or (eq x head-elem)
                     (if (symbol-bst< x head-elem)
                         (symbol-tree-search-in x (tree->left tree))
                       (symbol-tree-search-in x (tree->right tree)))))))
  :enabled t
  ;; Verified below
  :verify-guards nil)

;;;;;;;;;;;;;;;;;;;;

(defruled tree-search-in-becomes-symbol-tree-search-in-exec
  (equal (tree-search-in x tree)
         (if (tree-empty-p tree)
             nil
           (let ((head-elem (tagged-element->elem (tree->head tree))))
             (or (equal x head-elem)
                 (if (bst< x head-elem)
                     (symbol-tree-search-in x (tree->left tree))
                   (symbol-tree-search-in x (tree->right tree)))))))
  :induct t
  :enable tree-search-in)

(verify-guards symbol-tree-search-in
  :hints
  (("Goal" :use tree-search-in-becomes-symbol-tree-search-in-exec
           :in-theory (enable tree-all-symbolp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define eqlable-tree-search-in
  ((x eqlablep)
   (tree eqlable-treep))
  (mbe :logic (tree-search-in x tree)
       :exec (if (tree-empty-p tree)
                 nil
               (let ((head-elem (tagged-element->elem (tree->head tree))))
                 (or (eql x head-elem)
                     (if (eqlable-bst< x head-elem)
                         (eqlable-tree-search-in x (tree->left tree))
                       (eqlable-tree-search-in x (tree->right tree)))))))
  :enabled t
  ;; Verified below
  :verify-guards nil)

;;;;;;;;;;;;;;;;;;;;

(defruled tree-search-in-becomes-eqlable-tree-search-in-exec
  (equal (tree-search-in x tree)
         (if (tree-empty-p tree)
             nil
           (let ((head-elem (tagged-element->elem (tree->head tree))))
             (or (equal x head-elem)
                 (if (bst< x head-elem)
                     (eqlable-tree-search-in x (tree->left tree))
                   (eqlable-tree-search-in x (tree->right tree)))))))
  :induct t
  :enable tree-search-in)

(verify-guards eqlable-tree-search-in
  :hints
  (("Goal" :use tree-search-in-becomes-eqlable-tree-search-in-exec
           :in-theory (enable tree-all-eqlablep))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthy tree-in-extra-rules
  '(tree-in-when-tree-empty-p
    tree-in-when-tree-in-of-tree->left
    tree-in-when-tree-in-of-tree->right
    tree-in-when-bst<-all-r
    tree-in-when-bst<-all-l

    ;; TODO: should these also be in bst<-all rules? (would require defruleset)
    bst<-when-bst<-all-r-and-tree-in
    bst<-when-bst<-all-l-and-tree-in

    tree->head-when-heapp-and-tree-in-tree->head-syntaxp))
