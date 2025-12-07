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

(include-book "internal/insert-defs")
(include-book "hash-defs")
(include-book "set-defs")
(include-book "cardinality-defs")
(include-book "in-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(local (include-book "kestrel/utilities/ordinals" :dir :system))

(local (include-book "internal/tree"))
(local (include-book "internal/bst-order"))
(local (include-book "internal/bst"))
(local (include-book "internal/heap-order"))
(local (include-book "internal/heap"))
(local (include-book "internal/insert"))
(local (include-book "hash"))
(local (include-book "set"))
(local (include-book "cardinality"))
(local (include-book "in"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; TODO: add option for provided hash
(defsection insert
  :parents (set)
  :short "Add a value (or multiples values) to the set."
  :long
  (xdoc::topstring
    (xdoc::p
      "Time complexity: @($O(\\log(n))$)."))

  (define insert1
    (x
     (set setp))
    :returns (set$ setp
                   :hints (("Goal" :in-theory (enable setp
                                                      fix
                                                      empty))))
    (tree-insert x (hash x) (fix set))
    :inline t
    :guard-hints (("Goal" :in-theory (enable setp))))

  (define insert-macro-loop
    ((list true-listp))
    :guard (and (consp list)
                (consp (rest list)))
    (if (endp (rest (rest list)))
        (list 'insert1
              (first list)
              (second list))
      (list 'insert1
            (first list)
            (insert-macro-loop (rest list))))
    :hints (("Goal" :in-theory (enable acl2-count))))

  (defmacro insert (x y &rest rst)
    (declare (xargs :guard t))
    (insert-macro-loop (list* x y rst)))

  (add-macro-fn insert insert1$inline t))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t insert)))

(defrule insert-when-set-equiv-congruence
  (implies (equiv set0 set1)
           (equal (insert x set0)
                  (insert x set1)))
  :rule-classes :congruence
  :enable insert)

(defrule emptyp-of-insert
  (not (emptyp (insert x set)))
  :enable (emptyp
           insert
           fix
           setp))

;; (defrule insert-type-prescription
;;   (consp (insert x set))
;;   :rule-classes :type-prescription
;;   :disable emptyp-of-insert
;;   :use emptyp-of-insert)

(defrule in-of-insert
  (equal (in x (insert y set))
         (or (equal x y)
             (in x set)))
  :enable (in
           insert
           fix
           setp
           empty))

;; TODO
;; (defrule insert-commutative
;;   (equal (insert y x set)
;;          (insert x y set))
;;   :enable (double-containment
;;            pick-a-point
;;            subset))

;;;;;;;;;;;;;;;;;;;;

(defruled cardinality-of-insert
  (equal (cardinality (insert x set))
         (if (in x set)
             (cardinality set)
           (+ 1 (cardinality set))))
  :enable (cardinality
           insert
           in
           fix
           setp
           empty))

(defrule cardinality-of-insert-when-in
  (implies (in x set)
           (equal (cardinality (insert x set))
                  (cardinality set)))
  :enable cardinality-of-insert)

(defrule cardinality-of-insert-when-not-in
  (implies (not (in x set))
           (equal (cardinality (insert x set))
                  (+ 1 (cardinality set))))
  :enable cardinality-of-insert)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define insert-all
  ((list true-listp)
   (set setp))
  :returns (set$ setp)
  :parents (insert)
  :short "Add a list of values to the set."
  :long
  (xdoc::topstring
   (xdoc::p
     "Time complexity: @($O(n\\log(n+m))$), where @($n$) is the size of the list,
      and @($m$) is the size of the set."))
  (if (endp list)
      (fix set)
    (insert-all (rest list)
                (insert (first list) set))))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t insert-all)))

;; (defrule insert-all-type-prescription
;;   (or (consp (insert-all list set))
;;       (equal (insert-all list set) nil))
;;   :rule-classes :type-prescription
;;   :induct t
;;   :enable (insert-all
;;            sfix))

;; (defrule insert-all-when-consp-of-arg1-type-prescription
;;   (implies (consp list)
;;            (consp (insert-all list set)))
;;   :rule-classes :type-prescription
;;   :induct t
;;   :enable insert-all)

;;;;;;;;;;;;;;;;;;;;

(defrule insert-all-when-set-equiv-congruence
  (implies (equiv set0 set1)
           (equal (insert-all list set0)
                  (insert-all list set1)))
  :rule-classes :congruence
  :induct t
  :enable insert-all)

(defrule emptyp-of-insert-all
  (equal (emptyp (insert-all list set))
         (and (not (consp list))
              (emptyp set)))
  :induct t
  :enable insert-all)

(defrule in-of-insert-all
  (equal (in x (insert-all list set))
         (or (and (member-equal x list) t)
             (in x set)))
  :induct t
  :enable (insert-all
           member-equal)
  :prep-lemmas
  ((defrule in-of-insert-all-when-in
     (implies (in x set)
              (in x (insert-all list set)))
     :induct t
     :enable insert-all)))

;; TODO
;; (defrule insert-all-when-acl2-set-equiv
;;   (implies (acl2::set-equiv x y)
;;            (equal (insert-all x set)
;;                   (insert-all y set)))
;;   :enable (double-containment
;;            pick-a-point
;;            subset))

;; TODO: cardinality

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define from-list
  ((list true-listp))
  :parents (set)
  :short "Create a set from a list of values."
  :long
  (xdoc::topstring
   (xdoc::p
     "This is just a wrapper around @(tsee insert-all).")
   (xdoc::p
     "Time complexity: @($O(n\\log(n))$)."))
  :returns (set$ setp)
  (insert-all list (empty))
  :inline t)

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t from-list)))

(defrule emptyp-of-from-list
  (equal (emptyp (from-list list))
         (not (consp list)))
  :enable from-list)

(defrule in-of-from-list
  (equal (in x (from-list list))
         (and (member-equal x list) t))
  :enable from-list)

;; TODO
;; (defrule from-list-when-acl2-set-equiv
;;   (implies (acl2::set-equiv x y)
;;            (equal (insert-all x)
;;                   (insert-all y)))
;;   :enable from-list)

;; TODO: cardinality
