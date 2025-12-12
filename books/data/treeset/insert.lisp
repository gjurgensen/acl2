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
(include-book "data/utilities/oset-defs" :dir :system)

(include-book "internal/insert-defs")
(include-book "hash-defs")
(include-book "set-defs")
(include-book "cardinality-defs")
(include-book "in-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(local (include-book "data/utilities/fixed-size-words/u32" :dir :system))

(local (include-book "kestrel/alists-light/assoc-equal" :dir :system))
(local (include-book "kestrel/alists-light/symbol-alistp" :dir :system))

(local (include-book "kestrel/utilities/ordinals" :dir :system))

(local (include-book "std/osets/top" :dir :system))
(local (include-book "std/system/partition-rest-and-keyword-args" :dir :system))

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
(local (include-book "subset"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define insert-macro-loop
  (insert
   (list true-listp))
  :guard (and (consp list)
              (consp (rest list))
              (member-eq insert
                         '(insert$inline insert-= insert-eq insert-eql)))
  (if (endp (rest (rest list)))
      (list insert
            (first list)
            (second list))
    (list insert
          (first list)
          (insert-macro-loop insert (rest list))))
  :hints (("Goal" :in-theory (enable acl2-count))))

(define insert-macro-fn
  ((list true-listp))
  (mv-let (erp rest alist)
          (partition-rest-and-keyword-args list '(:test))
    (cond (erp
           (er hard? 'insert "Arguments are ill-formed: ~x0" list))
          ((or (not (consp rest))
               (not (consp (rest rest))))
           (er hard? 'insert "Too few arguments: ~x0" list))
          (t (let ((test? (assoc-eq :test alist)))
               (if test?
                   (let ((test (cdr test?)))
                     (case test
                       (equal (insert-macro-loop 'insert$inline rest))
                       (= (insert-macro-loop 'insert-= rest))
                       (eq (insert-macro-loop 'insert-eq rest))
                       (eql (insert-macro-loop 'insert-eql rest))
                       (otherwise
                        (er hard? 'insert
                            "Keyword argument :test should have one of the ~
                             following values: equal, =, eq, or eql.~%~
                             Instead, it has value: ~x0" test))))
                 (insert-macro-loop 'insert$inline rest))))))
  :guard-hints (("Goal" :in-theory (enable acl2::alistp-when-symbol-alistp))))

;; TODO: custom macro for rest + :test keyword argument
(defmacro insert (&rest forms)
  (declare (xargs :guard t))
  (insert-macro-fn forms))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; TODO: add back this topic

;; (defsection insert
;;   :parents (set)
;;   :short "Add a value (or multiples values) to the set."
;;   :long
;;   (xdoc::topstring
;;     (xdoc::p
;;       "Time complexity: @($O(\\log(n))$)."))
;;
;;   (define insert-macro-loop
;;     ((list true-listp))
;;     :guard (and (consp list)
;;                 (consp (rest list)))
;;     (if (endp (rest (rest list)))
;;         (list 'insert1
;;               (first list)
;;               (second list))
;;       (list 'insert1
;;             (first list)
;;             (insert-macro-loop (rest list))))
;;     :hints (("Goal" :in-theory (enable acl2-count))))
;;
;;   ;; TODO: custom macro for rest + :test keyword argument
;;   (defmacro insert (x y &rest rst)
;;     (declare (xargs :guard t))
;;     (insert-macro-loop (list* x y rst)))
;;
;;   (add-macro-fn insert insert1$inline t))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Note: we don't want to use define's `:inline t` feature here, because that
;; would introduce a macro alias attached to insert$inline that will conflict
;; with the one we wish to provide.
(define insert$inline
  (x
   (set setp))
  :returns (set$ setp
                 :hints (("Goal" :in-theory (enable setp
                                                    fix
                                                    empty))))
  (tree-insert x (hash x) (fix set))
  :guard-hints (("Goal" :in-theory (enable setp)))

  ///
  (add-macro-fn insert insert$inline t))

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

(defrule insert-commutative
  (equal (insert y x set)
         (insert x y set))
  :enable (double-containment
           pick-a-point))

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define from-oset ((oset set::setp))
  (from-list (set::sfix oset)))

;; TODO

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define insert-=
  ((x acl2-numberp)
   (set acl2-number-setp))
  (mbe :logic (insert x set)
       :exec (acl2-number-tree-insert x (hash x) (fix set)))
  :enabled t
  :inline t
  :guard-hints (("Goal" :in-theory (enable setp
                                           set-all-acl2-numberp
                                           insert))))

(define insert-eq
  ((x symbolp)
   (set symbol-setp))
  (mbe :logic (insert x set)
       :exec (symbol-tree-insert x (hash x) (fix set)))
  :enabled t
  :inline t
  :guard-hints (("Goal" :in-theory (enable setp
                                           set-all-symbolp
                                           insert))))
(define insert-eql
  ((x eqlablep)
   (set eqlable-setp))
  (mbe :logic (insert x set)
       :exec (eqlable-tree-insert x (hash x) (fix set)))
  :enabled t
  :inline t
  :guard-hints (("Goal" :in-theory (enable setp
                                           set-all-eqlablep
                                           insert))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define insert-with-hash
  (x
   (hash (unsigned-byte-p 32 hash))
   (set setp))
  :guard (mbe :logic (equal (hash x) hash)
              :exec (data::u32-equal (hash x) hash))
  (mbe :logic (insert x set)
       :exec (tree-insert x hash set))
  :enabled t
  :inline t
  :guard-hints (("Goal" :in-theory (enable data::u32-equal
                                           setp
                                           insert))))
