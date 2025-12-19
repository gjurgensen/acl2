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

(include-book "data/utilities/oset-defs" :dir :system)

(include-book "internal/tree-defs")
(include-book "internal/union-defs")
(include-book "set-defs")
(include-book "in-defs")
(include-book "subset-defs")
(include-book "insert-defs")
(include-book "to-oset-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(local (include-book "std/osets/top" :dir :system))

(local (include-book "kestrel/alists-light/assoc-equal" :dir :system))
(local (include-book "kestrel/alists-light/symbol-alistp" :dir :system))

(local (include-book "kestrel/utilities/ordinals" :dir :system))

(local (include-book "std/system/partition-rest-and-keyword-args" :dir :system))

(local (include-book "internal/tree"))
(local (include-book "internal/union"))
(local (include-book "internal/in-order"))
(local (include-book "set"))
(local (include-book "cardinality"))
(local (include-book "in"))
(local (include-book "insert"))
(local (include-book "subset"))
(local (include-book "to-oset"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc union
  :parents (treeset)
  :short "An @($n$)-ary set union on @(see treeset)s."
  :long
  (xdoc::topstring
    (xdoc::p
      "Time complexity: @($O(n\\log(m/n))$) (for binary union, where
       @($n < m$)).")
    (xdoc::section
      "General form"
      (xdoc::codeblock
        "(union set-0 set-1 ... set-n :test test)")
      (xdoc::desc
        "@(':test') &mdash; optional"
        (xdoc::p
          "One of: @('equal'), @('='), @('eq'), or @('eql'). If no value is
           provided, the default is @('equal'). Specifying an alternative test
           allows for a more performant implementation, at the cost of a
           stronger guard. The guard asserts that the set consists of elements
           suitable for comparison with the specified equality variant.")))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define union-macro-loop
  (union
   (list true-listp))
  :guard (and (consp list)
              (consp (rest list))
              (member-eq union
                         '(union$inline union-= union-eq union-eql)))
  (if (endp (rest (rest list)))
      (list union
            (first list)
            (second list))
    (list union
          (first list)
          (union-macro-loop union (rest list))))
  :hints (("Goal" :in-theory (enable acl2-count))))

(define union-macro-fn
  ((list true-listp))
  (mv-let (erp rest alist)
          (partition-rest-and-keyword-args list '(:test))
    (cond (erp
           (er hard? 'union "Arguments are ill-formed: ~x0" list))
          ((or (not (consp rest))
               (not (consp (rest rest))))
           (er hard? 'union "Too few arguments: ~x0" list))
          (t (let ((test? (assoc-eq :test alist)))
               (if test?
                   (let ((test (cdr test?)))
                     (case test
                       (equal (union-macro-loop 'union$inline rest))
                       (=     (union-macro-loop 'union-=      rest))
                       (eq    (union-macro-loop 'union-eq     rest))
                       (eql   (union-macro-loop 'union-eql    rest))
                       (otherwise
                        (er hard? 'union
                            "Keyword argument :test should have one of the ~
                             following values: equal, =, eq, or eql.~%~
                             Instead, it has value: ~x0" test))))
                 (union-macro-loop 'union$inline rest))))))
  :guard-hints (("Goal" :in-theory (enable acl2::alistp-when-symbol-alistp))))

(defmacro union (&rest forms)
  (declare (xargs :guard t))
  (union-macro-fn forms))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define union$inline
  ((x setp)
   (y setp))
  :returns (set setp
                :hints (("Goal" :in-theory (enable setp
                                                   fix
                                                   empty))))
  (tree-union (fix x) (fix y))
  :guard-hints (("Goal" :in-theory (enable setp))))

(add-macro-fn union union$inline t)

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t union)))

(defruled union-type-prescription
  (or (consp (union x y))
      (equal (union x y) nil))
  :rule-classes :type-prescription
  :enable union)

(add-to-ruleset break-abstraction '(union-type-prescription))

(defrule union-when-equiv-of-arg1-congruence
  (implies (equiv x0 x1)
           (equal (union x0 z)
                  (union x1 z)))
  :rule-classes :congruence
  :enable union)

(defrule union-when-equiv-of-arg2-congruence
  (implies (equiv y0 y1)
           (equal (union x y0)
                  (union x y1)))
  :rule-classes :congruence
  :enable union)

;;;;;;;;;;;;;;;;;;;;

(defrule emptyp-of-union
  (equal (emptyp (union x y))
         (and (emptyp x)
              (emptyp y)))
  :enable (union
           emptyp
           fix
           setp
           empty))

(defrule in-of-union
  (equal (in a (union x y))
         (or (in a x)
             (in a y)))
  :enable (union
           in
           fix
           setp
           empty))

;;;;;;;;;;;;;;;;;;;;

;; TODO: better names?

(defrule subset-of-union-left
  (subset x (union x y))
  :enable (pick-a-point
           subset))

(defrule subset-of-union-right
  (subset x (union y x))
  :enable (pick-a-point
           subset))

;;;;;;;;;;;;;;;;;;;;

(defrule associativity-of-union
  (equal (union (union x y) z)
         (union x y z))
  :enable (double-containment
           pick-a-point
           subset))

(defrule commutativity-of-union
  (equal (union y x)
         (union x y))
  :enable (double-containment
           pick-a-point))

;;;;;;;;;;;;;;;;;;;;

(defrule oset-union-of-to-oset
  (equal (set::union (to-oset x)
                     (to-oset y))
         (to-oset (union x y)))
  :enable (to-oset
           union
           fix
           setp
           empty))

(add-to-ruleset from-oset-theory '(oset-union-of-to-oset))

(defrule from-oset-of-oset-union
  (equal (from-oset (set::union x y))
         (union (from-oset x)
                (from-oset y)))
  :enable (double-containment
           pick-a-point))

(add-to-ruleset from-oset-theory '(from-oset-of-oset-union))

(defruled oset-union-becomes-union
  (equal (set::union x y)
         (to-oset (union (from-oset x)
                         (from-oset y))))
  :enable set::expensive-rules)

(add-to-ruleset from-oset-theory '(oset-union-becomes-union))

(defruled union-becomes-oset-union
  (equal (union x y)
         (from-oset (set::union (to-oset x)
                                (to-oset y)))))

(add-to-ruleset from-oset-theory '(union-becomes-oset-union))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define union-=
  ((x acl2-number-setp)
   (y acl2-number-setp))
  (mbe :logic (union x y)
       :exec (acl2-number-tree-union x y))
  :enabled t
  :inline t
  :guard-hints (("Goal" :in-theory (enable* break-abstraction
                                            set-all-acl2-numberp
                                            union))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define union-eq
  ((x symbol-setp)
   (y symbol-setp))
  (mbe :logic (union x y)
       :exec (symbol-tree-union x y))
  :enabled t
  :inline t
  :guard-hints (("Goal" :in-theory (enable* break-abstraction
                                            set-all-symbolp
                                            union))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define union-eql
  ((x eqlable-setp)
   (y eqlable-setp))
  (mbe :logic (union x y)
       :exec (eqlable-tree-union x y))
  :enabled t
  :inline t
  :guard-hints (("Goal" :in-theory (enable* break-abstraction
                                            set-all-eqlablep
                                            union))))
