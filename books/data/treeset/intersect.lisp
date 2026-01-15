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
(include-book "internal/intersect-defs")
(include-book "set-defs")
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
(local (include-book "internal/intersect"))
(local (include-book "internal/in"))
(local (include-book "internal/in-order"))
(local (include-book "set"))
(local (include-book "in"))
(local (include-book "subset"))
(local (include-book "insert"))
(local (include-book "extensionality"))
(local (include-book "to-oset"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc intersect
  :parents (treeset)
  :short "An @($n$)-ary set intersection on @(see treeset)s."
  :long
  (xdoc::topstring
    (xdoc::p
      "Time complexity: @($O(m\\log(n/m))$) (for binary intersection, where
       @($m < n$)).")
    (xdoc::section
      "General form"
      (xdoc::codeblock
        "(intersect set-0 set-1 ... set-n :test test)")
      (xdoc::desc
        "@(':test') &mdash; optional"
        (xdoc::p
          "One of: @('equal'), @('='), @('eq'), or @('eql'). If no value is
           provided, the default is @('equal'). Specifying an alternative test
           allows for a more performant implementation, at the cost of a
           stronger guard. The guard asserts that the set consists of elements
           suitable for comparison with the specified equality variant.")))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define intersect-macro-loop
  (intersect
   (list true-listp))
  :guard (and (consp list)
              (consp (rest list))
              (member-eq intersect
                         '(intersect$inline intersect-= intersect-eq
                           intersect-eql)))
  (if (endp (rest (rest list)))
      (list intersect
            (first list)
            (second list))
    (list intersect
          (first list)
          (intersect-macro-loop intersect (rest list))))
  :hints (("Goal" :in-theory (enable acl2-count))))

(define intersect-macro-fn
  ((list true-listp))
  (mv-let (erp rest alist)
          (partition-rest-and-keyword-args list '(:test))
    (cond (erp
           (er hard? 'intersect "Arguments are ill-formed: ~x0" list))
          ((or (not (consp rest))
               (not (consp (rest rest))))
           (er hard? 'intersect "Too few arguments: ~x0" list))
          (t (let ((test? (assoc-eq :test alist)))
               (if test?
                   (let ((test (cdr test?)))
                     (case test
                       (equal (intersect-macro-loop 'intersect$inline rest))
                       (=     (intersect-macro-loop 'intersect-=      rest))
                       (eq    (intersect-macro-loop 'intersect-eq     rest))
                       (eql   (intersect-macro-loop 'intersect-eql    rest))
                       (otherwise
                        (er hard? 'intersect
                            "Keyword argument :test should have one of the ~
                             following values: equal, =, eq, or eql.~%~
                             Instead, it has value: ~x0" test))))
                 (intersect-macro-loop 'intersect$inline rest))))))
  :guard-hints (("Goal" :in-theory (enable acl2::alistp-when-symbol-alistp))))

(defmacro intersect (&rest forms)
  (declare (xargs :guard t))
  (intersect-macro-fn forms))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define intersect$inline
  ((x setp)
   (y setp))
  :returns (set setp
                :hints (("Goal" :in-theory (enable setp
                                                   fix
                                                   empty))))
  (tree-intersect (fix x) (fix y))
  :guard-hints (("Goal" :in-theory (enable* break-abstraction)))

  ///
  (add-macro-fn intersect intersect$inline t))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t intersect)))

(defruled intersect-type-prescription
  (or (consp (intersect x y))
      (equal (intersect x y) nil))
  :rule-classes :type-prescription
  :enable intersect)

(add-to-ruleset break-abstraction '(intersect-type-prescription))

(defrule intersect-when-set-equiv-of-arg1-congruence
  (implies (equiv x0 x1)
           (equal (intersect x0 z)
                  (intersect x1 z)))
  :rule-classes :congruence
  :enable intersect)

(defrule intersect-when-set-equiv-of-arg2-congruence
  (implies (equiv y0 y1)
           (equal (intersect x y0)
                  (intersect x y1)))
  :rule-classes :congruence
  :enable intersect)

;;;;;;;;;;;;;;;;;;;;

(defrule emptyp-of-intersect-when-emptyp-of-arg1
  (implies (emptyp x)
           (emptyp (intersect x y)))
  :enable (emptyp
           intersect
           fix
           empty))

(defrule emptyp-of-intersect-when-emptyp-of-arg2
  (implies (emptyp y)
           (emptyp (intersect x y)))
  :enable (emptyp
           intersect
           fix
           empty))

(defrule in-of-intersect
  (equal (in a (intersect x y))
         (and (in a x)
              (in a y)))
  :enable (intersect
           in
           fix
           empty
           setp))

;;;;;;;;;;;;;;;;;;;;

;; TODO: better names?

(defrule subset-of-intersect-left
  (subset (intersect x y) x)
  :enable pick-a-point)

(defrule subset-of-intersect-right
  (subset (intersect x y) y)
  :enable pick-a-point)

;;;;;;;;;;;;;;;;;;;;

(defrule associativity-of-intersect
  (equal (intersect (intersect x y) z)
         (intersect x y z))
  :enable extensionality)

(defrule commutativity-of-intersect
  (equal (intersect y x)
         (intersect x y))
  :enable extensionality)

;;;;;;;;;;;;;;;;;;;;

(defrule oset-intersect-of-to-oset
  (equal (set::intersect (to-oset x)
                         (to-oset y))
         (to-oset (intersect x y)))
  :enable (to-oset
           intersect
           fix
           setp
           empty))

(add-to-ruleset from-oset-theory '(oset-intersect-of-to-oset))

(defrule from-oset-of-oset-intersect
  (equal (from-oset (set::intersect x y))
         (intersect (from-oset x)
                    (from-oset y)))
  :enable extensionality)

(add-to-ruleset from-oset-theory '(from-oset-of-oset-intersect))

(defruled oset-intersect-becomes-intersect
  (equal (set::intersect x y)
         (to-oset (intersect (from-oset x)
                             (from-oset y))))
  :enable set::expensive-rules)

(add-to-ruleset from-oset-theory '(oset-intersect-becomes-intersect))

(defruled intersect-becomes-oset-intersect
  (equal (intersect x y)
         (from-oset (set::intersect (to-oset x)
                                    (to-oset y)))))

(add-to-ruleset to-oset-theory '(intersect-becomes-oset-intersect))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define intersect-=
  ((x acl2-number-setp)
   (y acl2-number-setp))
  (mbe :logic (intersect x y)
       :exec (acl2-number-tree-intersect x y))
  :enabled t
  :inline t
  :guard-hints (("Goal" :in-theory (enable* break-abstraction
                                            set-all-acl2-numberp
                                            intersect))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define intersect-eq
  ((x symbol-setp)
   (y symbol-setp))
  (mbe :logic (intersect x y)
       :exec (symbol-tree-intersect x y))
  :enabled t
  :inline t
  :guard-hints (("Goal" :in-theory (enable* break-abstraction
                                            set-all-symbolp
                                            intersect))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define intersect-eql
  ((x eqlable-setp)
   (y eqlable-setp))
  (mbe :logic (intersect x y)
       :exec (eqlable-tree-intersect x y))
  :enabled t
  :inline t
  :guard-hints (("Goal" :in-theory (enable* break-abstraction
                                            set-all-eqlablep
                                            intersect))))
