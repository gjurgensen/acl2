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
(include-book "internal/diff-defs")
(include-book "set-defs")
(include-book "in-defs")
(include-book "subset-defs")
(include-book "insert-defs")
(include-book "union-defs")
(include-book "to-oset-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(local (include-book "std/osets/top" :dir :system))

(local (include-book "internal/tree"))
(local (include-book "internal/in"))
(local (include-book "internal/diff"))
(local (include-book "internal/in-order"))
(local (include-book "set"))
(local (include-book "cardinality"))
(local (include-book "in"))
(local (include-book "insert"))
(local (include-book "subset"))
(local (include-book "union"))
(local (include-book "extensionality"))
(local (include-book "to-oset"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc diff
  :parents (treeset)
  :short "Set difference on @(see treeset)s."
  :long
  (xdoc::topstring
    (xdoc::p
      "Time complexity: @($O(m\\log(n/m))$) (where @($m < n$)).")
    (xdoc::section
      "General form"
      (xdoc::codeblock
        "(diff x y :test test)")
      (xdoc::desc
        "@(':test') &mdash; optional"
        (xdoc::p
          "One of: @('equal'), @('='), @('eq'), or @('eql'). If no value is
           provided, the default is @('equal'). Specifying an alternative test
           allows for a more performant implementation, at the cost of a
           stronger guard. The guard asserts that the set consists of elements
           suitable for comparison with the specified equality variant.")))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro diff (x y &key (test 'equal))
  (declare (xargs :guard (member-eq test '(equal = eq eql))))
  (case test
    (equal `(diff$inline ,x ,y))
    (=     `(diff-=      ,x ,y))
    (eq    `(diff-eq     ,x ,y))
    (eql   `(diff-eql    ,x ,y))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define diff$inline
  ((x setp)
   (y setp))
  :returns (set setp
                :hints (("Goal" :in-theory (enable setp
                                                   fix
                                                   empty))))
  (tree-diff (fix x) (fix y))
  :guard-hints (("Goal" :in-theory (enable* break-abstraction)))

  ///
  (add-macro-fn diff diff$inline))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t diff)))

(defruled diff-type-prescription
  (or (consp (diff x y))
      (equal (diff x y) nil))
  :rule-classes :type-prescription
  :enable diff)

(add-to-ruleset break-abstraction '(diff-type-prescription))

(defrule diff-when-equiv-of-arg1-congruence
  (implies (equiv x0 x1)
           (equal (diff x0 y)
                  (diff x1 y)))
  :rule-classes :congruence
  :enable diff)

(defrule diff-when-equiv-of-arg2-congruence
  (implies (equiv y0 y1)
           (equal (diff x y0)
                  (diff x y1)))
  :rule-classes :congruence
  :enable diff)

;;;;;;;;;;;;;;;;;;;;

(defrule emptyp-of-diff-when-emptyp-of-arg1
  (implies (emptyp x)
           (emptyp (diff x y)))
  :enable (diff
           emptyp
           fix
           empty))

(defrule emptyp-of-diff-when-tree-emptyp-of-arg2
  (implies (emptyp y)
           (equal (diff x y)
                  (fix x)))
  :enable (diff
           emptyp
           fix
           setp
           empty))

;;;;;;;;;;;;;;;;;;;;

(defrule in-of-diff
  (equal (in a (diff x y))
         (and (in a x)
              (not (in a y))))
  :enable (diff
           in
           fix
           setp
           empty))

;;;;;;;;;;;;;;;;;;;;

(defrule subset-of-diff
  (subset (diff x y) x)
  :enable pick-a-point)

;;;;;;;;;;;;;;;;;;;;

;; TODO: enable in general?
(defruled diff-of-diff-becomes-diff-of-union
  (equal (diff (diff x y) z)
         (diff x (union y z)))
  :enable extensionality)

;;;;;;;;;;;;;;;;;;;;

(defrule oset-difference-of-to-oset
  (equal (set::difference (to-oset x)
                          (to-oset y))
         (to-oset (diff x y)))
  :enable (to-oset
           diff
           fix
           setp
           empty))

(add-to-ruleset from-oset-theory '(oset-difference-of-to-oset))

(defrule from-oset-of-oset-difference
  (equal (from-oset (set::difference x y))
         (diff (from-oset x)
               (from-oset y)))
  :enable extensionality)

(add-to-ruleset from-oset-theory '(from-oset-of-oset-difference))

(defruled oset-difference-becomes-diff
  (equal (set::difference x y)
         (to-oset (diff (from-oset x)
                        (from-oset y))))
  :enable set::expensive-rules)

(add-to-ruleset from-oset-theory '(oset-difference-becomes-diff))

(defruled diff-becomes-oset-difference
  (equal (diff x y)
         (from-oset (set::difference (to-oset x)
                                     (to-oset y)))))

(add-to-ruleset to-oset-theory '(diff-becomes-oset-difference))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define diff-=
  ((x acl2-number-setp)
   (y acl2-number-setp))
  (mbe :logic (diff x y)
       :exec (acl2-number-tree-diff x y))
  :guard-hints (("Goal" :in-theory (enable* break-abstraction
                                            set-all-acl2-numberp
                                            diff))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define diff-eq
  ((x symbol-setp)
   (y symbol-setp))
  (mbe :logic (diff x y)
       :exec (symbol-tree-diff x y))
  :guard-hints (("Goal" :in-theory (enable* break-abstraction
                                            set-all-symbolp
                                            diff))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define diff-eql
  ((x eqlable-setp)
   (y eqlable-setp))
  (mbe :logic (diff x y)
       :exec (eqlable-tree-diff x y))
  :guard-hints (("Goal" :in-theory (enable* break-abstraction
                                            set-all-eqlablep
                                            diff))))
