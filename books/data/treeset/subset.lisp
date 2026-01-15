; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "TREESET")

(include-book "std/util/define" :dir :system)
(include-book "std/util/define-sk" :dir :system)
(include-book "std/util/defrule" :dir :system)
(include-book "xdoc/constructors" :dir :system)

(include-book "internal/subset-defs")
(include-book "set-defs")
(include-book "in-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(local (include-book "kestrel/utilities/ordinals" :dir :system))

(local (include-book "internal/tree"))
(local (include-book "internal/subset"))
(local (include-book "internal/antisymmetry"))
(local (include-book "set"))
(local (include-book "in"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc subset
  :parents (treeset)
  :short "Check if one set is a subset of the other."
  :long
  (xdoc::topstring
    (xdoc::p
      "Time complexity: @($O(n\\log(m))$) (Note: the current implementation is
       slightly inefficient. This should eventually be @($O(n\\log(m/n))$),
       where @($n < m$). This may be implemented similar to @(tsee diff).)")
    (xdoc::section
      "General form"
      (xdoc::codeblock
        "(subset x y :test test)")
      (xdoc::desc
        "@(':test') &mdash; optional"
        (xdoc::p
          "One of: @('equal'), @('='), @('eq'), or @('eql'). If no value is
           provided, the default is @('equal'). Specifying an alternative test
           allows for a more performant implementation, at the cost of a
           stronger guard. The guard asserts that the set consists of elements
           suitable for comparison with the specified equality variant.")))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro subset (x set &key (test 'equal))
  (declare (xargs :guard (member-eq test '(equal = eq eql))))
  (case test
    (equal `(subset$inline ,x ,set))
    (=     `(subset-=      ,x ,set))
    (eq    `(subset-eq     ,x ,set))
    (eql   `(subset-eql    ,x ,set))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define subset$inline
  ((x setp)
   (y setp))
  :returns (yes/no booleanp :rule-classes :type-prescription)
  (tree-subset-p (fix x) (fix y))
  :guard-hints (("Goal" :in-theory (enable* break-abstraction)))

  ///
  (add-macro-fn subset subset$inline))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t subset)))

(defrule subset-when-equiv-of-arg1-congruence
  (implies (equiv x0 x1)
           (equal (subset x0 y)
                  (subset x1 y)))
  :rule-classes :congruence
  :enable subset)

(defrule subset-when-equiv-of-arg2-congruence
  (implies (equiv y0 y1)
           (equal (subset x y0)
                  (subset x y1)))
  :rule-classes :congruence
  :enable subset)

(defrule subset-when-emptyp-of-arg1
  (implies (emptyp x)
           (subset x y))
  :enable (subset
           emptyp
           empty))

(defrule subset-when-emptyp-of-arg2
  (implies (emptyp y)
           (equal (subset x y)
                  (emptyp x)))
  :enable (subset
           emptyp))

;; TODO: disable by default?
(defrule in-when-in-and-subset
  ;; (implies (and (in a x)
  ;;               (subset x y))
  (implies (and (subset x y)
                (in a x))
           (in a y))
  :enable (subset
           in))

;;;;;;;;;;;;;;;;;;;;

(defrule subset-reflexivity
  (subset x x)
  :enable subset)

(defruled subset-antisymmetry
  (implies (and (subset x y)
                (subset y x))
           (equal (fix x) (fix y)))
  :use (:instance tree-subset-p-antisymmetry
                  (x (fix x))
                  (y (fix y)))
  :enable (subset
           fix
           setp
           empty))

(defrule subset-transitivity
  (implies (and (subset x y)
                (subset y z))
           (subset x z))
  :enable subset)

;;;;;;;;;;;;;;;;;;;;

(defruled subset-when-not-in-of-head
  (implies (and (not (emptyp x))
                (not (in (head x) y)))
           (not (subset x y)))
  :enable (subset
           in
           head
           emptyp))

(defrule subset-when-not-in-of-head-cheap
  (implies (and (not (in (head x) y))
                (not (emptyp x)))
           (not (subset x y)))
  :rule-classes ((:rewrite :backchain-limit-lst (0 nil)))
  :by subset-when-not-in-of-head)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection double-containment
  :parents (set)
  :short "Prove set equalities via @(see subset) antisymmetry."
  :long
  (xdoc::topstring
    (xdoc::p
      "This mirrors the @(see set::std/osets) rule, @(see
       set::double-containment). Here, we disable it by default."))

  (defruled equal-becomes-subset-when-setp
    (implies (and (setp x)
                  (setp y))
             (equal (equal x y)
                    (and (subset x y)
                         (subset y x))))
    :use subset-antisymmetry)

  (defruled double-containment
    (implies (and (setp x)
                  (setp y))
             (equal (equal x y)
                    (and (subset x y)
                         (subset y x))))
    :rule-classes ((:rewrite :backchain-limit-lst (1 1)))
    :by equal-becomes-subset-when-setp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk subset-sk (x y)
  :parents (subset)
  :returns (yes/no booleanp :rule-classes :type-prescription)
  (forall (elem)
          (implies (in elem x)
                   (in elem y)))
  :verify-guards nil)

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t subset-sk)))

(defruled subset-sk-becomes-tree-subset-p-sk
  (equal (subset-sk x y)
         (tree-subset-p-sk (fix x) (fix y)))
  :use (subset-sk-becomes-tree-subset-p-sk-lemma0
        subset-sk-becomes-tree-subset-p-sk-lemma1)

  :prep-lemmas
  ((defruled subset-sk-becomes-tree-subset-p-sk-lemma0
     (implies (subset-sk x y)
              (tree-subset-p-sk (fix x) (fix y)))
     :use (:instance subset-sk-necc
                     (elem (tree-subset-p-sk-witness (fix x) (fix y))))
     :enable (tree-subset-p-sk
              in))

   (defruled subset-sk-becomes-tree-subset-p-sk-lemma1
     (implies (tree-subset-p-sk (fix x) (fix y))
              (subset-sk x y))
     :enable (subset-sk
              tree-subset-p-sk-becomes-tree-subset-p
              in))))

(defruled subset-becomes-subset-sk
  (equal (subset x y)
         (subset-sk x y))
  :enable (subset
           subset-sk-becomes-tree-subset-p-sk
           tree-subset-p-sk-becomes-tree-subset-p))

(defruled subset-sk-becomes-subset
  (equal (subset-sk x y)
         (subset x y))
  :by subset-becomes-subset-sk)

(defrule subset-sk-when-equiv-of-arg1-congruence
  (implies (equiv x0 x1)
           (equal (subset-sk x0 y)
                  (subset-sk x1 y)))
  :rule-classes :congruence
  :enable subset-sk-becomes-subset)

(defrule subset-sk-when-equiv-of-arg2-congruence
  (implies (equiv y0 y1)
           (equal (subset-sk x y0)
                  (subset-sk x y1)))
  :rule-classes :congruence
  :enable subset-sk-becomes-subset)

(defthy pick-a-point
  '(subset-becomes-subset-sk
    subset-sk))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define subset-=
  ((x acl2-number-setp)
   (y acl2-number-setp))
  (mbe :logic (subset x y)
       :exec (tree-subset-p x y))
  :enabled t
  :inline t
  :guard-hints (("Goal" :in-theory (enable* break-abstraction
                                            set-all-acl2-numberp
                                            subset))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define subset-eq
  ((x symbol-setp)
   (y symbol-setp))
  (mbe :logic (subset x y)
       :exec (tree-subset-p x y))
  :enabled t
  :inline t
  :guard-hints (("Goal" :in-theory (enable* break-abstraction
                                            set-all-symbolp
                                            subset))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define subset-eql
  ((x eqlable-setp)
   (y eqlable-setp))
  (mbe :logic (subset x y)
       :exec (tree-subset-p x y))
  :enabled t
  :inline t
  :guard-hints (("Goal" :in-theory (enable* break-abstraction
                                            set-all-eqlablep
                                            subset))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthy subset-extra-rules
  '(subset-when-not-in-of-head))
