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

(include-book "internal/subset-defs")
(include-book "set-defs")
(include-book "in-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(local (include-book "kestrel/utilities/ordinals" :dir :system))

(local (include-book "internal/tree"))
;; (local (include-book "internal/bst"))
;; (local (include-book "internal/heap"))
;; (local (include-book "internal/in"))
(local (include-book "internal/subset"))
(local (include-book "set"))
(local (include-book "in"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define subset
  ((x setp)
   (y setp))
  :parents (set)
  :short "Check if one set is a subset of the other."
  :long
  (xdoc::topstring
   (xdoc::p
     "Time complexity: @($O(n\\log(m))$) (Note: the current implementation is
      inefficient. This should eventually be @($O(n\\log(m/n))$), where
      @($n < m$). This may be implemented similar to @(tsee diff).)"))
  :returns (yes/no booleanp :rule-classes :type-prescription)
  (tree-subset-p (fix x) (fix y))
  :guard-hints (("Goal" :in-theory (enable setp))))

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

(defruled subset-when-subset-of-arg1-and-left
  (implies (subset x (left y))
           (subset x y))
  :enable (subset
           left
           fix
           empty))

(defrule subset-when-subset-of-arg1-and-left-forward-chaining
  (implies (subset x (left y))
           (subset x y))
  :rule-classes :forward-chaining
  :by subset-when-subset-of-arg1-and-left)

(defruled subset-when-subset-of-arg1-and-right
  (implies (subset x (right y))
           (subset x y))
  :enable (subset
           right
           fix
           empty))

(defrule subset-when-subset-of-arg1-and-right-forward-chaining
  (implies (subset x (right y))
           (subset x y))
  :rule-classes :forward-chaining
  :by subset-when-subset-of-arg1-and-right)

;;;;;;;;;;;;;;;;;;;;

(defruled subset-of-left-when-when-subset
  (implies (subset x y)
           (subset (left x) y))
  :enable (subset
           left
           fix
           empty))

(defrule subset-of-left-when-when-subset-cheap
  (implies (subset x y)
           (subset (left x) y))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by subset-of-left-when-when-subset)

(defruled subset-of-right-when-when-subset
  (implies (subset x y)
           (subset (right x) y))
  :enable (subset
           right
           fix
           empty))

(defrule subset-of-right-when-when-subset-cheap
  (implies (subset x y)
           (subset (right x) y))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by subset-of-right-when-when-subset)

;;;;;;;;;;;;;;;;;;;;

(defrule subset-of-left
  (subset (left x) x)
  :enable (subset
           left
           fix
           empty))

(defrule subset-of-right
  (subset (right x) x)
  :enable (subset
           right
           fix
           empty))

(defrule subset-reflexivity
  (subset x x)
  :enable subset)

;; TODO: antisymmetry

(defrule subset-transitivity
  (implies (and (subset x y)
                (subset y z))
           (subset x z))
  :enable subset)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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

(defthy subset-extra-rules
  '(subset-when-subset-of-arg1-and-left
    subset-when-subset-of-arg1-and-right
    subset-of-left-when-when-subset
    subset-of-right-when-when-subset
    subset-when-not-in-of-head))
