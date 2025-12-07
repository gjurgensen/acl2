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

(include-book "internal/tree-defs")
(include-book "internal/intersect-defs")
(include-book "set-defs")
(include-book "subset-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(local (include-book "internal/tree"))
(local (include-book "internal/intersect"))
;; (local (include-book "internal/in"))
(local (include-book "set"))
(local (include-book "in"))
(local (include-book "subset"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection intersect
  :parents (set)
  :short "An @($n$)-ary set intersection."
  :long
  (xdoc::topstring
    (xdoc::p
      "Time complexity: @($O(n\\log(m/n))$) (for binary intersection, where @($n < m$))."))

  (define binary-intersect
    ((x setp)
     (y setp))
    :returns (set setp
                  :hints (("Goal" :in-theory (enable setp
                                                     fix
                                                     empty))))
    (tree-intersect (fix x) (fix y))
    :inline t
    :guard-hints (("Goal" :in-theory (enable setp))))

  ;;;;;;;;;;;;;;;;;;;;

  (define intersect-macro-loop
    ((list true-listp))
    :guard (and (consp list)
                (consp (rest list)))
    (if (endp (rest (rest list)))
        (list 'binary-intersect
              (first list)
              (second list))
      (list 'binary-intersect
            (first list)
            (intersect-macro-loop (rest list))))
    :hints (("Goal" :in-theory (enable o< o-finp acl2-count))))

  (defmacro intersect (x y &rest rst)
    (declare (xargs :guard t))
    (intersect-macro-loop (list* x y rst)))

  (add-macro-fn intersect binary-intersect$inline t)

  "@(def intersect)")

;;;;;;;;;;;;;;;;;;;;

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
  :enable (double-containment
           pick-a-point))

(defrule commutativity-of-intersect
  (equal (intersect y x)
         (intersect x y))
  :enable (double-containment
           pick-a-point))
