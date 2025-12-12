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
(include-book "internal/diff-defs")
(include-book "set-defs")
(include-book "in-defs")
(include-book "subset-defs")
(include-book "union-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(local (include-book "internal/tree"))
(local (include-book "internal/in"))
(local (include-book "internal/diff"))
(local (include-book "set"))
(local (include-book "cardinality"))
(local (include-book "in"))
(local (include-book "insert"))
(local (include-book "subset"))
(local (include-book "union"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro diff (x y &key (test 'equal))
  (declare (xargs :guard (member-eq test '(equal = eq eql))))
  (case test
    (equal `(diff$inline ,x ,y))
    (=     `(diff-=      ,x ,y))
    (eq    `(diff-eq     ,x ,y))
    (eql   `(diff-eql    ,x ,y))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; TODO: doc should be on diff
(define diff$inline
  ((x setp)
   (y setp))
  :parents (set)
  :short "Set difference."
  :long
  (xdoc::topstring
    (xdoc::p
      "Time complexity: @($O(n\\log(m/n))$) (where @($n < m$))."))
  :returns (set setp
                :hints (("Goal" :in-theory (enable setp
                                                   fix
                                                   empty))))
  (tree-diff (fix x) (fix y))
  :guard-hints (("Goal" :in-theory (enable setp)))

  ///
  (add-macro-fn diff diff$inline))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t diff)))

(defrule diff-when-equiv-of-arg1-congruence
  (implies (equiv x0 x1)
           (equal (diff x0 z)
                  (diff x1 z)))
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
  :enable (double-containment
           pick-a-point))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define diff-=
  ((x acl2-number-setp)
   (y acl2-number-setp))
  (mbe :logic (diff x y)
       :exec (acl2-number-tree-diff x y))
  :guard-hints (("Goal" :in-theory (enable setp
                                           set-all-acl2-numberp
                                           diff))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define diff-eq
  ((x symbol-setp)
   (y symbol-setp))
  (mbe :logic (diff x y)
       :exec (symbol-tree-diff x y))
  :guard-hints (("Goal" :in-theory (enable setp
                                           set-all-symbolp
                                           diff))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define diff-eql
  ((x eqlable-setp)
   (y eqlable-setp))
  (mbe :logic (diff x y)
       :exec (eqlable-tree-diff x y))
  :guard-hints (("Goal" :in-theory (enable setp
                                           set-all-eqlablep
                                           diff))))
