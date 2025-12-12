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
(include-book "internal/union-defs")
(include-book "set-defs")
(include-book "in-defs")
(include-book "subset-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(local (include-book "kestrel/alists-light/assoc-equal" :dir :system))
(local (include-book "kestrel/alists-light/symbol-alistp" :dir :system))

(local (include-book "kestrel/utilities/ordinals" :dir :system))

(local (include-book "std/system/partition-rest-and-keyword-args" :dir :system))

(local (include-book "internal/tree"))
(local (include-book "internal/union"))
(local (include-book "set"))
(local (include-book "cardinality"))
(local (include-book "in"))
(local (include-book "insert"))
(local (include-book "subset"))

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

;; TODO: custom macro for rest + :test keyword argument
(defmacro union (&rest forms)
  (declare (xargs :guard t))
  (union-macro-fn forms))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; (defsection union
;;   :parents (set)
;;   :short "An @($n$)-ary set union."
;;   :long
;;   (xdoc::topstring
;;     (xdoc::p
;;       "Time complexity: @($O(n\\log(m/n))$) (for binary union, where @($n < m$))."))
;;
;;   (define binary-union
;;     ((x setp)
;;      (y setp))
;;     :returns (set setp
;;                   :hints (("Goal" :in-theory (enable setp
;;                                                      fix
;;                                                      empty))))
;;     (tree-union (fix x) (fix y))
;;     :inline t
;;     :guard-hints (("Goal" :in-theory (enable setp))))
;;
;;   ;;;;;;;;;;;;;;;;;;;;
;;
;;   (define union-macro-loop
;;     ((list true-listp))
;;     :guard (and (consp list)
;;                 (consp (rest list)))
;;     (if (endp (rest (rest list)))
;;         (list 'binary-union
;;               (first list)
;;               (second list))
;;       (list 'binary-union
;;             (first list)
;;             (union-macro-loop (rest list))))
;;     :hints (("Goal" :in-theory (enable o< o-finp acl2-count))))
;;
;;   (defmacro union (x y &rest rst)
;;     (declare (xargs :guard t))
;;     (union-macro-loop (list* x y rst)))
;;
;;   (add-macro-fn union binary-union$inline t))

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define union-=
  ((x acl2-number-setp)
   (y acl2-number-setp))
  (mbe :logic (union x y)
       :exec (acl2-number-tree-union x y))
  :enabled t
  :inline t
  :guard-hints (("Goal" :in-theory (enable setp
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
  :guard-hints (("Goal" :in-theory (enable setp
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
  :guard-hints (("Goal" :in-theory (enable setp
                                           set-all-eqlablep
                                           union))))
