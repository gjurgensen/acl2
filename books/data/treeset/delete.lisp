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

(include-book "internal/delete-defs")
(include-book "set-defs")
(include-book "cardinality-defs")
(include-book "in-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(local (include-book "kestrel/alists-light/assoc-equal" :dir :system))
(local (include-book "kestrel/alists-light/symbol-alistp" :dir :system))

(local (include-book "kestrel/utilities/ordinals" :dir :system))

(local (include-book "std/system/partition-rest-and-keyword-args" :dir :system))

(local (include-book "internal/delete"))
(local (include-book "internal/count"))
(local (include-book "internal/in"))
(local (include-book "set"))
(local (include-book "cardinality"))
(local (include-book "in"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define delete-macro-loop
  (delete
   (list true-listp))
  :guard (and (consp list)
              (consp (rest list))
              (member-eq delete
                         '(delete$inline delete-= delete-eq delete-eql)))
  (if (endp (rest (rest list)))
      (list delete
            (first list)
            (second list))
    (list delete
          (first list)
          (delete-macro-loop delete (rest list))))
  :hints (("Goal" :in-theory (enable acl2-count))))

(define delete-macro-fn
  ((list true-listp))
  (mv-let (erp rest alist)
          (partition-rest-and-keyword-args list '(:test))
    (cond (erp
           (er hard? 'delete "Arguments are ill-formed: ~x0" list))
          ((or (not (consp rest))
               (not (consp (rest rest))))
           (er hard? 'delete "Too few arguments: ~x0" list))
          (t (let ((test? (assoc-eq :test alist)))
               (if test?
                   (let ((test (cdr test?)))
                     (case test
                       (equal (delete-macro-loop 'delete$inline rest))
                       (= (delete-macro-loop 'delete-= rest))
                       (eq (delete-macro-loop 'delete-eq rest))
                       (eql (delete-macro-loop 'delete-eql rest))
                       (otherwise
                        (er hard? 'delete
                            "Keyword argument :test should have one of the ~
                             following values: equal, =, eq, or eql.~%~
                             Instead, it has value: ~x0" test))))
                 (delete-macro-loop 'delete$inline rest))))))
  :guard-hints (("Goal" :in-theory (enable acl2::alistp-when-symbol-alistp))))

;; TODO: custom macro for rest + :test keyword argument
(defmacro delete (&rest forms)
  (declare (xargs :guard t))
  (delete-macro-fn forms))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; (defsection delete
;;   :parents (set)
;;   :short "Remove a value from the set."
;;   :long
;;   (xdoc::topstring
;;     (xdoc::p
;;       "Time complexity: @($O(\\log(n))$)."))
;;
;;   (define delete1
;;     (x
;;      (set setp))
;;     ;; (declare (xargs :type-prescription (or (consp (delete1 x set))
;;     ;;                                        (equal (delete1 x set) nil))))
;;     :returns (set$ setp
;;                    :hints (("Goal" :in-theory (enable setp
;;                                                       fix
;;                                                       empty))))
;;     (tree-delete x (fix set))
;;     :inline t
;;     :guard-hints (("Goal" :in-theory (enable setp))))
;;
;;   ;;;;;;;;;;;;;;;;;;;;
;;
;;   (define delete-macro-loop
;;     ((list true-listp))
;;     :guard (and (consp list)
;;                 (consp (rest list)))
;;     (if (endp (rest (rest list)))
;;         (list 'delete1
;;               (first list)
;;               (second list))
;;       (list 'delete1
;;             (first list)
;;             (delete-macro-loop (rest list))))
;;     :hints (("Goal" :in-theory (enable acl2-count))))
;;
;;   (defmacro delete (x y &rest rst)
;;     (declare (xargs :guard t))
;;     (delete-macro-loop (list* x y rst)))
;;
;;   (add-macro-fn delete delete1$inline t))

(define delete$inline
  (x
   (set setp))
  :returns (set$ setp
                 :hints (("Goal" :in-theory (enable setp
                                                    fix
                                                    empty))))
  (tree-delete x (fix set))
  :guard-hints (("Goal" :in-theory (enable setp)))

  ///
  (add-macro-fn delete delete$inline t))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t delete)))

(defrule delete-when-set-equiv-congruence
  (implies (equiv set0 set1)
           (equal (delete x set0)
                  (delete x set1)))
  :rule-classes :congruence
  :enable delete)

;; TODO: remove/localize after introduction of more general rule
(defrule emptyp-of-delete-when-emptyp
  (implies (emptyp set)
           (emptyp (delete x set)))
  :enable (emptyp
           delete
           fix
           empty))

(defrule in-of-delete
  (equal (in x (delete y set))
         (and (not (equal x y))
              (in x set)))
  :enable (in
           delete
           fix
           setp
           empty))

;; TODO
;; (defrule delete-commutative
;;   (equal (delete y x set)
;;          (delete x y set))
;;   :enable (double-containment
;;            pick-a-point
;;            subset))

;; TODO
;; (include-book "insert")
;; (defrule emptyp-of-delete
;;   (equal (emptyp (delete x set))
;;          (or (emptyp set)
;;              (equal set (insert x set))))
;;   :enable (double-containment
;;            pick-a-point
;;            subset))

;;;;;;;;;;;;;;;;;;;;

(defruled cardinality-of-delete
  (equal (cardinality (delete x set))
         (if (in x set)
             (- (cardinality set) 1)
           (cardinality set)))
  :enable (cardinality
           delete
           in
           fix
           setp
           empty))

(defrule cardinality-of-delete-when-in
  (implies (in x set)
           (equal (cardinality (delete x set))
                  (- (cardinality set) 1)))
  :use cardinality-of-delete)

(defrule cardinality-of-delete-when-not-in
  (implies (not (in x set))
           (equal (cardinality (delete x set))
                  (cardinality set)))
  :use cardinality-of-delete)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define delete-=
  ((x acl2-numberp)
   (set acl2-number-setp))
  (mbe :logic (delete x set)
       :exec (acl2-number-tree-delete x (fix set)))
  :enabled t
  :inline t
  :guard-hints (("Goal" :in-theory (enable delete
                                           setp
                                           set-all-acl2-numberp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define delete-eq
  ((x symbolp)
   (set symbol-setp))
  (mbe :logic (delete x set)
       :exec (symbol-tree-delete x (fix set)))
  :enabled t
  :inline t
  :guard-hints (("Goal" :in-theory (enable delete
                                           setp
                                           set-all-symbolp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define delete-eql
  ((x eqlablep)
   (set eqlable-setp))
  (mbe :logic (delete x set)
       :exec (eqlable-tree-delete x (fix set)))
  :enabled t
  :inline t
  :guard-hints (("Goal" :in-theory (enable delete
                                           setp
                                           set-all-eqlablep))))
