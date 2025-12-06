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

(local (include-book "kestrel/utilities/ordinals" :dir :system))

;; (local (include-book "internal/bst-order"))
;; (local (include-book "internal/bst"))
;; (local (include-book "internal/heap"))
;; (local (include-book "internal/heap-order"))
(local (include-book "internal/delete"))
(local (include-book "internal/count"))
(local (include-book "internal/in"))
(local (include-book "set"))
(local (include-book "cardinality"))
(local (include-book "in"))
;; TODO
;; (local (include-book "pick-a-point"))
;; (local (include-book "double-containment"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection delete
  :parents (set)
  :short "Remove a value from the set."
  :long
  (xdoc::topstring
    (xdoc::p
      "Time complexity: @($O(\\log(n))$)."))

  (define delete1
    (x
     (set setp))
    ;; (declare (xargs :type-prescription (or (consp (delete1 x set))
    ;;                                        (equal (delete1 x set) nil))))
    :returns (set$ setp
                   :hints (("Goal" :in-theory (enable setp
                                                      fix
                                                      empty))))
    (tree-delete x (fix set))
    :inline t
    :guard-hints (("Goal" :in-theory (enable setp))))

  ;;;;;;;;;;;;;;;;;;;;

  (define delete-macro-loop
    ((list true-listp))
    :guard (and (consp list)
                (consp (rest list)))
    (if (endp (rest (rest list)))
        (list 'delete1
              (first list)
              (second list))
      (list 'delete1
            (first list)
            (delete-macro-loop (rest list))))
    :hints (("Goal" :in-theory (enable acl2-count))))

  (defmacro delete (x y &rest rst)
    (declare (xargs :guard t))
    (delete-macro-loop (list* x y rst)))

  (add-macro-fn delete delete1$inline t))

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
