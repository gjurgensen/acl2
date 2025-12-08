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
(include-book "internal/bst-defs")
(include-book "internal/heap-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(local (include-book "kestrel/utilities/ordinals" :dir :system))

(local (include-book "internal/tree"))
(local (include-book "internal/bst"))
(local (include-book "internal/heap"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define setp (x)
  :parents (set)
  :short "Recognizer for @(see treeset)s."
  :long
  (xdoc::topstring
   (xdoc::p
     "Time complexity: @($O(n^2)$) (Note: the current implementation is
      inefficient. This should eventually be @($O(n)$) once we introduce a more
      efficient binary search tree property check via an @(tsee mbe).)"))
  :returns (yes/no booleanp :rule-classes (:rewrite :type-prescription))
  (and (treep x)
       (bstp x)
       (heapp x)))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t setp)))

;; Exposes implementation
;; (defrule setp-compound-recognizer
;;   (if (setp set)
;;       (or (consp set)
;;           (equal set nil))
;;     (not (equal set nil)))
;;   :rule-classes :compound-recognizer
;;   :enable setp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define empty ()
  :returns (set setp)
  nil
  :inline t)

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t empty) (:e empty)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define fix ((set setp))
  :parents (set)
  :short "Fixer for @(see treeset)s."
  :returns (set$ setp)
  (mbe :logic (if (setp set)
                  set
                (empty))
       :exec (the list set))
  :inline t
  :guard-hints (("Goal" :in-theory (enable setp))))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t fix)))

(defrule fix-when-setp
  (implies (setp set)
           (equal (fix set)
                  set))
  :enable fix)

(defruled fix-when-not-setp
  (implies (not (setp set))
           (equal (fix set)
                  (empty)))
  :enable fix)

(defrule fix-when-not-setp-cheap
  (implies (not (setp set))
           (equal (fix set)
                  (empty)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by fix-when-not-setp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define equiv
  ((x setp)
   (y setp))
  :parents (set)
  :short "Equivalence up to @(tsee fix)."
  :returns (yes/no booleanp :rule-classes (:rewrite :type-prescription))
  (equal (fix x)
         (fix y))
  :inline t

  ///
  (defequiv equiv))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t equiv)))

(defrule fix-under-equiv
  (equiv (fix set)
         set)
  :enable equiv)

(defrule fix-when-equiv-congruence
  (implies (equiv set0 set1)
           (equal (fix set0)
                  (fix set1)))
  :rule-classes :congruence
  :enable equiv)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define emptyp ((set setp))
  :parents (set)
  :short "Check if a @(see treeset) is empty."
  :returns (yes/no booleanp :rule-classes (:rewrite :type-prescription))
  (tree-empty-p (fix set))
  :inline t
  :guard-hints (("Goal" :in-theory (enable setp))))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t emptyp)))

(defrule emptyp-when-equiv-congruence
  (implies (equiv set0 set1)
           (equal (emptyp set0)
                  (emptyp set1)))
  :rule-classes :congruence
  :enable emptyp)

(defrule emptyp-of-empty
  (emptyp (empty))
  :enable empty)

(defruled fix-when-emptyp
  (implies (emptyp set)
           (equal (fix set)
                  (empty)))
  :enable (emptyp
           fix
           tree-empty-p
           setp
           empty))

(defrule fix-when-emptyp-cheap
  (implies (emptyp set)
           (equal (fix set)
                  (empty)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :enable fix-when-emptyp)

(defrule setp-when-not-emptyp-forward-chaining
  (implies (not (emptyp set))
           (setp set))
  :rule-classes :forward-chaining
  :enable (emptyp
           setp
           empty))

;; TODO: Should this also be a regular rewrite rule?
(defrule emptyp-when-not-setp-forward-chaining
  (implies (not (setp set))
           (emptyp set))
  :rule-classes :forward-chaining)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define head ((set setp))
  :parents (set)
  :short "Get an element of the nonempty @(see treeset)."
  :long
  (xdoc::topstring
   (xdoc::p
     "For empty trees, returns @('nil').")
   (xdoc::p
     "From a user perspective, this should likely be viewed as an arbitrary
      element of the set, to be used only in conjunction with @(tsee left) and
      @(tsee right) to fold over the set. Under the hood, this is the root
      element of the underlying tree, which will be the unique maximum value
      with respect to @(tsee heap<)."))
  :guard (not (emptyp set))
  (tagged-element->elem (tree->head (fix set)))
  :inline t
  :guard-hints (("Goal" :in-theory (enable setp
                                           emptyp))))

;;;;;;;;;;;;;;;;;;;;

(defrule head-when-equiv-congruence
  (implies (equiv set0 set1)
           (equal (head set0)
                  (head set1)))
  :rule-classes :congruence
  :enable head)

(defruled head-when-emptyp
  (implies (emptyp set)
           (equal (head set)
                  nil))
  :enable (head
           emptyp
           irr-tagged-element))

(defrule head-when-emptyp-cheap
  (implies (emptyp set)
           (equal (head set)
                  nil))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :enable head-when-emptyp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define left ((set setp))
  :parents (set)
  :short "Get the \"left\" subset of the nonempty @(see treeset)."
  :long
  (xdoc::topstring
   (xdoc::p
     "For empty sets, returns @('nil').")
   (xdoc::p
     "From a user perspective, this should likely be viewed as an arbitrary
      proper subset excluding the @(tsee head) and disjoint from the @(tsee
      right) subset. Concretely, it is the subset for which all elements are
      @(tsee bst<) the @(tsee head). In terms of the underlying tree
      representation, this is the left subtree."))
  :returns (left setp
                 :hints (("Goal" :in-theory (enable setp
                                                    fix
                                                    empty))))
  (tree->left (fix set))
  :inline t
  :guard-hints (("Goal" :in-theory (enable setp))))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t left)))

;; (defrule left-type-prescription
;;   (setp (left set))
;;   :rule-classes ((:type-prescription :typed-term (left set))))

(defrule left-when-equiv-congruence
  (implies (equiv set0 set1)
           (equal (left set0)
                  (left set1)))
  :rule-classes :congruence
  :enable left)

(defruled left-when-emptyp
  (implies (emptyp set)
           (equal (left set)
                  (empty)))
  :enable (left
           empty))

(defrule left-when-emptyp-cheap
  (implies (emptyp set)
           (equal (left set)
                  (empty)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :enable left-when-emptyp)

(defrule emptyp-when-not-emptyp-of-left-forward-chaining
  (implies (not (emptyp (left set)))
           (not (emptyp set)))
  :rule-classes :forward-chaining)

(defrule equal-of-left-of-arg2-when-setp
  ;; TODO: Does this trigger on the symmetric equality form? I think so.
  (implies (setp x)
           (equal (equal (left x) x)
                  (emptyp x)))
  :enable (left
           emptyp
           setp))

(defrule acl2-count-of-left-linear
  (<= (acl2-count (left set))
      (acl2-count set))
  :rule-classes :linear
  :enable (left
           fix
           empty))

(defrule acl2-count-of-left-when-not-emptyp-linear
  (implies (not (emptyp set))
           (< (acl2-count (left set))
              (acl2-count set)))
  :rule-classes :linear
  :enable (emptyp
           left
           fix
           empty))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define right ((set setp))
  :parents (set)
  :short "Get the \"right\" subset of the nonempty @(see treeset)."
  :long
  (xdoc::topstring
   (xdoc::p
     "For empty sets, returns @('nil').")
   (xdoc::p
     "From a user perspective, this should likely be viewed as an arbitrary
      proper subset excluding the @(tsee head) and disjoint from the @(tsee
      left) subset. Concretely, it is the subset for which the @(tsee head) is
      @(tsee bst<) all elements. In terms of the underlying tree representation,
      this is the right subtree."))
  :returns (right setp
                  :hints (("Goal" :in-theory (enable setp
                                                     fix
                                                     empty))))
  (tree->right (fix set))
  :inline t
  :guard-hints (("Goal" :in-theory (enable setp))))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t right)))

;; (defrule right-type-prescription
;;   (setp (right set))
;;   :rule-classes ((:type-prescription :typed-term (right set))))

(defrule right-when-equiv-congruence
  (implies (equiv set0 set1)
           (equal (right set0)
                  (right set1)))
  :rule-classes :congruence
  :enable right)

(defruled right-when-emptyp
  (implies (emptyp set)
           (equal (right set)
                  (empty)))
  :enable (right
           empty))

(defrule right-when-emptyp-cheap
  (implies (emptyp set)
           (equal (right set)
                  (empty)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :enable right-when-emptyp)

(defrule emptyp-when-not-emptyp-of-right-forward-chaining
  (implies (not (emptyp (right set)))
           (not (emptyp set)))
  :rule-classes :forward-chaining)

(defrule equal-of-right-of-arg2-when-setp
  ;; TODO: Does this trigger on the symmetric equality form? I think so.
  (implies (setp x)
           (equal (equal (right x) x)
                  (emptyp x)))
  :enable (right
           emptyp
           setp))

(defrule acl2-count-of-right-linear
  (<= (acl2-count (right set))
      (acl2-count set))
  :rule-classes :linear
  :enable (right
           fix
           empty))

(defrule acl2-count-of-right-when-not-emptyp-linear
  (implies (not (emptyp set))
           (< (acl2-count (right set))
              (acl2-count set)))
  :rule-classes :linear
  :enable (emptyp
           right
           fix
           empty))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define set-induct (set)
  :parents (set)
  :short "Induct over the structure of a set."
  (or (emptyp set)
      (let ((left (set-induct (left set)))
            (right (set-induct (right set))))
        (declare (ignore left right))
        t))
  :verify-guards nil)

(in-theory (enable (:i set-induct)))

(defruled set-induction
  t
  :rule-classes
  ((:induction :pattern (setp set)
               :scheme (set-induct set))))

(defruled nonempty-set-induction
  t
  :rule-classes
  ((:induction :pattern (not (emptyp set))
               :scheme (set-induct set))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define set-bi-induct (x y)
  :parents (set)
  :short "Induct over the structure of two sets simultaneously."
  (or (emptyp x)
      (emptyp y)
      (let ((left (set-bi-induct (left x) (left y)))
            (right (set-bi-induct (right x) (right y))))
        (declare (ignore left right))
        t))
  :verify-guards nil)

(in-theory (enable (:i set-bi-induct)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; (define to-list
;;   ((set setp))
;;   :returns (list true-listp)
;;   :parents (set)
;;   :short "Create a list of values from a set."
;;   (tree-post-order (fix set))
;;   :guard-hints (("Goal" :in-theory (enable setp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; TODO: theorems
;; - no-duplicatesp
;; - connect member-equal to in under iff
;; - empty to null

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; TODO: to-oset
;; (With the current bst<, this is just an in-order traversal.)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthy set-extra-rules
  '(fix-when-not-setp
    fix-when-emptyp
    head-when-emptyp
    left-when-emptyp
    right-when-emptyp
    set-induction
    nonempty-set-induction))
