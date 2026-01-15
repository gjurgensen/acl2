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

(include-book "data/utilities/oset-defs" :dir :system)

(include-book "internal/tree-defs")
(include-book "internal/in-defs")
(include-book "set-defs")
(include-book "to-oset-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(local (include-book "std/osets/top" :dir :system))

(local (include-book "internal/tree"))
(local (include-book "internal/in"))
(local (include-book "internal/in-order"))
(local (include-book "set"))
(local (include-book "to-oset"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc in
  :parents (treeset)
  :short "Determine if a value is a member of a @(see treeset)."
  :long
  (xdoc::topstring
    (xdoc::p
      "Time complexity: @($O(log(n))$).")
    (xdoc::section
      "General form"
      (xdoc::codeblock
        "(in x set :test test)")
      (xdoc::desc
        "@(':test') &mdash; optional"
        (xdoc::p
          "One of: @('equal'), @('='), @('eq'), or @('eql'). If no value is
           provided, the default is @('equal'). Specifying an alternative test
           allows for a more performant implementation, at the cost of a
           stronger guard. The guard asserts that the set consists of elements
           suitable for comparison with the specified equality variant.")))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro in (x set &key (test 'equal))
  (declare (xargs :guard (member-eq test '(equal = eq eql))))
  (case test
    (equal `(in$inline ,x ,set))
    (=     `(in-=      ,x ,set))
    (eq    `(in-eq     ,x ,set))
    (eql   `(in-eql    ,x ,set))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define in$inline
  (x
   (set setp))
  :returns (yes/no booleanp :rule-classes (:rewrite :type-prescription))
  (mbe :logic (tree-in x (fix set))
       :exec (tree-search-in x set))
  :guard-hints (("Goal" :in-theory (enable* break-abstraction)))

  ///
  (add-macro-fn in in$inline))

;;;;;;;;;;;;;;;;;;;;

(defrule in-when-set-equiv-congruence
  (implies (equiv set0 set1)
           (equal (in x set0)
                  (in x set1)))
  :rule-classes :congruence
  :enable in)

(defruled in-when-emptyp
  (implies (emptyp set)
           (not (in x set)))
  :enable (in
           emptyp))

(defrule in-when-emptyp-cheap
  (implies (emptyp set)
           (not (in x set)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :enable in-when-emptyp)

(defrule in-of-arg1-and-empty
  (not (in x (empty)))
  :enable in-when-emptyp)

(defrule in-of-head
  (equal (in (head set) set)
         (not (emptyp set)))
  :enable (in
           head
           emptyp))

;;;;;;;;;;;;;;;;;;;;

(defrule oset-in-of-to-oset
  (equal (set::in x (to-oset set))
         (in x set))
  :enable (to-oset
           in
           fix
           setp
           empty))

(add-to-ruleset from-oset-theory '(oset-in-of-to-oset))

(defruled in-becomes-oset-in
  (equal (in x set)
         (set::in x (to-oset set))))

(add-to-ruleset to-oset-theory '(in-becomes-oset-in))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled acl2-numberp-when-set-all-acl2-numberp-and-in
  (implies (and (in x set)
                (set-all-acl2-numberp set))
           (acl2-numberp x))
  :enable (in
           set-all-acl2-numberp))

(defrule acl2-numberp-when-set-all-acl2-numberp-and-in-cheap
  (implies (and (in x set)
                (set-all-acl2-numberp set))
           (acl2-numberp x))
  ;; Note: the first hypothesis won't actually backchain, since `set` is free.
  :rule-classes ((:rewrite :backchain-limit-lst (nil 0)))
  :by acl2-numberp-when-set-all-acl2-numberp-and-in)

;;;;;;;;;;;;;;;;;;;;

(defruled symbolp-when-set-all-symbolp-and-in
  (implies (and (in x set)
                (set-all-symbolp set))
           (symbolp x))
  :enable (in
           set-all-symbolp))

(defrule symbolp-when-set-all-symbolp-and-in-cheap
  (implies (and (in x set)
                (set-all-symbolp set))
           (symbolp x))
  ;; Note: the first hypothesis won't actually backchain, since `set` is free.
  :rule-classes ((:rewrite :backchain-limit-lst (nil 0)))
  :by symbolp-when-set-all-symbolp-and-in)

;;;;;;;;;;;;;;;;;;;;

(defruled eqlablep-when-set-all-eqlablep-and-in
  (implies (and (in x set)
                (set-all-eqlablep set))
           (eqlablep x))
  :enable (in
           set-all-eqlablep))

(defrule eqlablep-when-set-all-eqlablep-and-in-cheap
  (implies (and (in x set)
                (set-all-eqlablep set))
           (eqlablep x))
  ;; Note: the first hypothesis won't actually backchain, since `set` is free.
  :rule-classes ((:rewrite :backchain-limit-lst (nil 0)))
  :by eqlablep-when-set-all-eqlablep-and-in)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk set-all-acl2-numberp-sk (set)
  :returns (yes/no booleanp :rule-classes :type-prescription)
  (forall (elem)
          (implies (in elem set)
                   (acl2-numberp elem)))
  :verify-guards nil)

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t set-all-acl2-numberp-sk)))

(defruledl set-all-acl2-numberp-sk-when-set-all-acl2-numberp
  (implies (set-all-acl2-numberp set)
           (set-all-acl2-numberp-sk set))
  :enable set-all-acl2-numberp-sk)

(defrulel set-all-acl2-numberp-sk-of-tree->left
  (implies (and (setp set)
                (set-all-acl2-numberp-sk set))
           (set-all-acl2-numberp-sk (tree->left set)))
  :expand (set-all-acl2-numberp-sk (tree->left set))
  :use (:instance set-all-acl2-numberp-sk-necc
                  (elem (set-all-acl2-numberp-sk-witness (tree->left set))))
  :enable (break-abstraction
           in))

(defrulel set-all-acl2-numberp-sk-of-tree->right
  (implies (and (setp set)
                (set-all-acl2-numberp-sk set))
           (set-all-acl2-numberp-sk (tree->right set)))
  :expand (set-all-acl2-numberp-sk (tree->right set))
  :use (:instance set-all-acl2-numberp-sk-necc
                  (elem (set-all-acl2-numberp-sk-witness (tree->right set))))
  :enable (break-abstraction
           in))

(defrulel tree-all-acl2-numberp-when-set-all-acl2-numberp-sk
  (implies (and (setp set)
                (set-all-acl2-numberp-sk set))
           (tree-all-acl2-numberp set))
  :induct t
  :hints ('(:use (:instance set-all-acl2-numberp-sk-necc
                            (elem (tagged-element->elem (tree->head set))))))
  :enable (tree-all-acl2-numberp
           break-abstraction
           in))

(defruledl set-all-acl2-numberp-when-set-all-acl2-numberp-sk
  (implies (set-all-acl2-numberp-sk set)
           (set-all-acl2-numberp set))
  :enable (set-all-acl2-numberp
           fix
           empty))

(defruled set-all-acl2-numberp-becomes-set-all-acl2-numberp-sk
  (equal (set-all-acl2-numberp set)
         (set-all-acl2-numberp-sk set))
  :use (set-all-acl2-numberp-sk-when-set-all-acl2-numberp
        set-all-acl2-numberp-when-set-all-acl2-numberp-sk))

(defthy set-all-acl2-numberp-pick-a-point
  '(set-all-acl2-numberp-becomes-set-all-acl2-numberp-sk
    set-all-acl2-numberp-sk))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk set-all-symbolp-sk (set)
  :returns (yes/no booleanp :rule-classes :type-prescription)
  (forall (elem)
          (implies (in elem set)
                   (symbolp elem)))
  :verify-guards nil)

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t set-all-symbolp-sk)))

(defruledl set-all-symbolp-sk-when-set-all-symbolp
  (implies (set-all-symbolp set)
           (set-all-symbolp-sk set))
  :enable set-all-symbolp-sk)

(defrulel set-all-symbolp-sk-of-tree->left
  (implies (and (setp set)
                (set-all-symbolp-sk set))
           (set-all-symbolp-sk (tree->left set)))
  :expand (set-all-symbolp-sk (tree->left set))
  :use (:instance set-all-symbolp-sk-necc
                  (elem (set-all-symbolp-sk-witness (tree->left set))))
  :enable (break-abstraction
           in))

(defrulel set-all-symbolp-sk-of-tree->right
  (implies (and (setp set)
                (set-all-symbolp-sk set))
           (set-all-symbolp-sk (tree->right set)))
  :expand (set-all-symbolp-sk (tree->right set))
  :use (:instance set-all-symbolp-sk-necc
                  (elem (set-all-symbolp-sk-witness (tree->right set))))
  :enable (break-abstraction
           in))

(defrulel tree-all-symbolp-when-set-all-symbolp-sk
  (implies (and (setp set)
                (set-all-symbolp-sk set))
           (tree-all-symbolp set))
  :induct t
  :hints ('(:use (:instance set-all-symbolp-sk-necc
                            (elem (tagged-element->elem (tree->head set))))))
  :enable (tree-all-symbolp
           break-abstraction
           in))

(defruledl set-all-symbolp-when-set-all-symbolp-sk
  (implies (set-all-symbolp-sk set)
           (set-all-symbolp set))
  :enable (set-all-symbolp
           fix
           empty))

(defruled set-all-symbolp-becomes-set-all-symbolp-sk
  (equal (set-all-symbolp set)
         (set-all-symbolp-sk set))
  :use (set-all-symbolp-sk-when-set-all-symbolp
        set-all-symbolp-when-set-all-symbolp-sk))

(defthy set-all-symbolp-pick-a-point
  '(set-all-symbolp-becomes-set-all-symbolp-sk
    set-all-symbolp-sk))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk set-all-eqlablep-sk (set)
  :returns (yes/no booleanp :rule-classes :type-prescription)
  (forall (elem)
          (implies (in elem set)
                   (eqlablep elem)))
  :verify-guards nil)

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t set-all-eqlablep-sk)))

(defruledl set-all-eqlablep-sk-when-set-all-eqlablep
  (implies (set-all-eqlablep set)
           (set-all-eqlablep-sk set))
  :enable set-all-eqlablep-sk)

(defrulel set-all-eqlablep-sk-of-tree->left
  (implies (and (setp set)
                (set-all-eqlablep-sk set))
           (set-all-eqlablep-sk (tree->left set)))
  :expand (set-all-eqlablep-sk (tree->left set))
  :use (:instance set-all-eqlablep-sk-necc
                  (elem (set-all-eqlablep-sk-witness (tree->left set))))
  :enable (break-abstraction
           in))

(defrulel set-all-eqlablep-sk-of-tree->right
  (implies (and (setp set)
                (set-all-eqlablep-sk set))
           (set-all-eqlablep-sk (tree->right set)))
  :expand (set-all-eqlablep-sk (tree->right set))
  :use (:instance set-all-eqlablep-sk-necc
                  (elem (set-all-eqlablep-sk-witness (tree->right set))))
  :enable (break-abstraction
           in))

(defrulel tree-all-eqlablep-when-set-all-eqlablep-sk
  (implies (and (setp set)
                (set-all-eqlablep-sk set))
           (tree-all-eqlablep set))
  :induct t
  :hints ('(:use (:instance set-all-eqlablep-sk-necc
                            (elem (tagged-element->elem (tree->head set))))))
  :enable (tree-all-eqlablep
           break-abstraction
           in))

(defruledl set-all-eqlablep-when-set-all-eqlablep-sk
  (implies (set-all-eqlablep-sk set)
           (set-all-eqlablep set))
  :enable (set-all-eqlablep
           fix
           empty))

(defruled set-all-eqlablep-becomes-set-all-eqlablep-sk
  (equal (set-all-eqlablep set)
         (set-all-eqlablep-sk set))
  :use (set-all-eqlablep-sk-when-set-all-eqlablep
        set-all-eqlablep-when-set-all-eqlablep-sk))

(defthy set-all-eqlablep-pick-a-point
  '(set-all-eqlablep-becomes-set-all-eqlablep-sk
    set-all-eqlablep-sk))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define in-=
  ((x acl2-numberp)
   (set acl2-number-setp))
  (mbe :logic (in x set)
       :exec (acl2-number-tree-search-in x set))
  :enabled t
  :inline t
  :guard-hints (("Goal" :in-theory (enable* break-abstraction
                                            set-all-acl2-numberp
                                            in))))

(define in-eq
  ((x symbolp)
   (set symbol-setp))
  (mbe :logic (in x set)
       :exec (symbol-tree-search-in x set))
  :enabled t
  :inline t
  :guard-hints (("Goal" :in-theory (enable* break-abstraction
                                            set-all-symbolp
                                            in))))

(define in-eql
  ((x eqlablep)
   (set eqlable-setp))
  (mbe :logic (in x set)
       :exec (eqlable-tree-search-in x set))
  :enabled t
  :inline t
  :guard-hints (("Goal" :in-theory (enable* break-abstraction
                                            set-all-eqlablep
                                            in))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthy in-extra-rules
  '(in-when-emptyp))
