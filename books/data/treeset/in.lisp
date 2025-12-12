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
(include-book "internal/in-defs")
(include-book "set-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(local (include-book "internal/tree"))
(local (include-book "internal/in"))
(local (include-book "set"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro in (x set &key (test 'equal))
  (declare (xargs :guard (member-eq test '(equal = eq eql))))
  (case test
    (equal `(in$inline ,x ,set))
    (=     `(in-=      ,x ,set))
    (eq    `(in-eq     ,x ,set))
    (eql   `(in-eql    ,x ,set))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; TODO: this documentation should be on in, not in$inline
(define in$inline
  (x
   (set setp))
  :parents (set)
  :short "Determine if a value is a member of the @(see treeset)."
  :long
  (xdoc::topstring
   (xdoc::p
     "Time complexity: @($O(log(n))$)."))
  :returns (yes/no booleanp :rule-classes (:rewrite :type-prescription))
  (mbe :logic (tree-in x (fix set))
       :exec (tree-search-in x set))
  :guard-hints (("Goal" :in-theory (enable setp)))

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

(defruled in-when-in-of-left
  (implies (in x (left set))
           (in x set))
  :enable (in
           left
           fix
           empty))

(defrule in-when-in-of-left-forward-chaining
  (implies (in x (left set))
           (in x set))
  :rule-classes :forward-chaining
  :enable in-when-in-of-left)

(defrule in-of-left-when-not-in-cheap
  (implies (not (in x set))
           (not (in x (left set))))
  :rule-classes ((:rewrite :backchain-limit-lst (0))))

(defruled in-when-in-of-right
  (implies (in x (right set))
           (in x set))
  :enable (in
           right
           fix
           empty))

(defrule in-when-in-of-right-forward-chaining
  (implies (in x (right set))
           (in x set))
  :rule-classes :forward-chaining
  :enable in-when-in-of-right)

(defrule in-of-right-when-not-in-cheap
  (implies (not (in x set))
           (not (in x (right set))))
  :rule-classes ((:rewrite :backchain-limit-lst (0))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule in-of-head-and-left
  (not (in (head set) (left set)))
  :enable (in
           head
           left
           fix
           setp
           empty))

(defrule in-of-head-and-right
  (not (in (head set) (right set)))
  :enable (in
           head
           right
           fix
           setp
           empty))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define in-=
  ((x acl2-numberp)
   (set acl2-number-setp))
  (mbe :logic (in x set)
       :exec (acl2-number-tree-search-in x set))
  :enabled t
  :inline t
  :guard-hints (("Goal" :in-theory (enable setp
                                           set-all-acl2-numberp
                                           in))))

(define in-eq
  ((x symbolp)
   (set symbol-setp))
  (mbe :logic (in x set)
       :exec (symbol-tree-search-in x set))
  :enabled t
  :inline t
  :guard-hints (("Goal" :in-theory (enable setp
                                           set-all-symbolp
                                           in))))

(define in-eql
  ((x eqlablep)
   (set eqlable-setp))
  (mbe :logic (in x set)
       :exec (eqlable-tree-search-in x set))
  :enabled t
  :inline t
  :guard-hints (("Goal" :in-theory (enable setp
                                           set-all-eqlablep
                                           in))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthy in-extra-rules
  '(in-when-emptyp
    in-when-in-of-left
    in-when-in-of-right))
