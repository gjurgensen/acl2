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

(include-book "internal/count-defs")
(include-book "set-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(local (include-book "kestrel/lists-light/len" :dir :system))

(local (include-book "internal/tree"))
(local (include-book "internal/count"))
(local (include-book "set"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define cardinality ((set setp))
  :parents (set)
  :short "The number of elements in a @(see treeset)."
  :long
  (xdoc::topstring
   (xdoc::p
     "Time complexity: @($O(n)$)."))
  :returns (cardinality natp :rule-classes (:rewrite :type-prescription))
  (tree-nodes-count (fix set))
  :inline t
  :guard-hints (("Goal" :in-theory (enable setp))))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t cardinality)))

(defrule cardinality-when-set-equiv-congruence
  (implies (equiv set0 set1)
           (equal (cardinality set0)
                  (cardinality set1)))
  :rule-classes :congruence
  :enable cardinality)

(defruled equal-of-cardinality-and-0-becomes-emptyp
  (equal (equal (cardinality set)
                0)
         (emptyp set))
  :enable (cardinality
           emptyp))

(defrule cardinality-when-emptyp-forward-chaining
  (implies (emptyp set)
           (equal (cardinality set)
                  0))
  :rule-classes :forward-chaining
  :enable equal-of-cardinality-and-0-becomes-emptyp)

(defrule emptyp-when-equal-cardinality-and-0-forward-chaining
  (implies (equal (cardinality set)
                  0)
           (emptyp set))
  :rule-classes :forward-chaining
  :enable equal-of-cardinality-and-0-becomes-emptyp)
