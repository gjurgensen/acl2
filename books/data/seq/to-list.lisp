; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "SEQ")

(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)

(include-book "seq-defs")

(include-book "internal/to-list-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(local (include-book "seq"))

(local (include-book "internal/ftree"))
(local (include-book "internal/to-list"))
(local (include-book "internal/well-formed-p"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define to-list ((seq seqp))
  :returns (list true-listp :rule-classes (:rewrite :type-prescription))
  (ftree-to-list-with-depth 0 (seq-fix seq))
  :inline t
  :guard-hints (("Goal" :in-theory (enable seqp))))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t to-list)))

(defrule to-list-when-seq-equal-congruence
  (implies (seq-equal seq0 seq1)
           (equal (to-list seq0)
                  (to-list seq1)))
  :rule-classes :congruence
  :enable to-list)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; TODO: optimize by not actually constructing the lists.
(define equiv
  ((x seqp)
   (y seqp))
  :returns (yes/no booleanp :rule-classes (:rewrite :type-prescription))
  (data::list-equal (to-list x) (to-list y))
  :inline t)

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t equiv)))

(defrule equiv-when-seq-equal-of-arg1-congruence
  (implies (seq-equal x0 x1)
           (equal (equiv x0 y)
                  (equiv x1 y)))
  :rule-classes :congruence
  :enable equiv)

(defrule equiv-when-seq-equal-of-arg2-congruence
  (implies (seq-equal y0 y1)
           (equal (equiv x y0)
                  (equiv x y1)))
  :rule-classes :congruence
  :enable equiv)

(defequiv equiv
  :hints (("Goal" :in-theory (enable equiv))))

(defrule equiv-when-seq-equal-refinement
  (implies (seq-equal x y)
           (equiv x y))
  :rule-classes :refinement
  :enable equiv)
