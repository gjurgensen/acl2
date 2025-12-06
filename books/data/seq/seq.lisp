; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "SEQ")

(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)

(include-book "internal/well-formed-p-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(local (include-book "internal/ftree"))
(local (include-book "internal/well-formed-p"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define seqp (x)
  :returns (yes/no booleanp :rule-classes :type-prescription)
  ;; TODO: optimize by doing both simultaneously
  (and (ftreep x)
       (ftree-well-formed-p 0 x)))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t seqp)))

;; TODO: compound-recognizer, but don't export

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define empty ()
  :returns (seq seqp)
  nil
  :inline t)

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t empty) (:e empty)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; TODO: rename to seq::fix
(define seq-fix ((seq seqp))
  :returns (seq$ seqp)
  (mbe :logic (if (seqp seq)
                  seq
                (empty))
       :exec (the (or cons null) seq))
  :inline t
  :guard-hints (("Goal" :in-theory (enable seqp))))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t seq-fix)))

(defrule seq-fix-when-seqp
  (implies (seqp seq)
           (equal (seq-fix seq)
                  seq))
  :enable seq-fix)

(defruled seq-fix-when-not-seqp
  (implies (not (seqp seq))
           (equal (seq-fix seq)
                  (empty)))
  :enable seq-fix)

(defrule seq-fix-when-not-seqp-cheap
  (implies (not (seqp seq))
           (equal (seq-fix seq)
                  (empty)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by seq-fix-when-not-seqp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; TODO: rename to seq::equal?
;; Note: this is *not* seq- equivalence
(define seq-equal
  ((x seqp)
   (y seqp))
  :returns (yes/no booleanp :rule-classes :type-prescription)
  (mbe :logic (equal (seq-fix x) (seq-fix y))
       :exec (ftree-equal x y))
  :inline t
  :guard-hints (("Goal" :in-theory (enable seqp
                                           ftree-equal))))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t seq-equal)))

(defequiv seq-equal
  :hints (("Goal" :in-theory (enable seq-equal))))

(defrule seq-fix-when-seq-equal-congruence
  (implies (seq-equal seq0 seq1)
           (equal (seq-fix seq0)
                  (seq-fix seq1)))
  :rule-classes :congruence
  :enable seq-equal)

(defrule seq-fix-under-seq-equal
  (seq-equal (seq-fix seq)
             seq)
  :enable seq-equal)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define emptyp ((seq seqp))
  :returns (yes/no booleanp :rule-classes :type-prescription)
  (mbe :logic (equal (seq-fix seq) (empty))
       :exec (ftree-empty-p seq))
  :inline t
  :guard-hints (("Goal" :in-theory (enable seqp
                                           empty
                                           ftree-empty-p))))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t emptyp)))

(defrule emptyp-when-seq-equal-congruence
  (implies (seq-equal seq0 seq1)
           (equal (emptyp seq0)
                  (emptyp seq1)))
  :rule-classes :congruence
  :enable emptyp)

(defrule emptyp-of-empty
  (emptyp (empty))
  :enable (empty
           emptyp))

(defruled emptyp-when-not-seqp
  (implies (not (seqp seq))
           (emptyp seq))
  :enable emptyp)

(defrule emptyp-when-not-seqp-cheap
  (implies (not (seqp seq))
           (emptyp seq))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by emptyp-when-not-seqp)

(defrule emptyp-when-not-seqp-forward-chaining
  (implies (not (seqp seq))
           (emptyp seq))
  :rule-classes :forward-chaining
  :by emptyp-when-not-seqp)

(defruled seqp-when-not-emptyp
  (implies (not (emptyp seq))
           (seqp seq)))

(defrule seqp-when-not-emptyp-forward-chaining
  (implies (not (emptyp seq))
           (seqp seq))
  :rule-classes :forward-chaining
  :by seqp-when-not-emptyp)

(defrule seqp-when-not-emptyp-cheap
  (implies (not (emptyp seq))
           (seqp seq))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by seqp-when-not-emptyp)
