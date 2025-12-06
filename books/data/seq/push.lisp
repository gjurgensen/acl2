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

(include-book "internal/push-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(local (include-book "seq"))

(local (include-book "internal/ftree"))
(local (include-book "internal/push"))
(local (include-book "internal/well-formed-p"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define push-front
  (a
   (seq seqp))
  :returns (seq$ seqp
                 :hints (("Goal" :in-theory (enable seqp
                                                    seq-fix
                                                    empty))))
  (ftree-push-front a (seq-fix seq))
  :inline t
  :guard-hints (("Goal" :in-theory (enable seqp))))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t push-front)))

(defrule push-front-when-seq-equal-congruence
  (implies (seq-equal seq0 seq1)
           (equal (push-front a seq0)
                  (push-front a seq1)))
  :rule-classes :congruence
  :enable push-front)

(defrule emptyp-of-push-front
  (not (emptyp (push-front a seq)))
  :enable (push-front
           emptyp
           empty
           seq-fix
           seqp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define singleton (a)
  (mbe :logic (push-front a (empty))
       :exec (ftree-single a))
  :enabled nil
  :inline t
  :guard-hints (("Goal" :in-theory (enable push-front
                                           empty
                                           ftree-push-front))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define push-back
  (a
   (seq seqp))
  :returns (seq$ seqp
                 :hints (("Goal" :in-theory (enable seqp
                                                    seq-fix
                                                    empty))))
  (ftree-push-back a (seq-fix seq))
  :inline t
  :guard-hints (("Goal" :in-theory (enable seqp))))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t push-back)))

(defrule push-back-when-seq-equal-congruence
  (implies (seq-equal seq0 seq1)
           (equal (push-back a seq0)
                  (push-back a seq1)))
  :rule-classes :congruence
  :enable push-back)

(defrule emptyp-of-push-back
  (not (emptyp (push-back a seq)))
  :enable (push-back
           emptyp
           empty
           seq-fix
           seqp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define push-list-front
  ((list true-listp)
   (seq seqp))
  :returns (seq$ seqp)
  (if (endp list)
      (seq-fix seq)
    (push-list-front (rest list)
                     (push-front (first list)
                                 seq))))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t push-list-front)))

;; TODO: list-equiv congruence

(defrule push-list-front-when-seq-equal-congruence
  (implies (seq-equal seq0 seq1)
           (equal (push-list-front a seq0)
                  (push-list-front a seq1)))
  :rule-classes :congruence
  :induct t
  :enable push-list-front)

(defrule emptyp-of-push-list-front
  (equal (emptyp (push-list-front list seq))
         (and (not (consp list))
              (emptyp seq)))
  :induct t
  :enable push-list-front)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define push-list-back
  ((list true-listp)
   (seq seqp))
  :returns (seq$ seqp)
  (if (endp list)
      (seq-fix seq)
    (push-list-back (rest list)
                    (push-back (first list)
                               seq))))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t push-list-back)))

;; TODO: list-equiv congruence

(defrule push-list-back-when-seq-equal-congruence
  (implies (seq-equal seq0 seq1)
           (equal (push-list-back a seq0)
                  (push-list-back a seq1)))
  :rule-classes :congruence
  :induct t
  :enable push-list-back)

(defrule emptyp-of-push-list-back
  (equal (emptyp (push-list-back list seq))
         (and (not (consp list))
              (emptyp seq)))
  :induct t
  :enable push-list-back)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define from-list
  ((list true-listp))
  :returns (seq$ seqp)
  (push-list-back list (empty))
  :inline t)

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t from-list)))

;; TODO: list-equiv congruence

(defrule emptyp-of-from-list
  (equal (emptyp (from-list list))
         (not (consp list)))
  :enable from-list)
