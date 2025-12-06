; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "SEQ")

(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)

(include-book "data/utilities/nat-defs" :dir :system)

(include-book "ftree-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(local (include-book "data/utilities/nat" :dir :system))
(local (include-book "kestrel/arithmetic-light/fix" :dir :system))
(local (include-book "kestrel/utilities/ordinals" :dir :system))

(local (include-book "ftree"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define elem-depth-p
  ((depth natp)
   elem)
  (declare (xargs :split-types t)
           (type unsigned-byte depth))
  :returns (yes/no booleanp :rule-classes :type-prescription)
  (or (nat-equal depth 0)
      (let ((depth$ (- (nat-fix depth) 1)))
        (and (nodep elem)
             (elem-depth-p depth$ (node->fst elem))
             (if (node2p elem)
                 (elem-depth-p depth$ (node2->snd elem))
               (and (elem-depth-p depth$ (node3->snd elem))
                    (elem-depth-p depth$ (node3->thd elem)))))))
  :measure (nfix depth))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t elem-depth-p)))

(defrule elem-depth-p-when-nat-equiv-congruence
  (implies (nat-equiv depth0 depth1)
           (equal (elem-depth-p depth0 elem)
                  (elem-depth-p depth1 elem)))
  :rule-classes :congruence
  :enable (elem-depth-p
           nfix))

(defruled elem-depth-p-when-not-natp
  (implies (not (natp depth))
           (elem-depth-p depth elem))
  :enable elem-depth-p)

(defrule elem-depth-p-when-not-natp-cheap
  (implies (not (natp depth))
           (elem-depth-p depth elem))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by elem-depth-p-when-not-natp)

(defrule elem-depth-p-when-not-natp-type-prescription
  (implies (not (natp depth))
           (equal (elem-depth-p depth elem)
                  t))
  :rule-classes :type-prescription)

(defrule elem-depth-p-of-0
  (elem-depth-p 0 elem)
  :enable elem-depth-p)

(defruled nodep-when-depth-not-0-and-elem-depth-p
  (implies (and (not (equal (nfix depth) 0))
                (elem-depth-p depth node))
           (nodep node))
  :enable elem-depth-p)

(defrule nodep-when-depth-not-0-and-elem-depth-p-cheap
  (implies (and (elem-depth-p depth node)
                (not (equal (nfix depth) 0)))
           (nodep node))
  :rule-classes ((:rewrite :backchain-limit-lst (0 nil)))
  :by nodep-when-depth-not-0-and-elem-depth-p)

(defrule elem-depth-p-weaken-depth
  (implies (and (elem-depth-p m elem)
                (< (nfix n) (nfix m)))
           (elem-depth-p n elem))
  :induct t
  :enable (elem-depth-p
           nfix))

(defrule elem-depth-p-of-node->fst
  (implies (elem-depth-p (+ 1 (nfix depth)) node)
           (elem-depth-p depth (node->fst node)))
  :enable elem-depth-p)

(defrule elem-depth-p-of-node2->snd
  (implies (and (node2p node)
                (elem-depth-p (+ 1 (nfix depth)) node))
           (elem-depth-p depth (node2->snd node)))
  :enable elem-depth-p)

(defrule elem-depth-p-of-node3->snd
  (implies (and (not (node2p node))
                (elem-depth-p (+ 1 (nfix depth)) node))
           (elem-depth-p depth (node3->snd node)))
  :enable elem-depth-p)

(defrule elem-depth-p-of-node3->thd
  (implies (and (not (node2p node))
                (elem-depth-p (+ 1 (nfix depth)) node))
           (elem-depth-p depth (node3->thd node)))
  :enable elem-depth-p)

(defrule elem-depth-p-of-node2
  (equal (elem-depth-p depth (node2 len a b))
         (or (equal (nfix depth) 0)
             (and (elem-depth-p (- (nfix depth) 1) a)
                  (elem-depth-p (- (nfix depth) 1) b))))
  :enable elem-depth-p)

(defrule elem-depth-p-of-node3
  (equal (elem-depth-p depth (node3 len a b c))
         (or (equal (nfix depth) 0)
             (and (elem-depth-p (- (nfix depth) 1) a)
                  (elem-depth-p (- (nfix depth) 1) b)
                  (elem-depth-p (- (nfix depth) 1) c))))
  :enable elem-depth-p)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define digit-depth-p
  ((depth natp)
   (digit digitp))
  (declare (xargs :split-types t)
           (type unsigned-byte depth)
           (type cons digit))
  :returns (yes/no booleanp :rule-classes :type-prescription)
  (case (digit-case digit)
    (1 (elem-depth-p depth (digit1->fst digit)))
    (2 (and (elem-depth-p depth (digit2->fst digit))
            (elem-depth-p depth (digit2->snd digit))))
    (3 (and (elem-depth-p depth (digit3->fst digit))
            (elem-depth-p depth (digit3->snd digit))
            (elem-depth-p depth (digit3->thd digit))))
    (otherwise (and (elem-depth-p depth (digit4->fst digit))
                    (elem-depth-p depth (digit4->snd digit))
                    (elem-depth-p depth (digit4->thd digit))
                    (elem-depth-p depth (digit4->frth digit))))))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t digit-depth-p)))

(defrule digit-depth-p-when-nat-equiv-congruence
  (implies (nat-equiv depth0 depth1)
           (equal (digit-depth-p depth0 digit)
                  (digit-depth-p depth1 digit)))
  :rule-classes :congruence
  :enable (digit-depth-p
           nfix))

(defrule digit-depth-p-when-digit-equal-congruence
  (implies (digit-equal digit0 digit1)
           (equal (digit-depth-p depth digit0)
                  (digit-depth-p depth digit1)))
  :rule-classes :congruence
  :enable digit-depth-p)

(defruled digit-depth-p-when-not-natp
  (implies (not (natp depth))
           (digit-depth-p depth digit))
  :enable digit-depth-p)

(defrule digit-depth-p-when-not-natp-cheap
  (implies (not (natp depth))
           (digit-depth-p depth digit))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by digit-depth-p-when-not-natp)

(defrule digit-depth-p-when-not-natp-type-prescription
  (implies (not (natp depth))
           (equal (digit-depth-p depth digit)
                  t))
  :rule-classes :type-prescription)

(defrule digit-depth-p-of-0
  (digit-depth-p 0 digit)
  :enable digit-depth-p)

(defrule digit-depth-p-weaken-depth
  (implies (and (digit-depth-p m digit)
                (< (nfix n) (nfix m)))
           (digit-depth-p n digit))
  :enable (digit-depth-p
           nfix))

(defrule elem-depth-p-of-digit1->fst
  (implies (and (equal (digit-case digit) 1)
                (digit-depth-p depth digit))
           (elem-depth-p depth (digit1->fst digit)))
  :enable digit-depth-p)

(defrule elem-depth-p-of-digit2->fst
  (implies (and (equal (digit-case digit) 2)
                (digit-depth-p depth digit))
           (elem-depth-p depth (digit2->fst digit)))
  :enable digit-depth-p)

(defrule elem-depth-p-of-digit2->snd
  (implies (and (equal (digit-case digit) 2)
                (digit-depth-p depth digit))
           (elem-depth-p depth (digit2->snd digit)))
  :enable digit-depth-p)

(defrule elem-depth-p-of-digit3->fst
  (implies (and (equal (digit-case digit) 3)
                (digit-depth-p depth digit))
           (elem-depth-p depth (digit3->fst digit)))
  :enable digit-depth-p)

(defrule elem-depth-p-of-digit3->snd
  (implies (and (equal (digit-case digit) 3)
                (digit-depth-p depth digit))
           (elem-depth-p depth (digit3->snd digit)))
  :enable digit-depth-p)

(defrule elem-depth-p-of-digit3->thd
  (implies (and (equal (digit-case digit) 3)
                (digit-depth-p depth digit))
           (elem-depth-p depth (digit3->thd digit)))
  :enable digit-depth-p)

(defrule elem-depth-p-of-digit4->fst
  (implies (and (equal (digit-case digit) 4)
                (digit-depth-p depth digit))
           (elem-depth-p depth (digit4->fst digit)))
  :enable digit-depth-p)

(defrule elem-depth-p-of-digit4->snd
  (implies (and (equal (digit-case digit) 4)
                (digit-depth-p depth digit))
           (elem-depth-p depth (digit4->snd digit)))
  :enable digit-depth-p)

(defrule elem-depth-p-of-digit4->thd
  (implies (and (equal (digit-case digit) 4)
                (digit-depth-p depth digit))
           (elem-depth-p depth (digit4->thd digit)))
  :enable digit-depth-p)

(defrule elem-depth-p-of-digit4->frth
  (implies (and (equal (digit-case digit) 4)
                (digit-depth-p depth digit))
           (elem-depth-p depth (digit4->frth digit)))
  :enable digit-depth-p)

(defrule digit-depth-p-of-digit1
  (equal (digit-depth-p depth (digit1 len a))
         (elem-depth-p depth a))
  :enable digit-depth-p)

(defrule digit-depth-p-of-digit2
  (equal (digit-depth-p depth (digit2 len a b))
         (and (elem-depth-p depth a)
              (elem-depth-p depth b)))
  :enable digit-depth-p)

(defrule digit-depth-p-of-digit3
  (equal (digit-depth-p depth (digit3 len a b c))
         (and (elem-depth-p depth a)
              (elem-depth-p depth b)
              (elem-depth-p depth c)))
  :enable digit-depth-p)

(defrule digit-depth-p-of-digit4
  (equal (digit-depth-p depth (digit4 len a b c d))
         (and (elem-depth-p depth a)
              (elem-depth-p depth b)
              (elem-depth-p depth c)
              (elem-depth-p depth d)))
  :enable digit-depth-p)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ftree-depth-p
  ((depth natp)
   (tree ftreep))
  (declare (xargs :split-types t)
           (type unsigned-byte depth)
           (type list tree))
  :returns (yes/no booleanp :rule-classes :type-prescription)
  (or (ftree-empty-p tree)
      (if (ftree-single-p tree)
          (elem-depth-p depth (ftree-single->elem tree))
        (and (digit-depth-p depth (ftree-deep->prefix tree))
             (digit-depth-p depth (ftree-deep->suffix tree))
             (ftree-depth-p (+ (nat-fix depth) 1)
                                  (ftree-deep->middle tree)))))
  :measure (acl2-count tree))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t ftree-depth-p)))

(defrule ftree-depth-p-when-nat-equiv-congruence
  (implies (nat-equiv depth0 depth1)
           (equal (ftree-depth-p depth0 tree)
                  (ftree-depth-p depth1 tree)))
  :rule-classes :congruence
  :expand ((ftree-depth-p depth0 tree)
           (ftree-depth-p depth1 tree))
  :enable (ftree-depth-p
           nfix))

(defrule ftree-depth-p-when-ftree-equal-congruence
  (implies (ftree-equal tree0 tree1)
           (equal (ftree-depth-p depth tree0)
                  (ftree-depth-p depth tree1)))
  :rule-classes :congruence
  :expand ((ftree-depth-p depth tree0)
           (ftree-depth-p depth tree1)))

(defrule elem-depth-p-of-ftree-single->elem
  (implies (and (ftree-depth-p depth tree)
                (ftree-single-p tree))
           (elem-depth-p depth (ftree-single->elem tree)))
  :enable ftree-depth-p)

(defrule digit-depth-p-of-ftree-deep->prefix
  (implies (and (ftree-depth-p depth tree)
                (not (ftree-empty-p tree))
                (not (ftree-single-p tree)))
           (digit-depth-p depth (ftree-deep->prefix tree)))
  :enable ftree-depth-p)

(defrule digit-depth-p-of-ftree-deep->suffix
  (implies (and (ftree-depth-p depth tree)
                (not (ftree-empty-p tree))
                (not (ftree-single-p tree)))
           (digit-depth-p depth (ftree-deep->suffix tree)))
  :enable ftree-depth-p)

(defrule ftree-depth-p-of-ftree-deep->middle
  (implies (and (< 0 (nfix depth))
                (ftree-depth-p (- (nfix depth) 1) tree)
                (not (ftree-empty-p tree))
                (not (ftree-single-p tree)))
           (ftree-depth-p depth (ftree-deep->middle tree)))
  :enable ftree-depth-p)

(defrule ftree-depth-p-of-nil
  (ftree-depth-p depth nil)
  :enable ftree-depth-p)

(defrule ftree-depth-p-weaken-depth
  (implies (and (ftree-depth-p m tree)
                (< (nfix n) (nfix m)))
           (ftree-depth-p n tree))
  :induct t
  :enable ftree-depth-p)

(defrule ftree-depth-p-of-ftree-single
  (equal (ftree-depth-p depth (ftree-single a))
         (elem-depth-p depth a))
  :enable ftree-depth-p)

(defrule ftree-depth-p-of-ftree-deep
  (equal (ftree-depth-p depth (ftree-deep len prefix middle suffix))
         (and (digit-depth-p depth prefix)
              (ftree-depth-p (+ (nat-fix depth) 1) middle)
              (digit-depth-p depth suffix)))
  :enable ftree-depth-p)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define elem-len
  ((depth natp)
   elem)
  :guard (elem-depth-p depth elem)
  (declare (xargs :split-types t)
           (type unsigned-byte depth))
  :returns (len natp :rule-classes :type-prescription)
  (if (nat-equal depth 0)
      1
    (let ((depth$ (- (nat-fix depth) 1)))
      (+ (the unsigned-byte (elem-len depth$ (node->fst elem)))
         (the unsigned-byte
           (if (node2p elem)
               (elem-len depth$ (node2->snd elem))
             (+ (the unsigned-byte (elem-len depth$ (node3->snd elem)))
                (the unsigned-byte (elem-len depth$ (node3->thd elem)))))))))
  :measure (nfix depth))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t elem-len)))

(defrule elem-len-when-nat-equiv-congruence
  (implies (nat-equiv depth0 depth1)
           (equal (elem-len depth0 elem)
                  (elem-len depth1 elem)))
  :rule-classes :congruence
  :enable (elem-len
           nfix))

(defrule elem-len-of-node-fix-when-depth-not-0
  (implies (not (equal (nfix depth) 0))
           (equal (elem-len depth (node-fix a))
                  (elem-len depth a)))
  :induct t
  :enable elem-len)

(defruled elem-len-when-not-natp
  (implies (not (natp depth))
           (equal (elem-len depth elem)
                  1))
  :enable elem-len)

(defrule elem-len-when-not-natp-cheap
  (implies (not (natp depth))
           (equal (elem-len depth elem)
                  1))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by elem-len-when-not-natp)

(defrule elem-len-of-0
  (equal (elem-len 0 elem)
         1)
  :enable elem-len)

(defrule elem-len-of-node2
  (equal (elem-len depth (node2 len a b))
         (if (equal (nfix depth) 0)
             1
           (+ (elem-len (- (nfix depth) 1) a)
              (elem-len (- (nfix depth) 1) b))))
  :enable elem-len)

(defrule elem-len-of-node3
  (equal (elem-len depth (node3 len a b c))
         (if (equal (nfix depth) 0)
             1
           (+ (elem-len (- (nfix depth) 1) a)
              (elem-len (- (nfix depth) 1) b)
              (elem-len (- (nfix depth) 1) c))))
  :enable elem-len)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define digit-len
  ((depth natp)
   (digit digitp))
  (declare (xargs :split-types t)
           (type unsigned-byte depth)
           (type cons digit))
  :guard (digit-depth-p depth digit)
  :returns (len natp :rule-classes :type-prescription)
  (case (digit-case digit)
    (1 (elem-len depth (digit1->fst digit)))
    (2 (+ (the unsigned-byte (elem-len depth (digit2->fst digit)))
          (the unsigned-byte (elem-len depth (digit2->snd digit)))))
    (3 (+ (the unsigned-byte (elem-len depth (digit3->fst digit)))
          (the unsigned-byte (elem-len depth (digit3->snd digit)))
          (the unsigned-byte (elem-len depth (digit3->thd digit)))))
    (otherwise (+ (the unsigned-byte (elem-len depth (digit4->fst digit)))
                  (the unsigned-byte (elem-len depth (digit4->snd digit)))
                  (the unsigned-byte (elem-len depth (digit4->thd digit)))
                  (the unsigned-byte (elem-len depth (digit4->frth digit)))))))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t digit-len)))

(defrule digit-len-when-nat-equiv-congruence
  (implies (nat-equiv depth0 depth1)
           (equal (digit-len depth0 digit)
                  (digit-len depth1 digit)))
  :rule-classes :congruence
  :enable digit-len
  :disable acl2::nat-equiv$inline)

(defrule digit-len-when-digit-equal-congruence
  (implies (digit-equal digit0 digit1)
           (equal (digit-len depth digit0)
                  (digit-len depth digit1)))
  :rule-classes :congruence
  :enable digit-len)

(defrule digit-len-of-digit1
  (equal (digit-len depth (digit1 len a))
         (elem-len depth a))
  :enable digit-len)

(defrule digit-len-of-digit2
  (equal (digit-len depth (digit2 len a b))
         (+ (elem-len depth a)
            (elem-len depth b)))
  :enable digit-len)

(defrule digit-len-of-digit3
  (equal (digit-len depth (digit3 len a b c))
         (+ (elem-len depth a)
            (elem-len depth b)
            (elem-len depth c)))
  :enable digit-len)

(defrule digit-len-of-digit4
  (equal (digit-len depth (digit4 len a b c d))
         (+ (elem-len depth a)
            (elem-len depth b)
            (elem-len depth c)
            (elem-len depth d)))
  :enable digit-len)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ftree-len
  ((depth natp)
   (tree ftreep))
  (declare (xargs :split-types t)
           (type unsigned-byte depth)
           (type list tree))
  :guard (ftree-depth-p depth tree)
  :returns (len natp :rule-classes :type-prescription)
  (if (ftree-empty-p tree)
      0
    (if (ftree-single-p tree)
        (elem-len depth (ftree-single->elem tree))
      (+ (the unsigned-byte (digit-len depth (ftree-deep->prefix tree)))
         (the unsigned-byte (digit-len depth (ftree-deep->suffix tree)))
         (the unsigned-byte (ftree-len (+ (nat-fix depth) 1)
                                       (ftree-deep->middle tree))))))
  :measure (acl2-count tree))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t ftree-len)))

(defrule ftree-len-when-nat-equiv-congruence
  (implies (nat-equiv depth0 depth1)
           (equal (ftree-len depth0 tree)
                  (ftree-len depth1 tree)))
  :rule-classes :congruence
  :expand ((ftree-len depth0 tree)
           (ftree-len depth1 tree))
  :disable acl2::nat-equiv$inline)

(defrule ftree-len-when-ftree-equal-congruence
  (implies (ftree-equal tree0 tree1)
           (equal (ftree-len depth tree0)
                  (ftree-len depth tree1)))
  :rule-classes :congruence
  :expand ((ftree-len depth tree0)
           (ftree-len depth tree1)))

(defrule ftree-len-of-nil
  (equal (ftree-len depth nil)
         0)
  :enable ftree-len)

(defruled ftree-len-when-ftree-empty-p
  (implies (ftree-empty-p tree)
           (equal (ftree-len depth tree)
                  0))
  :enable ftree-len)

(defrule ftree-len-when-ftree-empty-p-cheap
  (implies (ftree-empty-p tree)
           (equal (ftree-len depth tree)
                  0))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by ftree-len-when-ftree-empty-p)

(defrule ftree-len-of-ftree-single
  (equal (ftree-len depth (ftree-single a))
         (elem-len depth a))
  :enable ftree-len)

(defrule ftree-len-of-ftree-deep
  (equal (ftree-len depth (ftree-deep len prefix middle suffix))
         (+ (digit-len depth prefix)
            (ftree-len (+ (nat-fix depth) 1) middle)
            (digit-len depth suffix)))
  :enable ftree-len)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define elem-len-invariant?
  ((depth natp)
   (elem (elem-depth-p depth elem)))
  (declare (xargs :split-types t)
           (type unsigned-byte depth))
  :returns (len? (or (not len?) (natp len?)) :rule-classes :type-prescription)
  (if (nat-equal depth 0)
      1
    (let* ((depth$ (- (nat-fix depth) 1))
           (len-fst? (elem-len-invariant? depth$ (node->fst elem))))
      (and len-fst?
           (if (node2p elem)
               (let ((len-snd? (elem-len-invariant? depth$ (node2->snd elem))))
                 (and len-snd?
                      (equal (node->len elem)
                             (+ (the unsigned-byte len-fst?)
                                (the unsigned-byte len-snd?)))))
             (let ((len-snd? (elem-len-invariant? depth$ (node3->snd elem))))
               (and len-snd?
                    (let ((len-thd? (elem-len-invariant? depth$ (node3->thd elem))))
                      (and len-thd?
                           (equal (node->len elem)
                                  (+ (the unsigned-byte len-fst?)
                                     (the unsigned-byte len-snd?)
                                     (the unsigned-byte len-thd?))))))))
           (node->len elem))))
  :measure (nfix depth))

(define elem-len-invariant-p
  ((depth natp)
   (elem (elem-depth-p depth elem)))
  (declare (xargs :split-types t)
           (type unsigned-byte depth))
  :returns (yes/no booleanp :rule-classes :type-prescription)
  (mbe :logic (or (equal (nfix depth) 0)
                  (and (elem-len-invariant-p (- (nfix depth) 1) (node->fst elem))
                       (if (node2p elem)
                           (elem-len-invariant-p (- (nfix depth) 1) (node2->snd elem))
                         (and (elem-len-invariant-p (- (nfix depth) 1) (node3->snd elem))
                              (elem-len-invariant-p (- (nfix depth) 1) (node3->thd elem))))
                       (equal (node->len elem) (elem-len depth elem))))
       :exec (and (elem-len-invariant? depth elem) t))
  :measure (nfix depth)
  ;; Verified below
  :verify-guards nil)

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t elem-len-invariant?) (:t elem-len-invariant-p)))

(defrule elem-len-invariant?-when-nat-equiv-congruence
  (implies (nat-equiv depth0 depth1)
           (equal (elem-len-invariant? depth0 elem)
                  (elem-len-invariant? depth1 elem)))
  :rule-classes :congruence
  :enable (elem-len-invariant?
           nfix))

(defrule elem-len-invariant-p-when-nat-equiv-congruence
  (implies (nat-equiv depth0 depth1)
           (equal (elem-len-invariant-p depth0 elem)
                  (elem-len-invariant-p depth1 elem)))
  :rule-classes :congruence
  :enable (elem-len-invariant-p
           nfix))

(defrule elem-len-invariant-p-of-node-fix-when-depth-not-0
  (implies (not (equal (nfix depth) 0))
           (equal (elem-len-invariant-p depth (node-fix a))
                  (elem-len-invariant-p depth a)))
  :induct t
  :enable elem-len-invariant-p)

(defrule elem-len-invariant?-becomes-elem-len-invariant-p
  (equal (elem-len-invariant? depth elem)
         (and (elem-len-invariant-p depth elem)
              (elem-len depth elem)))
  :rule-classes :definition
  :induct t
  :enable (elem-len-invariant?
           elem-len-invariant-p
           elem-len))

(verify-guards elem-len-invariant-p
  :hints (("Goal" :in-theory (enable elem-len-invariant-p))))

(defruled elem-len-invariant-p-when-not-natp
  (implies (not (natp depth))
           (elem-len-invariant-p depth elem))
  :enable elem-len-invariant-p)

(defrule elem-len-invariant-p-when-not-natp-cheap
  (implies (not (natp depth))
           (elem-len-invariant-p depth elem))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by elem-len-invariant-p-when-not-natp)

(defrule elem-len-invariant-p-when-not-natp-type-prescription
  (implies (not (natp depth))
           (equal (elem-len-invariant-p depth elem)
                  t))
  :rule-classes :type-prescription)

(defrule elem-len-invariant-p-of-0
  (elem-len-invariant-p 0 elem)
  :enable elem-len-invariant-p)

(defrule elem-len-invariant-p-of-node->fst
  (implies (elem-len-invariant-p (+ 1 (nfix depth)) node)
           (elem-len-invariant-p depth (node->fst node)))
  :enable elem-len-invariant-p)

(defrule elem-len-invariant-p-of-node2->snd
  (implies (and (node2p node)
                (elem-len-invariant-p (+ 1 (nfix depth)) node))
           (elem-len-invariant-p depth (node2->snd node)))
  :enable elem-len-invariant-p)

(defrule elem-len-invariant-p-of-node3->snd
  (implies (and (not (node2p node))
                (elem-len-invariant-p (+ 1 (nfix depth)) node))
           (elem-len-invariant-p depth (node3->snd node)))
  :enable elem-len-invariant-p)

(defrule elem-len-invariant-p-of-node3->thd
  (implies (and (not (node2p node))
                (elem-len-invariant-p (+ 1 (nfix depth)) node))
           (elem-len-invariant-p depth (node3->thd node)))
  :enable elem-len-invariant-p)

(defrule elem-len-invariant-p-of-node2
  (equal (elem-len-invariant-p depth (node2 len a b))
         (or (equal (nfix depth) 0)
             (and (elem-len-invariant-p (- (nfix depth) 1) a)
                  (elem-len-invariant-p (- (nfix depth) 1) b)
                  (equal (nfix len) (elem-len depth (node2 len a b))))))
  :enable elem-len-invariant-p)

(defrule elem-len-invrariant-p-of-node3
  (equal (elem-len-invariant-p depth (node3 len a b c))
         (or (equal (nfix depth) 0)
             (and (elem-len-invariant-p (- (nfix depth) 1) a)
                  (elem-len-invariant-p (- (nfix depth) 1) b)
                  (elem-len-invariant-p (- (nfix depth) 1) c)
                  (equal (nfix len) (elem-len depth (node3 len a b c))))))
  :enable elem-len-invariant-p)

(defrule node->len-when-elem-len-invariant-p
  (implies (and (elem-len-invariant-p depth node)
                (not (equal (nfix depth) 0)))
           (equal (node->len node)
                  (elem-len depth node)))
  :enable elem-len-invariant-p)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define digit-len-invariant?
  ((depth natp)
   (digit digitp))
  (declare (xargs :split-types t)
           (type unsigned-byte depth)
           (type cons digit))
  :guard (digit-depth-p depth digit)
  :returns (len? (or (not len?) (natp len?)) :rule-classes :type-prescription)
  (and
   (case (digit-case digit)
     (1 (let ((len-fst? (elem-len-invariant? depth (digit1->fst digit))))
          (and len-fst?
               (equal (digit->len digit) len-fst?))))
     (2 (let ((len-fst? (elem-len-invariant? depth (digit2->fst digit))))
          (and len-fst?
               (let ((len-snd? (elem-len-invariant? depth (digit2->snd digit))))
                 (and len-snd?
                      (equal (digit->len digit)
                             (+ (the unsigned-byte len-fst?)
                                (the unsigned-byte len-snd?))))))))
     (3 (let ((len-fst? (elem-len-invariant? depth (digit3->fst digit))))
          (and len-fst?
               (let ((len-snd? (elem-len-invariant? depth (digit3->snd digit))))
                 (and len-snd?
                      (let ((len-thd? (elem-len-invariant? depth (digit3->thd digit))))
                        (and len-thd?
                             (equal (digit->len digit)
                                    (+ (the unsigned-byte len-fst?)
                                       (the unsigned-byte len-snd?)
                                       (the unsigned-byte len-thd?))))))))))
     (otherwise
       (let ((len-fst? (elem-len-invariant? depth (digit4->fst digit))))
         (and len-fst?
              (let ((len-snd? (elem-len-invariant? depth (digit4->snd digit))))
                (and len-snd?
                     (let ((len-thd? (elem-len-invariant? depth (digit4->thd digit))))
                       (and len-thd?
                            (let ((len-frth? (elem-len-invariant? depth (digit4->frth digit))))
                              (and len-frth?
                                   (equal (digit->len digit)
                                          (+ (the unsigned-byte len-fst?)
                                             (the unsigned-byte len-snd?)
                                             (the unsigned-byte len-thd?)
                                             (the unsigned-byte len-frth?)))))))))))))
   (digit->len digit)))

(define digit-len-invariant-p
  ((depth natp)
   (digit digitp))
  (declare (xargs :split-types t)
           (type unsigned-byte depth)
           (type cons digit))
  :guard (digit-depth-p depth digit)
  :returns (yes/no booleanp :rule-classes :type-prescription)
  (mbe :logic (and
                (case (digit-case digit)
                  (1 (elem-len-invariant-p depth (digit1->fst digit)))
                  (2 (and (elem-len-invariant-p depth (digit2->fst digit))
                          (elem-len-invariant-p depth (digit2->snd digit))))
                  (3 (and (elem-len-invariant-p depth (digit3->fst digit))
                          (elem-len-invariant-p depth (digit3->snd digit))
                          (elem-len-invariant-p depth (digit3->thd digit))))
                  (otherwise
                    (and (elem-len-invariant-p depth (digit4->fst digit))
                         (elem-len-invariant-p depth (digit4->snd digit))
                         (elem-len-invariant-p depth (digit4->thd digit))
                         (elem-len-invariant-p depth (digit4->frth digit)))))
                (equal (digit->len digit) (digit-len depth digit)))
       :exec (and (digit-len-invariant? depth digit) t))
  ;; Verified below
  :verify-guards nil)

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t digit-len-invariant?) (:t digit-len-invariant-p)))

(defrule digit-len-invariant?-when-nat-equiv-congruence
  (implies (nat-equiv depth0 depth1)
           (equal (digit-len-invariant? depth0 digit)
                  (digit-len-invariant? depth1 digit)))
  :rule-classes :congruence
  :enable (digit-len-invariant?
           nfix))

(defrule digit-len-invariant?-when-digit-equal-congruence
  (implies (digit-equal digit0 digit1)
           (equal (digit-len-invariant? depth digit0)
                  (digit-len-invariant? depth digit1)))
  :rule-classes :congruence
  :enable digit-len-invariant?)

(defrule digit-len-invariant-p-when-nat-equiv-congruence
  (implies (nat-equiv depth0 depth1)
           (equal (digit-len-invariant-p depth0 digit)
                  (digit-len-invariant-p depth1 digit)))
  :rule-classes :congruence
  :enable digit-len-invariant-p
  :disable acl2::nat-equiv$inline)

(defrule digit-len-invariant-p-when-digit-equal-congruence
  (implies (digit-equal digit0 digit1)
           (equal (digit-len-invariant-p depth digit0)
                  (digit-len-invariant-p depth digit1)))
  :rule-classes :congruence
  :enable digit-len-invariant-p)

(defrule digit-len-invariant?-becomes-digit-len-invariant-p
  (equal (digit-len-invariant? depth digit)
         (and (digit-len-invariant-p depth digit)
              (digit-len depth digit)))
  :rule-classes :definition
  :enable (digit-len-invariant?
           digit-len-invariant-p
           digit-len))

(verify-guards digit-len-invariant-p
  :hints (("Goal" :in-theory (enable digit-len-invariant-p))))

(defrule digit-len-invariant-p-of-digit1
  (equal (digit-len-invariant-p depth (digit1 len a))
         (and (elem-len-invariant-p depth a)
              (equal (nfix len) (digit-len depth (digit1 len a)))))
  :enable digit-len-invariant-p)

(defrule digit-len-invariant-p-of-digit2
  (equal (digit-len-invariant-p depth (digit2 len a b))
         (and (elem-len-invariant-p depth a)
              (elem-len-invariant-p depth b)
              (equal (nfix len) (digit-len depth (digit2 len a b)))))
  :enable digit-len-invariant-p)

(defrule digit-len-invariant-p-of-digit3
  (equal (digit-len-invariant-p depth (digit3 len a b c))
         (and (elem-len-invariant-p depth a)
              (elem-len-invariant-p depth b)
              (elem-len-invariant-p depth c)
              (equal (nfix len) (digit-len depth (digit3 len a b c)))))
  :enable digit-len-invariant-p)

(defrule digit-len-invariant-p-of-digit4
  (equal (digit-len-invariant-p depth (digit4 len a b c d))
         (and (elem-len-invariant-p depth a)
              (elem-len-invariant-p depth b)
              (elem-len-invariant-p depth c)
              (elem-len-invariant-p depth d)
              (equal (nfix len) (digit-len depth (digit4 len a b c d)))))
  :enable digit-len-invariant-p)

(defrule digit->len-when-digit-len-invariant-p
  (implies (digit-len-invariant-p depth digit)
           (equal (digit->len digit)
                  (digit-len depth digit)))
  :enable digit-len-invariant-p)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ftree-len-invariant?
  ((depth natp)
   (tree ftreep))
  (declare (xargs :split-types t)
           (type unsigned-byte depth)
           (type list tree))
  :guard (ftree-depth-p depth tree)
  :returns (len? (or (not len?) (natp len?)) :rule-classes :type-prescription)
  (if (ftree-empty-p tree)
      0
    (if (ftree-single-p tree)
        (elem-len-invariant? depth (ftree-single->elem tree))
      (let ((len-prefix? (digit-len-invariant? depth (ftree-deep->prefix tree))))
        (and len-prefix?
             (let ((len-suffix?
                     (digit-len-invariant? depth (ftree-deep->suffix tree))))
               (and len-suffix?
                    (let ((len-middle?
                            (ftree-len-invariant? (+ (nfix depth) 1)
                                                  (ftree-deep->middle tree))))
                      (and len-middle?
                           (equal (ftree-deep->len tree)
                                  (+ (the unsigned-byte len-prefix?)
                                     (the unsigned-byte len-suffix?)
                                     (the unsigned-byte len-middle?)))
                           (ftree-deep->len tree)))))))))
  :measure (acl2-count tree))

(define ftree-len-invariant-p
  ((depth natp)
   (tree ftreep))
  (declare (xargs :split-types t)
           (type unsigned-byte depth)
           (type list tree))
  :guard (ftree-depth-p depth tree)
  :returns (yes/no booleanp :rule-classes :type-prescription)
  (mbe :logic
       (or (ftree-empty-p tree)
           (if (ftree-single-p tree)
               (elem-len-invariant-p depth (ftree-single->elem tree))
             (and (digit-len-invariant-p depth (ftree-deep->prefix tree))
                  (digit-len-invariant-p depth (ftree-deep->suffix tree))
                  (ftree-len-invariant-p (+ (nfix depth) 1)
                                         (ftree-deep->middle tree))
                  (equal (ftree-deep->len tree) (ftree-len depth tree)))))
       :exec (and (ftree-len-invariant? depth tree) t))
  :measure (acl2-count tree)
  ;; Verified below
  :verify-guards nil)

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t ftree-len-invariant?) (:t ftree-len-invariant-p)))

(defrule ftree-len-invariant?-when-nat-equiv-congruence
  (implies (nat-equiv depth0 depth1)
           (equal (ftree-len-invariant? depth0 tree)
                  (ftree-len-invariant? depth1 tree)))
  :rule-classes :congruence
  :induct t
  :enable ftree-len-invariant?
  :disable acl2::nat-equiv$inline)

(defrule ftree-len-invariant?-when-ftree-equal-congruence
  (implies (ftree-equal tree0 tree1)
           (equal (ftree-len-invariant? depth tree0)
                  (ftree-len-invariant? depth tree1)))
  :rule-classes :congruence
  :induct t
  :enable ftree-len-invariant?)

(defrule ftree-len-invariant-p-when-nat-equiv-congruence
  (implies (nat-equiv depth0 depth1)
           (equal (ftree-len-invariant-p depth0 tree)
                  (ftree-len-invariant-p depth1 tree)))
  :rule-classes :congruence
  :induct t
  :enable ftree-len-invariant-p
  :disable acl2::nat-equiv$inline)

(defrule ftree-len-invariant-p-when-ftree-equal-congruence
  (implies (ftree-equal tree0 tree1)
           (equal (ftree-len-invariant-p depth tree0)
                  (ftree-len-invariant-p depth tree1)))
  :rule-classes :congruence
  :induct t
  :enable ftree-len-invariant-p)

(defrule ftree-len-invariant?-becomes-ftree-len-invariant-p
  (equal (ftree-len-invariant? depth tree)
         (and (ftree-len-invariant-p depth tree)
              (ftree-len depth tree)))
  :rule-classes :definition
  :induct t
  :enable (ftree-len-invariant?
           ftree-len-invariant-p
           ftree-len))

(verify-guards ftree-len-invariant-p
  :hints (("Goal" :in-theory (enable ftree-len-invariant-p))))

(defrule ftree-len-invariant-p-of-nil
  (ftree-len-invariant-p depth nil)
  :enable ftree-len-invariant-p)

(defrule ftree-len-invariant-p-of-ftree-single
  (equal (ftree-len-invariant-p depth (ftree-single a))
         (elem-len-invariant-p depth a))
  :enable ftree-len-invariant-p)

(defrule ftree-len-invariant-p-of-ftree-deep
  (equal (ftree-len-invariant-p depth (ftree-deep len prefix middle suffix))
         (and (digit-len-invariant-p depth prefix)
              (digit-len-invariant-p depth suffix)
              (ftree-len-invariant-p (+ (nfix depth) 1) middle)
              (equal (nfix len)
                     (ftree-len depth (ftree-deep len prefix middle suffix)))))
  :enable ftree-len-invariant-p)

(defrule ftree-deep->len-when-ftree-invariant-p
  (implies (and (ftree-len-invariant-p depth tree)
                (not (ftree-empty-p tree))
                (not (ftree-single-p tree)))
           (equal (ftree-deep->len tree)
                  (ftree-len depth tree)))
  :enable ftree-len-invariant-p)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ftree-well-formed-p
  ((tree ftreep))
  :returns (yes/no booleanp :rule-classes :type-prescription)
  (and (ftree-depth-p 0 tree)
       (ftree-len-invariant-p 0 tree))
  :inline t)

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t ftree-well-formed-p)))

(defrule ftree-well-formed-p-when-ftree-equal-congruence
  (implies (ftree-equal tree0 tree1)
           (equal (ftree-well-formed-p tree0)
                  (ftree-well-formed-p tree1)))
  :rule-classes :congruence
  :enable ftree-well-formed-p)

(defruled ftree-depth-p-when-ftree-well-formed-p
  (implies (ftree-well-formed-p tree)
           (ftree-depth-p 0 tree))
  :enable ftree-well-formed-p)

(defrule ftree-depth-p-when-ftree-well-formed-p-forward-chaining
  (implies (ftree-well-formed-p tree)
           (ftree-depth-p 0 tree))
  :rule-classes :forward-chaining
  :by ftree-depth-p-when-ftree-well-formed-p)

(defruled ftree-len-invariant-p-when-ftree-well-formed-p
  (implies (ftree-well-formed-p tree)
           (ftree-len-invariant-p 0 tree))
  :enable ftree-well-formed-p)

(defrule ftree-len-invariant-p-when-ftree-well-formed-p-forward-chaining
  (implies (ftree-well-formed-p tree)
           (ftree-len-invariant-p 0 tree))
  :rule-classes :forward-chaining
  :by ftree-len-invariant-p-when-ftree-well-formed-p)

(defrule ftree-well-formed-p-when-depth-and-len-invariant-cheap
  (implies (and (ftree-depth-p 0 tree)
                (ftree-len-invariant-p 0 tree))
           (ftree-well-formed-p tree))
  :rule-classes ((:rewrite :backchain-limit-lst (0 0)))
  :enable ftree-well-formed-p)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define elem-len-cached
  ((depth natp)
   elem)
  :guard (and (elem-depth-p depth elem)
              (elem-len-invariant-p depth elem))
  (declare (xargs :split-types t)
           (type unsigned-byte depth))
  :returns (len natp :rule-classes :type-prescription)
  (mbe :logic (elem-len depth elem)
       :exec (if (nat-equal depth 0)
                 1
               (node->len elem)))
  :enabled t
  :inline t
  :guard-hints (("Goal" :in-theory (enable elem-len-invariant-p))))

(define digit-len-cached
  ((depth natp)
   (digit digitp))
  :guard (and (digit-depth-p depth digit)
              (digit-len-invariant-p depth digit))
  (declare (xargs :split-types t)
           (type unsigned-byte depth))
  :returns (len natp :rule-classes :type-prescription)
  (mbe :logic (digit-len depth digit)
       :exec (digit->len digit))
  :enabled t
  :inline t
  :guard-hints (("Goal" :in-theory (enable digit-len-invariant-p))))

(define ftree-len-cached
  ((depth natp)
   (tree ftreep))
  :guard (and (ftree-depth-p depth tree)
              (ftree-len-invariant-p depth tree))
  (declare (xargs :split-types t)
           (type unsigned-byte depth))
  :returns (len natp :rule-classes :type-prescription)
  (mbe :logic (ftree-len depth tree)
       :exec (if (ftree-empty-p tree)
                 0
               (if (ftree-single-p tree)
                   (elem-len-cached depth (ftree-single->elem tree))
                 (ftree-deep->len tree))))
  :enabled t
  :inline t
  :guard-hints (("Goal" :in-theory (enable ftree-well-formed-p))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Smart constructors

;; TODO

(define digit1$ (a)
  :returns (digit digitp :rule-classes (:rewrite :type-prescription))
  (digit1 1 a)
  :inline t)

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t digit1$)))

(defrule digit-case-of-digit1$
  (equal (digit-case (digit1$ a))
         1)
  :enable digit1$)

(defrule digit->len-of-digit1$
  (equal (digit->len (digit1$ a))
         1)
  :enable digit1$)

(defrule digit1->fst-of-digit1$
  (equal (digit1->fst (digit1$ a))
         a)
  :enable digit1$)

(defrule digit-depth-p-of-digit1$
  (equal (digit-depth-p depth (digit1$ a))
         (elem-depth-p depth a))
  :enable digit1$)

(defrule digit-len-invariant-p-of-digit1$
  (digit-len-invariant-p 0 (digit1$ a))
  :enable digit1$)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define digit2$ (a b)
  :returns (digit digitp :rule-classes (:rewrite :type-prescription))
  (digit2 2 a b)
  :inline t)

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t digit2$)))

(defrule digit-case-of-digit2$
  (equal (digit-case (digit2$ a b))
         2)
  :enable digit2$)

(defrule digit->len-of-digit2$
  (equal (digit->len (digit2$ a b))
         2)
  :enable digit2$)

(defrule digit2->fst-of-digit2$
  (equal (digit2->fst (digit2$ a b))
         a)
  :enable digit2$)

(defrule digit2->snd-of-digit2$
  (equal (digit2->snd (digit2$ a b))
         b)
  :enable digit2$)

(defrule digit-depth-p-of-digit2$
  (equal (digit-depth-p depth (digit2$ a b))
         (and (elem-depth-p depth a)
              (elem-depth-p depth b)))
  :enable digit2$)

(defrule digit-len-invariant-p-of-digit2$
  (digit-len-invariant-p 0 (digit2$ a b))
  :enable digit2$)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define digit3$ (a b c)
  :returns (digit digitp :rule-classes (:rewrite :type-prescription))
  (digit3 3 a b c)
  :inline t)

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t digit3$)))

(defrule digit-case-of-digit3$
  (equal (digit-case (digit3$ a b c))
         3)
  :enable digit3$)

(defrule digit->len-of-digit3$
  (equal (digit->len (digit3$ a b c))
         3)
  :enable digit3$)

(defrule digit3->fst-of-digit3$
  (equal (digit3->fst (digit3$ a b c))
         a)
  :enable digit3$)

(defrule digit3->snd-of-digit3$
  (equal (digit3->snd (digit3$ a b c))
         b)
  :enable digit3$)

(defrule digit3->thd-of-digit3$
  (equal (digit3->thd (digit3$ a b c))
         c)
  :enable digit3$)

(defrule digit-depth-p-of-digit3$
  (equal (digit-depth-p depth (digit3$ a b c))
         (and (elem-depth-p depth a)
              (elem-depth-p depth b)
              (elem-depth-p depth c)))
  :enable digit3$)

(defrule digit-len-invariant-p-of-digit3$
  (digit-len-invariant-p 0 (digit3$ a b c))
  :enable digit3$)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define digit4$ (a b c d)
  :returns (digit digitp :rule-classes (:rewrite :type-prescription))
  (digit4 4 a b c d)
  :inline t)

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t digit4$)))

(defrule digit-case-of-digit4$
  (equal (digit-case (digit4$ a b c d))
         4)
  :enable digit4$)

(defrule digit->len-of-digit4$
  (equal (digit->len (digit4$ a b c d))
         4)
  :enable digit4$)

(defrule digit4->fst-of-digit4$
  (equal (digit4->fst (digit4$ a b c d))
         a)
  :enable digit4$)

(defrule digit4->snd-of-digit4$
  (equal (digit4->snd (digit4$ a b c d))
         b)
  :enable digit4$)

(defrule digit4->thd-of-digit4$
  (equal (digit4->thd (digit4$ a b c d))
         c)
  :enable digit4$)

(defrule digit4->frth-of-digit4$
  (equal (digit4->frth (digit4$ a b c d))
         d)
  :enable digit4$)

(defrule digit-depth-p-of-digit4$
  (equal (digit-depth-p depth (digit4$ a b c d))
         (and (elem-depth-p depth a)
              (elem-depth-p depth b)
              (elem-depth-p depth c)
              (elem-depth-p depth d)))
  :enable digit4$)

(defrule digit-len-invariant-p-of-digit4$
  (digit-len-invariant-p 0 (digit4$ a b c d))
  :enable digit4$)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro digit$ (&rest args)
  (case (acl2::len args)
    (1 `(digit1$ ,@args))
    (2 `(digit2$ ,@args))
    (3 `(digit3$ ,@args))
    (4 `(digit4$ ,@args))
    (otherwise
      (er hard 'digit "Illegal number of arguments: ~x0." (acl2::len args)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define digit1$node ((a nodep))
  :returns (digit digitp :rule-classes (:rewrite :type-prescription))
  (digit1 (node->len a) (node-fix a))
  :inline t)

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t digit1$node)))

(defrule digit1$node-when-node-equal-congruence
  (implies (node-equal a0 a1)
           (equal (digit1$node a0)
                  (digit1$node a1)))
  :rule-classes :congruence
  :enable digit1$node)

(defrule digit-case-of-digit1$node
  (equal (digit-case (digit1$node a))
         1)
  :enable digit1$node)

(defruled digit->len-of-digit1$node
  (equal (digit->len (digit1$node a))
         (node->len a))
  :enable digit1$node)

(defrule digit1->fst-of-digit1$node
  (equal (digit1->fst (digit1$node a))
         (node-fix a))
  :enable digit1$node)

(defrule digit->len-of-digit1$node-when-digit-len-invariant-p
  (implies (digit-len-invariant-p depth (digit1$node a))
           (equal (digit->len (digit1$node a))
                  (digit-len depth (digit1$node a))))
  :enable digit-len-invariant-p)

(defrule digit-depth-p-of-digit1$node
  (equal (digit-depth-p depth (digit1$node a))
         (elem-depth-p depth (node-fix a)))
  :enable digit1$node)

(defrule digit-len-invariant-p-of-digit1$node
  (implies (not (equal (nfix depth) 0))
           (equal (digit-len-invariant-p depth (digit1$node a))
                  (elem-len-invariant-p depth (node-fix a))))
  :expand (elem-len-invariant-p depth (node-fix a))
  :enable digit1$node)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define digit2$node
  ((a nodep)
   (b nodep))
  :returns (digit digitp :rule-classes (:rewrite :type-prescription))
  (digit2 (+ (the unsigned-byte (node->len a))
             (the unsigned-byte (node->len b)))
          (node-fix a)
          (node-fix b))
  :inline t)

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t digit2$node)))

(defrule digit2$node-when-node-equal-of-arg1-congruence
  (implies (node-equal a0 a1)
           (equal (digit2$node a0 b)
                  (digit2$node a1 b)))
  :rule-classes :congruence
  :enable digit2$node)

(defrule digit2$node-when-node-equal-of-arg2-congruence
  (implies (node-equal b0 b1)
           (equal (digit2$node a b0)
                  (digit2$node a b1)))
  :rule-classes :congruence
  :enable digit2$node)

(defrule digit-case-of-digit2$node
  (equal (digit-case (digit2$node a b))
         2)
  :enable digit2$node)

(defruled digit->len-of-digit2$node
  (equal (digit->len (digit2$node a b))
         (+ (node->len a) (node->len b)))
  :enable digit2$node)

(defrule digit2->fst-of-digit2$node
  (equal (digit2->fst (digit2$node a b))
         (node-fix a))
  :enable digit2$node)

(defrule digit2->snd-of-digit2$node
  (equal (digit2->snd (digit2$node a b))
         (node-fix b))
  :enable digit2$node)

(defrule digit->len-of-digit2$node-when-digit-len-invariant-p
  (implies (digit-len-invariant-p depth (digit2$node a b))
           (equal (digit->len (digit2$node a b))
                  (digit-len depth (digit2$node a b))))
  :enable digit-len-invariant-p)

(defrule digit-depth-p-of-digit2$node
  (equal (digit-depth-p depth (digit2$node a b))
         (and (elem-depth-p depth (node-fix a))
              (elem-depth-p depth (node-fix b))))
  :enable digit2$node)

(defrule digit-len-invariant-p-of-digit2$node
  (implies (not (equal (nfix depth) 0))
           (equal (digit-len-invariant-p depth (digit2$node a b))
                  (and (elem-len-invariant-p depth (node-fix a))
                       (elem-len-invariant-p depth (node-fix b)))))
  :expand ((elem-len-invariant-p depth (node-fix a))
           (elem-len-invariant-p depth (node-fix b)))
  :enable digit2$node)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define digit3$node
  ((a nodep)
   (b nodep)
   (c nodep))
  :returns (digit digitp :rule-classes (:rewrite :type-prescription))
  (digit3 (+ (the unsigned-byte (node->len a))
             (the unsigned-byte (node->len b))
             (the unsigned-byte (node->len c)))
          (node-fix a)
          (node-fix b)
          (node-fix c))
  :inline t)

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t digit3$node)))

(defrule digit3$node-when-node-equal-of-arg1-congruence
  (implies (node-equal a0 a1)
           (equal (digit3$node a0 b c)
                  (digit3$node a1 b c)))
  :rule-classes :congruence
  :enable digit3$node)

(defrule digit3$node-when-node-equal-of-arg2-congruence
  (implies (node-equal b0 b1)
           (equal (digit3$node a b0 c)
                  (digit3$node a b1 c)))
  :rule-classes :congruence
  :enable digit3$node)

(defrule digit3$node-when-node-equal-of-arg3-congruence
  (implies (node-equal c0 c1)
           (equal (digit3$node a b c0)
                  (digit3$node a b c1)))
  :rule-classes :congruence
  :enable digit3$node)

(defrule digit-case-of-digit3$node
  (equal (digit-case (digit3$node a b c))
         3)
  :enable digit3$node)

(defruled digit->len-of-digit3$node
  (equal (digit->len (digit3$node a b c))
         (+ (node->len a) (node->len b) (node->len c)))
  :enable digit3$node)

(defrule digit3->fst-of-digit3$node
  (equal (digit3->fst (digit3$node a b c))
         (node-fix a))
  :enable digit3$node)

(defrule digit3->snd-of-digit3$node
  (equal (digit3->snd (digit3$node a b c))
         (node-fix b))
  :enable digit3$node)

(defrule digit3->thd-of-digit3$node
  (equal (digit3->thd (digit3$node a b c))
         (node-fix c))
  :enable digit3$node)

(defrule digit->len-of-digit3$node-when-digit-len-invariant-p
  (implies (digit-len-invariant-p depth (digit3$node a b c))
           (equal (digit->len (digit3$node a b c))
                  (digit-len depth (digit3$node a b c))))
  :enable digit-len-invariant-p)

(defrule digit-depth-p-of-digit3$node
  (equal (digit-depth-p depth (digit3$node a b c))
         (and (elem-depth-p depth (node-fix a))
              (elem-depth-p depth (node-fix b))
              (elem-depth-p depth (node-fix c))))
  :enable digit3$node)

(defrule digit-len-invariant-p-of-digit3$node
  (implies (not (equal (nfix depth) 0))
           (equal (digit-len-invariant-p depth (digit3$node a b c))
                  (and (elem-len-invariant-p depth (node-fix a))
                       (elem-len-invariant-p depth (node-fix b))
                       (elem-len-invariant-p depth (node-fix c)))))
  :expand ((elem-len-invariant-p depth (node-fix a))
           (elem-len-invariant-p depth (node-fix b))
           (elem-len-invariant-p depth (node-fix c)))
  :enable digit3$node)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define digit4$node
  ((a nodep)
   (b nodep)
   (c nodep)
   (d nodep))
  :returns (digit digitp :rule-classes (:rewrite :type-prescription))
  (digit4 (+ (the unsigned-byte (node->len a))
             (the unsigned-byte (node->len b))
             (the unsigned-byte (node->len c))
             (the unsigned-byte (node->len d)))
          (node-fix a)
          (node-fix b)
          (node-fix c)
          (node-fix d))
  :inline t)

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t digit4$node)))

(defrule digit4$node-when-node-equal-of-arg1-congruence
  (implies (node-equal a0 a1)
           (equal (digit4$node a0 b c d)
                  (digit4$node a1 b c d)))
  :rule-classes :congruence
  :enable digit4$node)

(defrule digit4$node-when-node-equal-of-arg2-congruence
  (implies (node-equal b0 b1)
           (equal (digit4$node a b0 c d)
                  (digit4$node a b1 c d)))
  :rule-classes :congruence
  :enable digit4$node)

(defrule digit4$node-when-node-equal-of-arg3-congruence
  (implies (node-equal c0 c1)
           (equal (digit4$node a b c0 d)
                  (digit4$node a b c1 d)))
  :rule-classes :congruence
  :enable digit4$node)

(defrule digit4$node-when-node-equal-of-arg4-congruence
  (implies (node-equal d0 d1)
           (equal (digit4$node a b c d0)
                  (digit4$node a b c d1)))
  :rule-classes :congruence
  :enable digit4$node)

(defrule digit-case-of-digit4$node
  (equal (digit-case (digit4$node a b c d))
         4)
  :enable digit4$node)

(defruled digit->len-of-digit4$node
  (equal (digit->len (digit4$node a b c d))
         (+ (node->len a) (node->len b) (node->len c) (node->len d)))
  :enable digit4$node)

(defrule digit4->fst-of-digit4$node
  (equal (digit4->fst (digit4$node a b c d))
         (node-fix a))
  :enable digit4$node)

(defrule digit4->snd-of-digit4$node
  (equal (digit4->snd (digit4$node a b c d))
         (node-fix b))
  :enable digit4$node)

(defrule digit4->thd-of-digit4$node
  (equal (digit4->thd (digit4$node a b c d))
         (node-fix c))
  :enable digit4$node)

(defrule digit4->frth-of-digit4$node
  (equal (digit4->frth (digit4$node a b c d))
         (node-fix d))
  :enable digit4$node)

(defrule digit->len-of-digit4$node-when-digit-len-invariant-p
  (implies (digit-len-invariant-p depth (digit4$node a b c d))
           (equal (digit->len (digit4$node a b c d))
                  (digit-len depth (digit4$node a b c d))))
  :enable digit-len-invariant-p)

(defrule digit-depth-p-of-digit4$node
  (equal (digit-depth-p depth (digit4$node a b c d))
         (and (elem-depth-p depth (node-fix a))
              (elem-depth-p depth (node-fix b))
              (elem-depth-p depth (node-fix c))
              (elem-depth-p depth (node-fix d))))
  :enable digit4$node)

(defrule digit-len-invariant-p-of-digit4$node
  (implies (not (equal (nfix depth) 0))
           (equal (digit-len-invariant-p depth (digit4$node a b c d))
                  (and (elem-len-invariant-p depth (node-fix a))
                       (elem-len-invariant-p depth (node-fix b))
                       (elem-len-invariant-p depth (node-fix c))
                       (elem-len-invariant-p depth (node-fix d)))))
  :expand ((elem-len-invariant-p depth (node-fix a))
           (elem-len-invariant-p depth (node-fix b))
           (elem-len-invariant-p depth (node-fix c))
           (elem-len-invariant-p depth (node-fix d)))
  :enable digit4$node)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro digit$node (&rest args)
  (case (acl2::len args)
    (1 `(digit1$node ,@args))
    (2 `(digit2$node ,@args))
    (3 `(digit3$node ,@args))
    (4 `(digit4$node ,@args))
    (otherwise
      (er hard 'digit "Illegal number of arguments: ~x0." (acl2::len args)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define node2$ (a b)
  :returns (node nodep :rule-classes (:rewrite :type-prescription))
  (node2 2 a b)
  :inline t)

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t node2$)))

(defrule node2p-of-node2$
  (node2p (node2$ a b))
  :enable node2$)

(defrule node->len-of-node2$
  (equal (node->len (node2$ a b))
         2)
  :enable node2$)

(defrule node->fst-of-node2$
  (equal (node->fst (node2$ a b))
         a)
  :enable node2$)

(defrule node2->snd-of-node2$
  (equal (node2->snd (node2$ a b))
         b)
  :enable node2$)

(defrule elem-depth-p-of-node2$
  (equal (elem-depth-p depth (node2$ a b))
         (or (equal (nfix depth) 0)
             (and (elem-depth-p (- (nfix depth) 1) a)
                  (elem-depth-p (- (nfix depth) 1) b))))
  :enable node2$)

(defrule elem-len-invariant-p-1-of-node2$
  (elem-len-invariant-p 1 (node2$ a b))
  :enable node2$)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define node3$ (a b c)
  :returns (node nodep :rule-classes (:rewrite :type-prescription))
  (node3 3 a b c)
  :inline t)

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t node3$)))

(defrule node2p-of-node3$
  (not (node2p (node3$ a b c)))
  :enable node3$)

(defrule node->len-of-node3$
  (equal (node->len (node3$ a b c))
         3)
  :enable node3$)

(defrule node->fst-of-node3$
  (equal (node->fst (node3$ a b c))
         a)
  :enable node3$)

(defrule node3->snd-of-node3$
  (equal (node3->snd (node3$ a b c))
         b)
  :enable node3$)

(defrule node3->thd-of-node3$
  (equal (node3->thd (node3$ a b c))
         c)
  :enable node3$)

(defrule elem-depth-p-of-node3$
  (equal (elem-depth-p depth (node3$ a b c))
         (or (equal (nfix depth) 0)
             (and (elem-depth-p (- (nfix depth) 1) a)
                  (elem-depth-p (- (nfix depth) 1) b)
                  (elem-depth-p (- (nfix depth) 1) c))))
  :enable node3$)

(defrule elem-len-invariant-p-1-of-node3$
  (elem-len-invariant-p 1 (node3$ a b c))
  :enable node3$)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro node$ (&rest args)
  (case (acl2::len args)
    (2 `(node2$ ,@args))
    (3 `(node3$ ,@args))
    (otherwise
      (er hard 'node "Illegal number of arguments: ~x0." (acl2::len args)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define node2$node
  ((a nodep)
   (b nodep))
  :returns (node nodep :rule-classes (:rewrite :type-prescription))
  (node2 (+ (the unsigned-byte (node->len a))
            (the unsigned-byte (node->len b)))
         (node-fix a)
         (node-fix b))
  :inline t)

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t node2$node)))

(defrule node2$node-when-node-equal-of-arg1-congruence
  (implies (node-equal a0 a1)
           (equal (node2$node a0 b)
                  (node2$node a1 b)))
  :rule-classes :congruence
  :enable node2$node)

(defrule node2$node-when-node-equal-of-arg2-congruence
  (implies (node-equal b0 b1)
           (equal (node2$node a b0)
                  (node2$node a b1)))
  :rule-classes :congruence
  :enable node2$node)

(defrule node2p-of-node2$node
  (node2p (node2$node a b))
  :enable node2$node)

(defruled node->len-of-node2$node
  (equal (node->len (node2$node a b))
         (+ (node->len a) (node->len b)))
  :enable node2$node)

(defrule node->fst-of-node2$node
  (equal (node->fst (node2$node a b))
         (node-fix a))
  :enable node2$node)

(defrule node2->snd-of-node2$node
  (equal (node2->snd (node2$node a b))
         (node-fix b))
  :enable node2$node)

(defrule node->len-of-node2$node-when-elem-len-invariant-p
  (implies (and (elem-len-invariant-p depth (node2$node a b))
                (not (equal (nfix depth) 0)))
           (equal (node->len (node2$node a b))
                  (elem-len depth (node2$node a b))))
  :enable elem-len-invariant-p)

(defrule elem-depth-p-of-node2$node
  (equal (elem-depth-p depth (node2$node a b))
         (or (equal (nfix depth) 0)
             (and (elem-depth-p (- (nfix depth) 1) (node-fix a))
                  (elem-depth-p (- (nfix depth) 1) (node-fix b)))))
  :enable node2$node)

(defrule elem-len-invariant-p-of-node2$node
  (implies (< 1 (nfix depth))
           (equal (elem-len-invariant-p depth (node2$node a b))
                  (and (elem-len-invariant-p (- (nfix depth) 1) (node-fix a))
                       (elem-len-invariant-p (- (nfix depth) 1) (node-fix b)))))
  :expand ((elem-len-invariant-p (+ -1 depth)
                                 (node-fix a))
           (elem-len-invariant-p (+ -1 depth)
                                 (node-fix b)))
  :enable (node2$node
           nfix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define node3$node
  ((a nodep)
   (b nodep)
   (c nodep))
 :returns (node nodep :rule-classes (:rewrite :type-prescription))
 (node3 (+ (the unsigned-byte (node->len a))
           (the unsigned-byte (node->len b))
           (the unsigned-byte (node->len c)))
        (node-fix a)
        (node-fix b)
        (node-fix c))
 :inline t)

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t node3$node)))

(defrule node3$node-when-node-equal-of-arg1-congruence
  (implies (node-equal a0 a1)
           (equal (node3$node a0 b c)
                  (node3$node a1 b c)))
  :rule-classes :congruence
  :enable node3$node)

(defrule node3$node-when-node-equal-of-arg2-congruence
  (implies (node-equal b0 b1)
           (equal (node3$node a b0 c)
                  (node3$node a b1 c)))
  :rule-classes :congruence
  :enable node3$node)

(defrule node3$node-when-node-equal-of-arg3-congruence
  (implies (node-equal c0 c1)
           (equal (node3$node a b c0)
                  (node3$node a b c1)))
  :rule-classes :congruence
  :enable node3$node)

(defrule node2p-of-node3$node
  (not (node2p (node3$node a b c)))
  :enable node3$node)

(defruled node->len-of-node3$node
  (equal (node->len (node3$node a b c))
         (+ (node->len a) (node->len b) (node->len c)))
  :enable node3$node)

(defrule node->fst-of-node3$node
  (equal (node->fst (node3$node a b c))
         (node-fix a))
  :enable node3$node)

(defrule node3->snd-of-node3$node
  (equal (node3->snd (node3$node a b c))
         (node-fix b))
  :enable node3$node)

(defrule node3->thd-of-node3$node
  (equal (node3->thd (node3$node a b c))
         (node-fix c))
  :enable node3$node)

(defrule node->len-of-node3$node-when-elem-len-invariant-p
  (implies (and (elem-len-invariant-p depth (node3$node a b c))
                (not (equal (nfix depth) 0)))
           (equal (node->len (node3$node a b c))
                  (elem-len depth (node3$node a b c))))
  :enable elem-len-invariant-p)

(defrule elem-depth-p-of-node3$node
  (equal (elem-depth-p depth (node3$node a b c))
         (or (equal (nfix depth) 0)
             (and (elem-depth-p (- (nfix depth) 1) (node-fix a))
                  (elem-depth-p (- (nfix depth) 1) (node-fix b))
                  (elem-depth-p (- (nfix depth) 1) (node-fix c)))))
  :enable node3$node)

(defrule elem-len-invariant-p-of-node3$node
  (implies (< 1 (nfix depth))
           (equal (elem-len-invariant-p depth (node3$node a b c))
                  (and (elem-len-invariant-p (- (nfix depth) 1) (node-fix a))
                       (elem-len-invariant-p (- (nfix depth) 1) (node-fix b))
                       (elem-len-invariant-p (- (nfix depth) 1) (node-fix c)))))
  :expand ((elem-len-invariant-p (+ -1 depth)
                                 (node-fix a))
           (elem-len-invariant-p (+ -1 depth)
                                 (node-fix b))
           (elem-len-invariant-p (+ -1 depth)
                                 (node-fix c)))
  :enable (node3$node
           nfix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro node$node (&rest args)
  (case (acl2::len args)
    (2 `(node2$node ,@args))
    (3 `(node3$node ,@args))
    (otherwise
      (er hard 'node "Illegal number of arguments: ~x0." (acl2::len args)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ftree-deep$
  ((prefix digitp)
   (middle ftreep)
   (suffix digitp))
  :guard (ftree-depth-p 1 middle)
  :returns (tree ftreep)
  (ftree-deep (+ (the unsigned-byte (digit->len prefix))
                 (the unsigned-byte (digit->len suffix))
                 (the unsigned-byte
                   (cond ((ftree-empty-p middle)
                          0)
                         ((ftree-single-p middle)
                          (node->len (ftree-single->elem middle)))
                         (t
                          (ftree-deep->len middle)))))
              prefix
              middle
              suffix)
  :inline t)

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t ftree-deep$)))

(defrule ftree-deep$-type-prescription
  (consp (ftree-deep$ prefix middle suffix))
  :rule-classes :type-prescription
  :enable ftree-deep$)

(defrule
ftree-deep$-when-digit-equal-of-arg2-congruence
  (implies (digit-equal prefix0 prefix1)
           (equal (ftree-deep$ prefix0 middle suffix)
                  (ftree-deep$ prefix1 middle suffix)))
  :rule-classes :congruence
  :enable ftree-deep$)

(defrule ftree-deep$-when-ftree-equal-congruence
  (implies (ftree-equal middle0 middle1)
           (equal (ftree-deep$ prefix middle0 suffix)
                  (ftree-deep$ prefix middle1 suffix)))
  :rule-classes :congruence
  :enable ftree-deep$)

(defrule ftree-deep$-when-digit-equal-of-arg4-congruence
  (implies (digit-equal suffix0 suffix1)
           (equal (ftree-deep$ prefix middle suffix0)
                  (ftree-deep$ prefix middle suffix1)))
  :rule-classes :congruence
  :enable ftree-deep$)

(defrule ftree-empty-p-of-ftree-deep$
  (not (ftree-empty-p (ftree-deep$ prefix middle suffix)))
  :enable ftree-deep$)

(defrule ftree-single-p-of-ftree-deep$
  (not (ftree-single-p (ftree-deep$ prefix middle suffix)))
  :enable ftree-deep$)

(defrule ftree-deep->len-of-ftree-deep$
  (equal (ftree-deep->len (ftree-deep$ prefix middle suffix))
         (+ (digit->len prefix)
            (digit->len suffix)
            (cond ((ftree-empty-p middle)
                   0)
                  ((ftree-single-p middle)
                   (node->len (ftree-single->elem middle)))
                  (t
                   (ftree-deep->len middle)))))
  :enable ftree-deep$)

(defrule ftree-deep->prefix-of-ftree-deep$
  (equal (ftree-deep->prefix (ftree-deep$ prefix middle suffix))
         (digit-fix prefix))
  :enable ftree-deep$)

(defrule ftree-deep->middle-of-ftree-deep$
  (equal (ftree-deep->middle (ftree-deep$ prefix middle suffix))
         (ftree-fix middle))
  :enable ftree-deep$)

(defrule ftree-deep->suffix-of-ftree-deep$
  (equal (ftree-deep->suffix (ftree-deep$ prefix middle suffix))
         (digit-fix suffix))
  :enable ftree-deep$)

(defrule ftree-depth-p-of-ftree-deep$
  (equal (ftree-depth-p depth (ftree-deep$ prefix middle suffix))
         (and (digit-depth-p depth prefix)
              (ftree-depth-p (+ (nat-fix depth) 1) middle)
              (digit-depth-p depth suffix)))
  :enable ftree-deep$)

;; TODO: similar rules for other smart constructors
(defrule ftree-len-of-ftree-deep$
  (equal (ftree-len depth (ftree-deep$ prefix middle suffix))
         (+ (digit-len depth prefix)
            (ftree-len (+ (nat-fix depth) 1) middle)
            (digit-len depth suffix)))
  :enable ftree-deep$)

(defrule ftree-len-invariant-p-of-ftree-deep$
  (equal (ftree-len-invariant-p depth (ftree-deep$ prefix middle suffix))
         (and (digit-len-invariant-p depth prefix)
              (digit-len-invariant-p depth suffix)
              (ftree-len-invariant-p (+ (nfix depth) 1) middle)))
  :enable ftree-deep$)
