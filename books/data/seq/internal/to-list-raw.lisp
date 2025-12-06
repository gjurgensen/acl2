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
(include-book "data/utilities/true-list-defs" :dir :system)

(include-book "drop-defs")
(include-book "front-back-defs")
(include-book "pop-defs")
(include-book "push-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(local (include-book "data/utilities/nat" :dir :system))
(local (include-book "data/utilities/true-list" :dir :system))

(local (include-book "kestrel/arithmetic-light/fix" :dir :system))
(local (include-book "kestrel/lists-light/append" :dir :system))
(local (include-book "kestrel/utilities/ordinals" :dir :system))

(local (include-book "drop"))
(local (include-book "front-back"))
(local (include-book "ftree"))
(local (include-book "pop"))
(local (include-book "push"))
(local (include-book "well-formed-p"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define node-to-list-with-depth-acc
  ((depth natp)
   (node? (node?-depth-p depth node?))
   (acc true-listp))
  :returns (list true-listp :rule-classes (:rewrite :type-prescription))
  (if (nat-equal depth 0)
      (cons node? (data::list-fix acc))
    (let ((depth$ (- (nat-fix depth) 1)))
      (node-to-list-with-depth-acc
        depth$
        (node->fst node?)
        (node-to-list-with-depth-acc
          depth$
          (node->snd node?)
          (if (node2p node?)
              acc
            (node-to-list-with-depth-acc
              depth$
              (node->thd node?)
              acc))))))
  :measure (nfix depth))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t node-to-list-with-depth-acc)))

(defrule node-to-list-with-depth-acc-when-nat-equiv-congruence
  (implies (nat-equiv depth0 depth1)
           (equal (node-to-list-with-depth-acc depth0 node? acc)
                  (node-to-list-with-depth-acc depth1 node? acc)))
  :rule-classes :congruence
  :enable (node-to-list-with-depth-acc
           nfix))

(defrule node-to-list-with-depth-acc-when-list-equiv-congruence
  (implies (list-equiv acc0 acc1)
           (equal (node-to-list-with-depth-acc depth node? acc0)
                  (node-to-list-with-depth-acc depth node? acc1)))
  :rule-classes :congruence
  :induct t
  :enable node-to-list-with-depth-acc)

(defruledl node-to-list-with-depth-acc-of-append
  (implies (true-listp y)
           (equal (node-to-list-with-depth-acc depth node? (append x y))
                  (append (node-to-list-with-depth-acc depth node? x)
                          y)))
  :induct t
  :enable (node-to-list-with-depth-acc
           nfix))

(defruledl node-to-list-with-depth-acc-arg3-becomes-nil
  (equal (node-to-list-with-depth-acc depth node? acc)
         (append (node-to-list-with-depth-acc depth node? nil)
                 (true-list-fix acc)))
  :use ((:instance node-to-list-with-depth-acc-of-append
                   (x nil)
                   (y (true-list-fix acc)))))

(defrule node-to-list-with-depth-acc-arg3-becomes-nil-syntaxp
  (implies (syntaxp (not (equal acc ''nil)))
           (equal (node-to-list-with-depth-acc depth node? acc)
                  (append (node-to-list-with-depth-acc depth node? nil)
                          (true-list-fix acc))))
  :by node-to-list-with-depth-acc-arg3-becomes-nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define node-to-list-with-depth
  ((depth natp)
   (node? (node?-depth-p depth node?)))
  :returns (list true-listp :rule-classes (:rewrite :type-prescription))
  (mbe :logic
       (if (equal (nfix depth) 0)
           (list node?)
         (let ((depth$ (- (nfix depth) 1)))
           (append (node-to-list-with-depth depth$ (node->fst node?))
                   (if (node2p node?)
                       (node-to-list-with-depth depth$ (node->snd node?))
                     (append
                       (node-to-list-with-depth depth$ (node->snd node?))
                       (node-to-list-with-depth depth$ (node->thd node?)))))))
       :exec (node-to-list-with-depth-acc depth node? nil))
  :inline t
  :measure (nfix depth)
  ;; Verified below
  :verify-guards nil)

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t node-to-list-with-depth)))

(defrule node-to-list-with-depth-when-nat-equiv-congruence
  (implies (nat-equiv depth0 depth1)
           (equal (node-to-list-with-depth depth0 node?)
                  (node-to-list-with-depth depth1 node?)))
  :rule-classes :congruence
  :enable (node-to-list-with-depth
           nfix))

(defruled node-to-list-with-depth-becomes-exec
  (equal (node-to-list-with-depth depth node?)
         (node-to-list-with-depth-acc depth node? nil))
  :induct t
  :expand (node-to-list-with-depth-acc depth node? nil)
  :enable node-to-list-with-depth)

(verify-guards node-to-list-with-depth$inline
  :hints (("Goal" :in-theory (enable node-to-list-with-depth)
                  :use node-to-list-with-depth-becomes-exec)))

;; (defruled node-to-list-with-depth-when-not-natp-of-arg1
;;   (implies))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define digit-to-list-with-depth-acc
  ((depth natp)
   (digit digitp)
   (acc true-listp))
  :guard (digit-depth-p depth digit)
  :returns (list true-listp :rule-classes (:rewrite :type-prescription))
  (case (digit-case digit)
    (1 (node-to-list-with-depth-acc depth (digit->fst digit) acc))
    (2 (node-to-list-with-depth-acc
         depth
         (digit->fst digit)
         (node-to-list-with-depth-acc depth (digit->snd digit) acc)))
    (3 (node-to-list-with-depth-acc
         depth
         (digit->fst digit)
         (node-to-list-with-depth-acc
           depth
           (digit->snd digit)
           (node-to-list-with-depth-acc depth (digit->thd digit) acc))))
    (4 (node-to-list-with-depth-acc
         depth
         (digit->fst digit)
         (node-to-list-with-depth-acc
           depth
           (digit->snd digit)
           (node-to-list-with-depth-acc
             depth
             (digit->thd digit)
             (node-to-list-with-depth-acc depth (digit->frth digit) acc)))))
    (otherwise (the nil nil))))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t digit-to-list-with-depth-acc)))

(defrule digit-to-list-with-depth-acc-when-nat-equiv-congruence
  (implies (nat-equiv depth0 depth1)
           (equal (digit-to-list-with-depth-acc depth0 node? acc)
                  (digit-to-list-with-depth-acc depth1 node? acc)))
  :rule-classes :congruence
  :enable digit-to-list-with-depth-acc
  :disable acl2::nat-equiv$inline)

(defrule digit-to-list-with-depth-acc-when-list-equiv-congruence
  (implies (list-equiv acc0 acc1)
           (equal (digit-to-list-with-depth-acc depth digit acc0)
                  (digit-to-list-with-depth-acc depth digit acc1)))
  :rule-classes :congruence
  :enable digit-to-list-with-depth-acc)

(defruledl digit-to-list-with-depth-acc-of-append
  (implies (true-listp y)
           (equal (digit-to-list-with-depth-acc depth digit (append x y))
                  (append (digit-to-list-with-depth-acc depth digit x)
                          y)))
  :enable digit-to-list-with-depth-acc)

(defruledl digit-to-list-with-depth-acc-arg3-becomes-nil
  (equal (digit-to-list-with-depth-acc depth digit acc)
         (append (digit-to-list-with-depth-acc depth digit nil)
                 (true-list-fix acc)))
  :use ((:instance digit-to-list-with-depth-acc-of-append
                   (x nil)
                   (y (true-list-fix acc)))))

(defrule digit-to-list-with-depth-acc-arg3-becomes-nil-syntaxp
  (implies (syntaxp (not (equal acc ''nil)))
           (equal (digit-to-list-with-depth-acc depth digit acc)
                  (append (digit-to-list-with-depth-acc depth digit nil)
                          (true-list-fix acc))))
  :by digit-to-list-with-depth-acc-arg3-becomes-nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define digit-to-list-with-depth
  ((depth natp)
   (digit digitp))
  :guard (digit-depth-p depth digit)
  :returns (list true-listp :rule-classes (:rewrite :type-prescription))
  (mbe :logic
       (case (digit-case digit)
         (1 (node-to-list-with-depth depth (digit->fst digit)))
         (2 (append (node-to-list-with-depth depth (digit->fst digit))
                    (node-to-list-with-depth depth (digit->snd digit))))
         (3 (append (node-to-list-with-depth depth (digit->fst digit))
                    (node-to-list-with-depth depth (digit->snd digit))
                    (node-to-list-with-depth depth (digit->thd digit))))
         (4 (append (node-to-list-with-depth depth (digit->fst digit))
                    (node-to-list-with-depth depth (digit->snd digit))
                    (node-to-list-with-depth depth (digit->thd digit))
                    (node-to-list-with-depth depth (digit->frth digit))))
         (otherwise nil))
       :exec (digit-to-list-with-depth-acc depth digit nil))
  :inline t
  ;; Verified below
  :verify-guards nil)

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t digit-to-list-with-depth)))

(defrule digit-to-list-with-depth-when-nat-equiv-congruence
  (implies (nat-equiv depth0 depth1)
           (equal (digit-to-list-with-depth depth0 digit)
                  (digit-to-list-with-depth depth1 digit)))
  :rule-classes :congruence
  :enable digit-to-list-with-depth
  :disable acl2::nat-equiv$inline)

(defrule digit-to-list-with-depth-when-digit-equal-congruence
  (implies (digit-equal digit0 digit1)
           (equal (digit-to-list-with-depth depth digit0)
                  (digit-to-list-with-depth depth digit1)))
  :rule-classes :congruence
  :enable digit-to-list-with-depth)

(defruled digit-to-list-with-depth-becomes-exec
  (equal (digit-to-list-with-depth depth digit)
         (digit-to-list-with-depth-acc depth digit nil))
  :enable (digit-to-list-with-depth
           digit-to-list-with-depth-acc
           node-to-list-with-depth-becomes-exec))

(verify-guards digit-to-list-with-depth$inline
  :hints (("Goal" :in-theory (enable digit-to-list-with-depth)
                  :use digit-to-list-with-depth-becomes-exec)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ftree-to-list-with-depth-acc
  ((depth natp)
   (tree ftreep)
   (acc true-listp))
  :guard (ftree-well-formed-p depth tree)
  :returns (list true-listp :rule-classes (:rewrite :type-prescription))
  (cond ((ftree-empty-p tree)
         (data::list-fix acc))
        ((ftree-single-p tree)
         (node-to-list-with-depth-acc depth (ftree-single->elem tree) acc))
        (t
         (digit-to-list-with-depth-acc
           depth
           (ftree-deep->prefix tree)
           (ftree-to-list-with-depth-acc
             (+ (nat-fix depth) 1)
             (ftree-deep->middle tree)
             (digit-to-list-with-depth-acc
               depth
               (ftree-deep->suffix tree)
               acc))))))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t ftree-to-list-with-depth-acc)))

(defrule ftree-to-list-with-depth-acc-when-nat-equiv-congruence
  (implies (nat-equiv depth0 depth1)
           (equal (ftree-to-list-with-depth-acc depth0 tree acc)
                  (ftree-to-list-with-depth-acc depth1 tree acc)))
  :rule-classes :congruence
  :expand ((ftree-to-list-with-depth-acc depth0 tree acc)
           (ftree-to-list-with-depth-acc depth1 tree acc))
  :disable acl2::nat-equiv$inline)

(defrule ftree-to-list-with-depth-acc-when-ftree-equiv-congruence
  (implies (ftree-equal tree0 tree1)
           (equal (ftree-to-list-with-depth-acc depth tree0 acc)
                  (ftree-to-list-with-depth-acc depth tree1 acc)))
  :rule-classes :congruence
  :expand ((ftree-to-list-with-depth-acc depth tree0 acc)
           (ftree-to-list-with-depth-acc depth tree1 acc)))

(defrule ftree-to-list-with-depth-acc-when-list-equiv-congruence
  (implies (list-equiv acc0 acc1)
           (equal (ftree-to-list-with-depth-acc depth tree acc0)
                  (ftree-to-list-with-depth-acc depth tree acc1)))
  :rule-classes :congruence
  :expand ((ftree-to-list-with-depth-acc depth tree acc0)
           (ftree-to-list-with-depth-acc depth tree acc1)))

(defruledl ftree-to-list-with-depth-acc-of-append
  (implies (true-listp y)
           (equal (ftree-to-list-with-depth-acc depth tree (append x y))
                  (append (ftree-to-list-with-depth-acc depth tree x)
                          y)))
  :induct t
  :enable (ftree-to-list-with-depth-acc
           nfix))

(defruledl ftree-to-list-with-depth-acc-arg3-becomes-nil
  (equal (ftree-to-list-with-depth-acc depth tree acc)
         (append (ftree-to-list-with-depth-acc depth tree nil)
                 (true-list-fix acc)))
  :use ((:instance ftree-to-list-with-depth-acc-of-append
                   (x nil)
                   (y (true-list-fix acc)))))

(defrule ftree-to-list-with-depth-acc-arg3-becomes-nil-syntaxp
  (implies (syntaxp (not (equal acc ''nil)))
           (equal (ftree-to-list-with-depth-acc depth tree acc)
                  (append (ftree-to-list-with-depth-acc depth tree nil)
                          (true-list-fix acc))))
  :by ftree-to-list-with-depth-acc-arg3-becomes-nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ftree-to-list-with-depth
  ((depth natp)
   (tree ftreep))
  :guard (ftree-well-formed-p depth tree)
  :returns (list true-listp :rule-classes (:rewrite :type-prescription))
  (mbe :logic
       (cond ((ftree-empty-p tree)
              nil)
             ((ftree-single-p tree)
              (node-to-list-with-depth depth (ftree-single->elem tree)))
             (t
              (append
                (digit-to-list-with-depth depth (ftree-deep->prefix tree))
                (ftree-to-list-with-depth (+ (nfix depth) 1)
                                          (ftree-deep->middle tree))
                (digit-to-list-with-depth depth (ftree-deep->suffix tree)))))
       :exec (ftree-to-list-with-depth-acc depth tree nil))
  :inline t
  ;; Verified below
  :verify-guards nil)

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t ftree-to-list-with-depth)))

(defrule ftreee-to-list-with-depth-when-nat-equiv-congruence
  (implies (nat-equiv depth0 depth1)
           (equal (ftree-to-list-with-depth depth0 tree)
                  (ftree-to-list-with-depth depth1 tree)))
  :rule-classes :congruence
  :expand ((ftree-to-list-with-depth depth0 tree)
           (ftree-to-list-with-depth depth1 tree))
  :disable acl2::nat-equiv$inline)

(defrule ftree-to-list-with-depth-when-ftree-equal-congruence
  (implies (ftree-equal tree0 tree1)
           (equal (ftree-to-list-with-depth depth tree0)
                  (ftree-to-list-with-depth depth tree1)))
  :rule-classes :congruence
  :expand ((ftree-to-list-with-depth depth tree0)
           (ftree-to-list-with-depth depth tree1)))

(defruled ftree-to-list-with-depth-becomes-exec
  (equal (ftree-to-list-with-depth depth tree)
         (ftree-to-list-with-depth-acc depth tree nil))
  :induct t
  :enable (ftree-to-list-with-depth
           ftree-to-list-with-depth-acc
           digit-to-list-with-depth-becomes-exec
           node-to-list-with-depth-becomes-exec))

(verify-guards ftree-to-list-with-depth$inline
  :hints (("Goal" :in-theory (enable ftree-to-list-with-depth)
                  :use ftree-to-list-with-depth-becomes-exec)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; TODO: front of to-list is car, push is cons, etc.

(defrule car-of-ftree-to-list-with-depth-of-0
  (equal (car (ftree-to-list-with-depth 0 tree))
         (ftree-front tree))
  :enable (ftree-front
           ftree-to-list-with-depth
           node-to-list-with-depth
           digit-to-list-with-depth))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule cdr-of-digit-to-list-with-depth
  (equal (cdr (digit-to-list-with-depth depth digit))
         (digit-to-list depth (digit-tail digit))))

(defrule ftree-to-list-with-depth-of-mv-nth-1-of-ftree-pop-front
  (equal (ftree-to-list-with-depth depth (mv-nth 1 (ftree-pop-front tree)))
         (cdr (ftree-to-list-with-depth depth tree)))
  ;; :induct t
  :induct (ftree-pop-front tree)
  :expand ((ftree-to-list-with-depth (+ 1 (nfix depth))
                                     (ftree-deep->middle tree))
           (ftree-to-list-with-depth depth tree)
           )
  :enable (ftree-to-list-with-depth
           ftree-pop-front
           ;; nfix
           ))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; TODO: equiv definition which doesn't do too much consing and can short
;; circuit.
;; This is a little more complicated by the fact that the structure may be
;; different.
;; May need to keep a backlog when one tree gets "ahead" of the other.
