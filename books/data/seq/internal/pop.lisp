; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "SEQ")

(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)

(include-book "front-back-defs")
(include-book "ftree-defs")
(include-book "well-formed-p-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(local (include-book "kestrel/utilities/ordinals" :dir :system))

(local (include-book "front-back"))
(local (include-book "ftree"))
(local (include-book "well-formed-p"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define digit-tail
  ((digit digitp))
  (case (digit-case digit)
    (1 nil)
    (2 (digit (digit->snd digit)))
    (3 (digit (digit->snd digit) (digit->thd digit)))
    (4 (digit (digit->snd digit) (digit->thd digit) (digit->frth digit)))
    (otherwise (the nil (digit-fix digit))))
  :inline t)

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t digit-tail)))

(defrule digit-tail-type-prescription
  (or (consp (digit-tail digit))
      (equal (digit-tail digit) nil))
  :rule-classes :type-prescription
  :enable digit-tail)

(defrule digit-tail-when-digit-equal-congruence
  (implies (digit-equal digit0 digit1)
           (equal (digit-tail digit0)
                  (digit-tail digit1)))
  :rule-classes :congruence
  :enable digit-tail)

(defrule digitp-of-digit-tail
  (equal (digitp (digit-tail digit))
         (not (equal (digit-case digit) 1)))
  :enable digit-tail)

(defrule digit-tail-under-iff
  (iff (digit-tail digit)
       (not (equal (digit-case digit) 1)))
  :enable digit-tail)

(defrule digit-depth-p-of-digit-tail
  (implies (and (not (equal (digit-case digit) 1))
                (digit-depth-p depth digit))
           (digit-depth-p depth (digit-tail digit)))
  :enable digit-tail)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define digit-to-ftree
  ((digit digitp))
  :returns (tree ftreep)
  (case (digit-case digit)
    (1 (ftree-single (digit->fst digit)))
    (2 (ftree-deep (digit (digit->fst digit))
                   nil
                   (digit (digit->snd digit))))
    (3 (ftree-deep (digit (digit->fst digit)
                          (digit->snd digit))
                   nil
                   (digit (digit->thd digit))))
    ;; (4 (ftree-deep (digit (digit->fst digit)
    ;;                       (digit->snd digit)
    ;;                       (digit->thd digit))
    ;;                nil
    ;;                (digit (digit->frth digit))))
    (4 (ftree-deep (digit (digit->fst digit)
                          (digit->snd digit))
                   nil
                   (digit (digit->thd digit)
                          (digit->frth digit))))
    (otherwise (the nil (digit-fix digit)))))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t digit-to-ftree)))

(defrule digit-to-ftree-type-prescription
  (consp (digit-to-ftree digit))
  :rule-classes :type-prescription
  :enable digit-to-ftree)

(defrule digit-to-ftree-when-digit-equal-congruence
  (implies (digit-equal digit0 digit1)
           (equal (digit-to-ftree digit0)
                  (digit-to-ftree digit1)))
  :rule-classes :congruence
  :enable digit-to-ftree)

(defrule ftree-empty-p-of-digit-to-ftree
  (not (ftree-empty-p (digit-to-ftree digit)))
  :enable digit-to-ftree)

(defrule ftree-well-formedp-of-digit-to-ftree
  (implies (digit-depth-p depth digit)
           (ftree-well-formed-p depth (digit-to-ftree digit)))
  :enable digit-to-ftree)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ftree-pop-front ((tree ftreep))
  :guard (not (ftree-empty-p tree))
  :returns (mv front
               (tree$ ftreep :rule-classes (:rewrite :type-prescription)))
  (mbe :logic (mv (ftree-front tree)
                  (if (mbt (not (ftree-empty-p tree)))
                      (if (ftree-single-p tree)
                          nil
                        (let* ((prefix (ftree-deep->prefix tree))
                               (tail-prefix? (digit-tail prefix))
                               (middle (ftree-deep->middle tree)))
                          (if tail-prefix?
                              (ftree-deep tail-prefix?
                                          middle
                                          (ftree-deep->suffix tree))
                            (if (ftree-empty-p middle)
                                (digit-to-ftree (ftree-deep->suffix tree))
                              (mv-let (front$ middle$)
                                      (ftree-pop-front middle)
                                (ftree-deep (digit front$)
                                            middle$
                                            (ftree-deep->suffix tree)))))))
                    (ftree-fix tree)))
       :exec (if (ftree-single-p tree)
                 (mv (ftree-single->elem tree) nil)
               (let* ((prefix (ftree-deep->prefix tree))
                      (tail-prefix? (digit-tail prefix))
                      (middle (ftree-deep->middle tree)))
                 (mv (digit->fst prefix)
                     (if tail-prefix?
                         (ftree-deep tail-prefix?
                                     middle
                                     (ftree-deep->suffix tree))
                       (if (ftree-empty-p middle)
                           (digit-to-ftree (ftree-deep->suffix tree))
                         (mv-let (front$ middle$)
                                 (ftree-pop-front middle)
                           (ftree-deep (digit front$)
                                       middle$
                                       (ftree-deep->suffix tree)))))))))
  ;; Ruler extender is necessary because the recursion is occurring in an
  ;; argument to `mv` (logically just `cons`).
  :ruler-extenders (cons)
  :verify-guards :after-returns
  :guard-hints (("Goal" :in-theory (enable ftree-front))))

;;;;;;;;;;;;;;;;;;;;

(defrule ftree-pop-front-when-ftree-equal-congruence
  (implies (ftree-equal tree0 tree1)
           (equal (ftree-pop-front tree0)
                  (ftree-pop-front tree1)))
  :rule-classes :congruence
  :expand ((ftree-pop-front tree0)
           (ftree-pop-front tree1)))

(defrule mv-nth-0-of-ftree-pop-front
  (equal (mv-nth 0 (ftree-pop-front tree))
         (ftree-front tree))
  :expand (ftree-pop-front tree))

(defrule ftree-well-formed-p-of-ftree-pop-front
  (implies (and (ftree-well-formed-p depth tree)
                (not (ftree-empty-p tree)))
           (ftree-well-formed-p depth (mv-nth 1 (ftree-pop-front tree))))
  :induct t
  :enable (ftree-pop-front
           ftree-front
           ftree-well-formed-p
           nfix))

(defrule ftree-well-formed-p-0-of-ftree-pop-front
  (implies (ftree-well-formed-p 0 tree)
           (ftree-well-formed-p 0 (mv-nth 1 (ftree-pop-front tree))))
  :cases ((ftree-empty-p tree))
  :enable ftree-pop-front)

(defrule acl2-count-when-not-ftree-empty-p-and-not-ftree-single-p
  (implies (and (not (ftree-empty-p tree))
                (not (ftree-single-p tree)))
           (equal (acl2-count tree)
                  (+ 3
                     (acl2-count (ftree-deep->prefix tree))
                     (acl2-count (ftree-deep->middle tree))
                     (acl2-count (ftree-deep->suffix tree)))))
  :rule-classes ((:rewrite :backchain-limit-lst (0 0)))
  :use ftree-deep-elim
  :disable ftree-deep-elim
  :prep-lemmas
  ((defrule acl2-count-of-ftree-deep
     (equal (acl2-count (ftree-deep prefix middle suffix))
            (+ 3
               (acl2-count (digit-fix prefix))
               (acl2-count (ftree-fix middle))
               (acl2-count (digit-fix suffix))))
     :enable (acl2-count
              ftree-deep
              fix))))

(defrule acl2-count-of-ftree-deep->prefix-linear
  (implies (and (not (ftree-empty-p tree))
                (not (ftree-single-p tree)))
           (< (acl2-count (ftree-deep->prefix tree))
              (acl2-count tree)))
  :rule-classes :linear)

(defrule acl2-count-of-ftree-deep->middle-linear
  (implies (and (not (ftree-empty-p tree))
                (not (ftree-single-p tree)))
           (< (acl2-count (ftree-deep->middle tree))
              (acl2-count tree)))
  :rule-classes :linear)

(defrule acl2-count-of-ftree-deep->suffix-linear
  (implies (and (not (ftree-empty-p tree))
                (not (ftree-single-p tree)))
           (< (acl2-count (ftree-deep->suffix tree))
              (acl2-count tree)))
  :rule-classes :linear)

(local (include-book "kestrel/arithmetic-light/top" :dir :system))

(defrule acl2-count-of-ftree-pop-front-linear
  (implies (not (ftree-empty-p tree))
           (< (acl2-count (ftree-pop-front tree))
              (acl2-count tree)))
  :rule-classes :linear
  :induct t
  :enable (ftree-pop-front
           acl2-count
           fix
           ))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define digit-liat
  ((digit digitp))
  (case (digit-case digit)
    (1 nil)
    (2 (digit (digit->fst digit)))
    (3 (digit (digit->fst digit) (digit->snd digit)))
    (4 (digit (digit->fst digit) (digit->snd digit) (digit->thd digit)))
    (otherwise (the nil (digit-fix digit))))
  :inline t)

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t digit-liat)))

(defrule digit-liat-type-prescription
  (or (consp (digit-liat digit))
      (equal (digit-liat digit) nil))
  :rule-classes :type-prescription
  :enable digit-liat)

(defrule digit-liat-when-digit-equal-congruence
  (implies (digit-equal digit0 digit1)
           (equal (digit-liat digit0)
                  (digit-liat digit1)))
  :rule-classes :congruence
  :enable digit-liat)

(defrule digitp-of-digit-liat
  (equal (digitp (digit-liat digit))
         (not (equal (digit-case digit) 1)))
  :enable digit-liat)

(defrule digit-liat-under-iff
  (iff (digit-liat digit)
       (not (equal (digit-case digit) 1)))
  :enable digit-liat)

(defrule digit-depth-p-of-digit-liat
  (implies (and (not (equal (digit-case digit) 1))
                (digit-depth-p depth digit))
           (digit-depth-p depth (digit-liat digit)))
  :enable digit-liat)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; TODO

(define ftree-pop-back ((tree ftreep))
  :guard (not (ftree-empty-p tree))
  :returns (mv back
               (tree$ ftreep :rule-classes (:rewrite :type-prescription)))
  (mbe :logic (mv (ftree-back tree)
                  (if (mbt (not (ftree-empty-p tree)))
                      (if (ftree-single-p tree)
                          nil
                        (let* ((suffix (ftree-deep->suffix tree))
                               (liat-suffix? (digit-liat suffix))
                               (middle (ftree-deep->middle tree)))
                          (if liat-suffix?
                              (ftree-deep (ftree-deep->prefix tree)
                                          middle
                                          liat-suffix?)
                            (if (ftree-empty-p middle)
                                (digit-to-ftree (ftree-deep->prefix tree))
                              (mv-let (back$ middle$)
                                      (ftree-pop-back middle)
                                (ftree-deep (ftree-deep->prefix tree)
                                            middle$
                                            (digit back$)))))))
                    (ftree-fix tree)))
       :exec (if (ftree-single-p tree)
                 (mv (ftree-single->elem tree) nil)
               (let* ((suffix (ftree-deep->suffix tree))
                      (liat-suffix? (digit-liat suffix))
                      (middle (ftree-deep->middle tree)))
                 (mv (digit->last suffix)
                     (if liat-suffix?
                         (ftree-deep (ftree-deep->prefix tree)
                                     middle
                                     liat-suffix?)
                       (if (ftree-empty-p middle)
                           (digit-to-ftree (ftree-deep->prefix tree))
                         (mv-let (back$ middle$)
                                 (ftree-pop-back middle)
                           (ftree-deep (ftree-deep->prefix tree)
                                       middle$
                                       (digit back$)))))))))
  ;; Ruler extender is necessary because the recursion is occurring in an
  ;; argument to `mv` (logically just `cons`).
  :ruler-extenders (cons)
  :verify-guards :after-returns
  :guard-hints (("Goal" :in-theory (enable ftree-back))))

;;;;;;;;;;;;;;;;;;;;

(defrule ftree-pop-back-when-ftree-equal-congruence
  (implies (ftree-equal tree0 tree1)
           (equal (ftree-pop-back tree0)
                  (ftree-pop-back tree1)))
  :rule-classes :congruence
  :expand ((ftree-pop-back tree0)
           (ftree-pop-back tree1)))

(defrule mv-nth-0-of-ftree-pop-back
  (equal (mv-nth 0 (ftree-pop-back tree))
         (ftree-back tree))
  :expand (ftree-pop-back tree))

(defrule ftree-well-formed-p-of-ftree-pop-back
  (implies (and (ftree-well-formed-p depth tree)
                (not (ftree-empty-p tree)))
           (ftree-well-formed-p depth (mv-nth 1 (ftree-pop-back tree))))
  :induct t
  :enable (ftree-pop-back
           ftree-back
           ftree-well-formed-p
           nfix
           digit->last))

(defrule ftree-well-formed-p-0-of-ftree-pop-back
  (implies (ftree-well-formed-p 0 tree)
           (ftree-well-formed-p 0 (mv-nth 1 (ftree-pop-back tree))))
  :cases ((ftree-empty-p tree))
  :enable ftree-pop-back)
