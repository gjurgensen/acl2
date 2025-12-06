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

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(local (include-book "kestrel/utilities/ordinals" :dir :system))

(local (include-book "data/utilities/nat" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Reference implementation
;; https://hackage.haskell.org/package/containers-0.6.0.1/docs/src/Data.Sequence.Internal.html#FingerTree

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; digit1: (1 . (len . a))
;; digit2: (2 . (len . (a . b)))
;; digit3: (3 . (len . ((a . b) . c)))
;; digit4: (4 . (len . ((a . b) . (c . d))))

;; TODO: consider dropping len field
(define digitp (x)
  :returns (yes/no booleanp :rule-classes (:rewrite :type-prescription))
  (and (consp x)
       (consp (cdr x))
       (natp (cadr x))
       (let ((count (car x)))
         (or (eql count 1)
             (and (consp (cddr x))
                  (or (eql count 2)
                      (and (consp (caddr x))
                           (or (eql count 3)
                               (and (consp (cdddr x))
                                    (eql count 4))))))))))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t digitp)))

(defrule digitp-compound-recognizer
  (implies (digitp x)
           (consp x))
  :rule-classes :compound-recognizer
  :enable digitp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define irr-digit ()
  :returns (digit$ digitp :rule-classes (:rewrite :type-prescription))
  (list 1 1 nil))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t irr-digit) (:e irr-digit)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define digit-fix ((digit digitp))
  :returns (digit$ digitp :rule-classes (:rewrite :type-prescription))
  (mbe :logic (if (digitp digit)
                  digit
                (irr-digit))
       :exec (the cons digit))
  :inline t)

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t digit-fix)))

(defrule digit-fix-when-digitp
  (implies (digitp digit)
           (equal (digit-fix digit)
                  digit))
  :enable digit-fix)

(defruled digit-fix-when-not-digitp
  (implies (not (digitp digit))
           (equal (digit-fix digit)
                  (irr-digit)))
  :enable digit-fix)

(defrule digit-fix-when-not-digitp-cheap
  (implies (not (digitp digit))
           (equal (digit-fix digit)
                  (irr-digit)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by digit-fix-when-not-digitp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define digit-equal ((x digitp) (y digitp))
  :returns (yes/no booleanp :rule-classes (:rewrite :type-prescription))
  (mbe :logic (equal (digit-fix x) (digit-fix y))
       :exec (and (= (the (integer 1 4) (car x)) (the (integer 1 4) (car y)))
                  (= (the unsigned-byte (cadr x)) (the unsigned-byte (cadr y)))
                  ;; TODO: optimize
                  (equal (cddr x) (cddr y))))
  :inline t
  :guard-hints (("Goal" :in-theory (enable digitp))))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t digit-equal)))

(defequiv digit-equal
  :hints (("Goal" :in-theory (enable digit-equal))))

(defrule digit-fix-when-digit-equal-congruence
  (implies (digit-equal digit0 digit1)
           (equal (digit-fix digit0)
                  (digit-fix digit1)))
  :rule-classes :congruence
  :enable digit-equal)

(defrule digit-fix-under-digit-equal
  (digit-equal (digit-fix digit)
               digit)
  :enable digit-equal)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define digit-case ((digit digitp))
  :returns (case posp
                 :rule-classes :type-prescription
                 :hints (("Goal" :in-theory (enable digit-fix
                                                    digitp
                                                    irr-digit))))
  (the (integer 1 4) (car (digit-fix digit)))
  :inline t
  :guard-hints (("Goal" :in-theory (enable digitp))))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t digit-case)))

(defrule digit-case-when-digit-equal-congruence
  (implies (digit-equal digit0 digit1)
           (equal (digit-case digit0)
                  (digit-case digit1)))
  :rule-classes :congruence
  :enable digit-case)

(defrule digit-case-max-linear
  (<= (digit-case digit)
      4)
  :rule-classes :linear
  :enable (digit-case
           digit-fix
           digitp
           irr-digit))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define digit->len ((digit digitp))
  :returns (len natp
                :rule-classes :type-prescription
                :hints (("Goal" :in-theory (enable digit-fix
                                                   digitp
                                                   irr-digit))))
  (the unsigned-byte (cadr (digit-fix digit)))
  :inline t
  :guard-hints (("Goal" :in-theory (enable digitp))))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t digit->len)))

(defrule digit->len-when-digit-equal-congruence
  (implies (digit-equal digit0 digit1)
           (equal (digit->len digit0)
                  (digit->len digit1)))
  :rule-classes :congruence
  :enable digit->len)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define digit1->fst ((digit digitp))
  :guard (mbe :logic (equal (digit-case digit) 1)
              :exec (= (the (integer 1 4) (digit-case digit)) 1))
  (cddr (digit-fix digit))
  :inline t
  :guard-hints (("Goal" :in-theory (enable digitp))))

;;;;;;;;;;;;;;;;;;;;

(defrule digit1->fst-when-digit-equal-congruence
  (implies (digit-equal digit0 digit1)
           (equal (digit1->fst digit0)
                  (digit1->fst digit1)))
  :rule-classes :congruence
  :enable digit1->fst)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define digit2->fst ((digit digitp))
  :guard (mbe :logic (equal (digit-case digit) 2)
              :exec (= (the (integer 1 4) (digit-case digit)) 2))
  (caddr (digit-fix digit))
  :inline t
  :guard-hints (("Goal" :in-theory (enable digitp
                                           digit-case))))

;;;;;;;;;;;;;;;;;;;;

(defrule digit2->fst-when-digit-equal-congruence
  (implies (digit-equal digit0 digit1)
           (equal (digit2->fst digit0)
                  (digit2->fst digit1)))
  :rule-classes :congruence
  :enable digit2->fst)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define digit2->snd ((digit digitp))
  :guard (mbe :logic (equal (digit-case digit) 2)
              :exec (= (the (integer 1 4) (digit-case digit)) 2))
  (cdddr (digit-fix digit))
  :inline t
  :guard-hints (("Goal" :in-theory (enable digitp digit-case))))

;;;;;;;;;;;;;;;;;;;;

(defrule digit2->snd-when-digit-equal-congruence
  (implies (digit-equal digit0 digit1)
           (equal (digit2->snd digit0)
                  (digit2->snd digit1)))
  :rule-classes :congruence
  :enable digit2->snd)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define digit3->fst ((digit digitp))
  :guard (mbe :logic (equal (digit-case digit) 3)
              :exec (= (the (integer 1 4) (digit-case digit)) 3))
  (caar (cddr (digit-fix digit)))
  :inline t
  :guard-hints (("Goal" :in-theory (enable digitp
                                           digit-case))))

;;;;;;;;;;;;;;;;;;;;

(defrule digit3->fst-when-digit-equal-congruence
  (implies (digit-equal digit0 digit1)
           (equal (digit3->fst digit0)
                  (digit3->fst digit1)))
  :rule-classes :congruence
  :enable digit3->fst)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define digit3->snd ((digit digitp))
  :guard (mbe :logic (equal (digit-case digit) 3)
              :exec (= (the (integer 1 4) (digit-case digit)) 3))
  (cdar (cddr (digit-fix digit)))
  :inline t
  :guard-hints (("Goal" :in-theory (enable digitp digit-case))))

;;;;;;;;;;;;;;;;;;;;

(defrule digit3->snd-when-digit-equal-congruence
  (implies (digit-equal digit0 digit1)
           (equal (digit3->snd digit0)
                  (digit3->snd digit1)))
  :rule-classes :congruence
  :enable digit3->snd)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define digit3->thd ((digit digitp))
  :guard (mbe :logic (equal (digit-case digit) 3)
              :exec (= (the (integer 1 4) (digit-case digit)) 3))
  (cdddr (digit-fix digit))
  :inline t
  :guard-hints (("Goal" :in-theory (enable digitp digit-case))))

;;;;;;;;;;;;;;;;;;;;

(defrule digit3->thd-when-digit-equal-congruence
  (implies (digit-equal digit0 digit1)
           (equal (digit3->thd digit0)
                  (digit3->thd digit1)))
  :rule-classes :congruence
  :enable digit3->thd)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define digit4->fst ((digit digitp))
  :guard (mbe :logic (equal (digit-case digit) 4)
              :exec (= (the (integer 1 4) (digit-case digit)) 4))
  (caar (cddr (digit-fix digit)))
  :inline t
  :guard-hints (("Goal" :in-theory (enable digitp
                                           digit-case))))

;;;;;;;;;;;;;;;;;;;;

(defrule digit4->fst-when-digit-equal-congruence
  (implies (digit-equal digit0 digit1)
           (equal (digit4->fst digit0)
                  (digit4->fst digit1)))
  :rule-classes :congruence
  :enable digit4->fst)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define digit4->snd ((digit digitp))
  :guard (mbe :logic (equal (digit-case digit) 4)
              :exec (= (the (integer 1 4) (digit-case digit)) 4))
  (cdar (cddr (digit-fix digit)))
  :inline t
  :guard-hints (("Goal" :in-theory (enable digitp digit-case))))

;;;;;;;;;;;;;;;;;;;;

(defrule digit4->snd-when-digit-equal-congruence
  (implies (digit-equal digit0 digit1)
           (equal (digit4->snd digit0)
                  (digit4->snd digit1)))
  :rule-classes :congruence
  :enable digit4->snd)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define digit4->thd ((digit digitp))
  :guard (mbe :logic (equal (digit-case digit) 4)
              :exec (= (the (integer 1 4) (digit-case digit)) 4))
  (car (cdddr (digit-fix digit)))
  :inline t
  :guard-hints (("Goal" :in-theory (enable digitp digit-case))))

;;;;;;;;;;;;;;;;;;;;

(defrule digit4->thd-when-digit-equal-congruence
  (implies (digit-equal digit0 digit1)
           (equal (digit4->thd digit0)
                  (digit4->thd digit1)))
  :rule-classes :congruence
  :enable digit4->thd)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define digit4->frth ((digit digitp))
  :guard (mbe :logic (equal (digit-case digit) 4)
              :exec (= (the (integer 1 4) (digit-case digit)) 4))
  (cddddr (digit-fix digit))
  :inline t
  :guard-hints (("Goal" :in-theory (enable digitp digit-case))))

;;;;;;;;;;;;;;;;;;;;

(defrule digit4->frth-when-digit-equal-congruence
  (implies (digit-equal digit0 digit1)
           (equal (digit4->frth digit0)
                  (digit4->frth digit1)))
  :rule-classes :congruence
  :enable digit4->frth)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define digit1
  ((len natp)
   a)
  :returns (digit digitp
                  :rule-classes (:rewrite :type-prescription)
                  :hints (("Goal" :in-theory (enable digitp))))
  (cons 1 (cons (nat-fix len) a))
  :inline t)

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t digit1)))

(defrule digit1-when-nat-equiv-congruence
  (implies (nat-equiv len0 len1)
           (equal (digit1 len0 a)
                  (digit1 len1 a)))
  :rule-classes :congruence
  :enable digit1)

(defrule digit-case-of-digit1
  (equal (digit-case (digit1 len a))
         1)
  :enable (digit-case
           digit1
           digitp))

(defrule digit->len-of-digit1
  (equal (digit->len (digit1 len a))
         (nfix len))
  :enable (digit->len
           digit1
           digitp))

(defrule digit1->fst-of-digit1
  (equal (digit1->fst (digit1 len a))
         a)
  :enable (digit1->fst
           digit1
           digitp))

(defrule digit1-elim
  (implies (and (digitp digit)
                (equal (digit-case digit) 1))
           (equal (digit1 (digit->len digit) (digit1->fst digit))
                  digit))
  :rule-classes :elim
  :enable (digit1
           digit->len
           digit1->fst
           digit-case
           digitp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define digit2
  ((len natp)
   a
   b)
  :returns (digit digitp
                  :rule-classes (:rewrite :type-prescription)
                  :hints (("Goal" :in-theory (enable digitp))))
  (cons 2 (cons (nat-fix len) (cons a b)))
  :inline t)

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t digit2)))

(defrule digit2-when-nat-equiv-congruence
  (implies (nat-equiv len0 len1)
           (equal (digit2 len0 a b)
                  (digit2 len1 a b)))
  :rule-classes :congruence
  :enable digit2)

(defrule digit-case-of-digit2
  (equal (digit-case (digit2 len a b))
         2)
  :enable (digit-case
           digit2
           digitp))

(defrule digit->len-of-digit2
  (equal (digit->len (digit2 len a b))
         (nfix len))
  :enable (digit->len
           digit2
           digitp))

(defrule digit2->fst-of-digit2
  (equal (digit2->fst (digit2 len a b))
         a)
  :enable (digit2->fst
           digit2
           digitp))

(defrule digit2->snd-of-digit2
  (equal (digit2->snd (digit2 len a b))
         b)
  :enable (digit2->snd
           digit2
           digitp))

(defrule digit2-elim
  (implies (equal (digit-case digit) 2)
           (equal (digit2 (digit->len digit)
                          (digit2->fst digit)
                          (digit2->snd digit))
                  digit))
  :rule-classes :elim
  :enable (digit2
           digit->len
           digit2->fst
           digit2->snd
           digit-case
           digit-fix
           digitp
           irr-digit))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define digit3
  ((len natp)
   a
   b
   c)
  :returns (digit digitp
                  :rule-classes (:rewrite :type-prescription)
                  :hints (("Goal" :in-theory (enable digitp))))
  (cons 3 (cons (nat-fix len) (cons (cons a b) c)))
  :inline t)

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t digit3)))

(defrule digit3-when-nat-equiv-congruence
  (implies (nat-equiv len0 len1)
           (equal (digit3 len0 a b c)
                  (digit3 len1 a b c)))
  :rule-classes :congruence
  :enable digit3)

(defrule digit-case-of-digit3
  (equal (digit-case (digit3 len a b c))
         3)
  :enable (digit-case
           digit3
           digitp))

(defrule digit->len-of-digit3
  (equal (digit->len (digit3 len a b c))
         (nfix len))
  :enable (digit->len
           digit3
           digitp))

(defrule digit3->fst-of-digit3
  (equal (digit3->fst (digit3 len a b c))
         a)
  :enable (digit3->fst
           digit3
           digitp))

(defrule digit3->snd-of-digit3
  (equal (digit3->snd (digit3 len a b c))
         b)
  :enable (digit3->snd
           digit3
           digitp))

(defrule digit3->thd-of-digit3
  (equal (digit3->thd (digit3 len a b c))
         c)
  :enable (digit3->thd
           digit3
           digitp))

(defrule digit3-elim
  (implies (equal (digit-case digit) 3)
           (equal (digit3 (digit->len digit)
                          (digit3->fst digit)
                          (digit3->snd digit)
                          (digit3->thd digit))
                  digit))
  :rule-classes :elim
  :enable (digit3
           digit->len
           digit3->fst
           digit3->snd
           digit3->thd
           digit-case
           digit-fix
           digitp
           irr-digit))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define digit4
  ((len natp)
   a
   b
   c
   d)
  :returns (digit digitp
                  :rule-classes (:rewrite :type-prescription)
                  :hints (("Goal" :in-theory (enable digitp))))
  (cons 4 (cons (nat-fix len) (cons (cons a b) (cons c d))))
  :inline t)

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t digit4)))

(defrule digit4-when-nat-equiv-congruence
  (implies (nat-equiv len0 len1)
           (equal (digit4 len0 a b c d)
                  (digit4 len1 a b c d)))
  :rule-classes :congruence
  :enable digit4)

(defrule digit-case-of-digit4
  (equal (digit-case (digit4 len a b c d))
         4)
  :enable (digit-case
           digit4
           digitp))

(defrule digit->len-of-digit4
  (equal (digit->len (digit4 len a b c d))
         (nfix len))
  :enable (digit->len
           digit4
           digitp))

(defrule digit4->fst-of-digit4
  (equal (digit4->fst (digit4 len a b c d))
         a)
  :enable (digit4->fst
           digit4
           digitp))

(defrule digit4->snd-of-digit4
  (equal (digit4->snd (digit4 len a b c d))
         b)
  :enable (digit4->snd
           digit4
           digitp))

(defrule digit4->thd-of-digit4
  (equal (digit4->thd (digit4 len a b c d))
         c)
  :enable (digit4->thd
           digit4
           digitp))

(defrule digit4->frth-of-digit4
  (equal (digit4->frth (digit4 len a b c d))
         d)
  :enable (digit4->frth
           digit4
           digitp))

(defrule digit4-elim
  (implies (equal (digit-case digit) 4)
           (equal (digit4 (digit->len digit)
                          (digit4->fst digit)
                          (digit4->snd digit)
                          (digit4->thd digit)
                          (digit4->frth digit))
                  digit))
  :rule-classes :elim
  :enable (digit4
           digit->len
           digit4->fst
           digit4->snd
           digit4->thd
           digit4->frth
           digit-case
           digit-fix
           digitp
           irr-digit))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro digit (len &rest args)
  (case (acl2::len args)
    (1 `(digit1 ,len ,@args))
    (2 `(digit2 ,len ,@args))
    (3 `(digit3 ,len ,@args))
    (4 `(digit4 ,len ,@args))
    (otherwise
      (er hard 'digit "Illegal number of arguments: ~x0." (acl2::len args)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; This is a pseudo-accessor
(define digit->head ((digit digitp))
  (mbe :logic (case (digit-case digit)
                (1 (digit1->fst digit))
                (2 (digit2->fst digit))
                (3 (digit3->fst digit))
                (otherwise (digit4->fst digit)))
       :exec (case (digit-case digit)
               (1 (digit1->fst digit))
               (2 (digit2->fst digit))
               (otherwise (caar (cddr digit)))))
  :inline t
  :guard-hints (("Goal" :in-theory (enable digit3->fst
                                           digit4->fst
                                           digitp
                                           digit-case))))

;;;;;;;;;;;;;;;;;;;;

(defrule digit->head-when-digit-equal-congruence
  (implies (digit-equal digit0 digit1)
           (equal (digit->head digit0)
                  (digit->head digit1)))
  :rule-classes :congruence
  :enable digit->head)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define digit->last ((digit digitp))
  (case (digit-case digit)
    (1 (digit1->fst digit))
    (2 (digit2->snd digit))
    (3 (digit3->thd digit))
    (otherwise (digit4->frth digit)))
  :inline t)

;;;;;;;;;;;;;;;;;;;;

(defrule digit->last-when-digit-equal-congruence
  (implies (digit-equal digit0 digit1)
           (equal (digit->last digit0)
                  (digit->last digit1)))
  :rule-classes :congruence
  :enable digit->last)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; node2: (t   . (len . (a . b)))
;; node3: (nil . (len . (a . (b . c))))
(define nodep (x)
  :returns (yes/no booleanp :rule-classes (:rewrite :type-prescription))
  (and (consp x)
       (consp (cdr x))
       (consp (cddr x))
       (natp (cadr x))
       (let ((tag (car x)))
         (if tag
             ;; node2
             (eq tag t)
           ;; node3
           (consp (cdddr x))))))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t nodep)))

(defrule nodep-compound-recognizer
  (implies (nodep node)
           (consp node))
  :rule-classes :compound-recognizer
  :enable nodep)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define irr-node ()
  :returns (node$ nodep :rule-classes (:rewrite :type-prescription))
  (cons t (cons 2 (cons nil nil))))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t irr-node) (:e irr-node)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define node-fix ((node nodep))
  :returns (node$ nodep :rule-classes (:rewrite :type-prescription))
  (mbe :logic (if (nodep node)
                  node
                (irr-node))
       :exec (the cons node))
  :inline t)

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t node-fix)))

(defrule node-fix-when-nodep
  (implies (nodep node)
           (equal (node-fix node)
                  node))
  :enable node-fix)

(defruled node-fix-when-not-nodep
  (implies (not (nodep node))
           (equal (node-fix node)
                  (irr-node)))
  :enable node-fix)

(defrule node-fix-when-not-nodep-cheap
  (implies (not (nodep node))
           (equal (node-fix node)
                  (irr-node)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by node-fix-when-not-nodep)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define node-equal ((x nodep) (y nodep))
  :returns (yes/no booleanp :rule-classes (:rewrite :type-prescription))
  (mbe :logic (equal (node-fix x) (node-fix y))
       :exec (and (eq (the symbol (car x)) (the symbol (car y)))
                  (= (the unsigned-byte (cadr x)) (the unsigned-byte (cadr y)))
                  (equal (cddr x) (cddr y))))
  :inline t
  :guard-hints (("Goal" :in-theory (enable nodep))))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t node-equal)))

(defequiv node-equal
  :hints (("Goal" :in-theory (enable node-equal))))

(defrule node-fix-when-node-equal-congruence
  (implies (node-equal node0 node1)
           (equal (node-fix node0)
                  (node-fix node1)))
  :rule-classes :congruence
  :enable node-equal)

(defrule node-fix-under-node-equal
  (node-equal (node-fix node)
               node)
  :enable node-equal)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; If not node2, then node3
(define node2p ((node nodep))
  :returns (yes/no booleanp
                   :rule-classes (:rewrite :type-prescription)
                   :hints (("Goal" :in-theory (enable node-fix
                                                      nodep
                                                      irr-node))))
  (the symbol (car (node-fix node)))
  :inline t
  :guard-hints (("Goal" :in-theory (enable nodep))))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t node2p)))

(defrule node2p-when-node-equal-congruence
  (implies (node-equal node0 node1)
           (equal (node2p node0)
                  (node2p node1)))
  :rule-classes :congruence
  :enable node2p)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define node->len ((node nodep))
  :returns (len natp
                :rule-classes :type-prescription
                :hints (("Goal" :in-theory (enable node-fix
                                                   nodep
                                                   irr-node))))
  (the unsigned-byte (cadr (node-fix node)))
  :inline t
  :guard-hints (("Goal" :in-theory (enable nodep))))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t node->len)))

(defrule node->len-when-node-equal-congruence
  (implies (node-equal node0 node1)
           (equal (node->len node0)
                  (node->len node1)))
  :rule-classes :congruence
  :enable node->len)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define node->fst ((node nodep))
  (caddr (node-fix node))
  :inline t
  :guard-hints (("Goal" :in-theory (enable nodep))))

;;;;;;;;;;;;;;;;;;;;

(defrule node->fst-when-node-equal-congruence
  (implies (node-equal node0 node1)
           (equal (node->fst node0)
                  (node->fst node1)))
  :rule-classes :congruence
  :enable node->fst)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define node2->snd ((node nodep))
  :guard (node2p node)
  (cdddr (node-fix node))
  :inline t
  :guard-hints (("Goal" :in-theory (enable nodep))))

;;;;;;;;;;;;;;;;;;;;

(defrule node2->snd-when-node-equal-congruence
  (implies (node-equal node0 node1)
           (equal (node2->snd node0)
                  (node2->snd node1)))
  :rule-classes :congruence
  :enable node2->snd)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define node3->snd ((node nodep))
  :guard (not (node2p node))
  (cadddr (node-fix node))
  :inline t
  :guard-hints (("Goal" :in-theory (enable nodep
                                           node2p))))

;;;;;;;;;;;;;;;;;;;;

(defrule node3->snd-when-node-equal-congruence
  (implies (node-equal node0 node1)
           (equal (node3->snd node0)
                  (node3->snd node1)))
  :rule-classes :congruence
  :enable node3->snd)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define node3->thd ((node nodep))
  :guard (not (node2p node))
  (cddddr (node-fix node))
  :inline t
  :guard-hints (("Goal" :in-theory (enable nodep node2p))))

;;;;;;;;;;;;;;;;;;;;

(defrule node3->thd-when-node-equal-congruence
  (implies (node-equal node0 node1)
           (equal (node3->thd node0)
                  (node3->thd node1)))
  :rule-classes :congruence
  :enable node3->thd)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define node2
  ((len natp)
   a
   b)
  :returns (node nodep
                 :rule-classes (:rewrite :type-prescription)
                 :hints (("Goal" :in-theory (enable nodep))))
  (cons t (cons (nat-fix len) (cons a b)))
  :inline t)

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t node2)))

(defrule node2-when-nat-equiv-congruence
  (implies (nat-equiv len0 len1)
           (equal (node2 len0 a b)
                  (node2 len1 a b)))
  :rule-classes :congruence
  :enable node2)

(defrule node2p-of-node2
  (node2p (node2 len a b))
  :enable (node2p
           node2
           node-fix
           irr-node))

(defrule node->len-of-node2
  (equal (node->len (node2 len a b))
         (nfix len))
  :enable (node->len
           node2
           nodep))

(defrule node->fst-of-node2
  (equal (node->fst (node2 len a b))
         a)
  :enable (node->fst
           node2
           nodep))

(defrule node2->snd-of-node2
  (equal (node2->snd (node2 len a b))
         b)
  :enable (node2->snd
           node2
           nodep))

(defrule node2-elim
  (implies (and (nodep node)
                (node2p node))
           (equal (node2 (node->len node) (node->fst node) (node2->snd node))
                  node))
  :rule-classes :elim
  :enable (node2
           node->len
           node->fst
           node2->snd
           nodep
           node2p))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define node3
  ((len natp)
   a
   b
   c)
  :returns (node nodep
                 :rule-classes (:rewrite :type-prescription)
                 :hints (("Goal" :in-theory (enable nodep))))
  (cons nil (cons (nat-fix len) (cons a (cons b c))))
  :inline t)

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t node3)))

(defrule node3-when-nat-equiv-congruence
  (implies (nat-equiv len0 len1)
           (equal (node3 len0 a b c)
                  (node3 len1 a b c)))
  :rule-classes :congruence
  :enable node3)

(defrule node2p-of-node3
  (not (node2p (node3 len a b c)))
  :enable (node2p
           node3
           node-fix
           nodep))

(defrule node->len-of-node3
  (equal (node->len (node3 len a b c))
         (nfix len))
  :enable (node->len
           node3
           nodep))

(defrule node->fst-of-node3
  (equal (node->fst (node3 len a b c))
         a)
  :enable (node->fst
           node3
           nodep))

(defrule node3->snd-of-node3
  (equal (node3->snd (node3 len a b c))
         b)
  :enable (node3->snd
           node3
           nodep))

(defrule node3->thd-of-node3
  (equal (node3->thd (node3 len a b c))
         c)
  :enable (node3->thd
           node3
           nodep))

(defrule node3-elim
  (implies (not (node2p node))
           (equal (node3 (node->len node)
                         (node->fst node)
                         (node3->snd node)
                         (node3->thd node))
                  node))
  :rule-classes :elim
  :enable (node3
           node->len
           node->fst
           node3->snd
           node3->thd
           node-fix
           nodep
           node2p
           irr-node))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro node (len &rest args)
  (case (acl2::len args)
    (2 `(node2 ,len ,@args))
    (3 `(node3 ,len ,@args))
    (otherwise
      (er hard 'node "Illegal number of arguments: ~x0." (acl2::len args)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; ftree = finger tree
(define ftreep (x)
  :returns (yes/no booleanp :rule-classes (:rewrite :type-prescription))
  (if (consp x)
      (if (car x)
          ;; single
          (eq (car x) t)
        ;; deep
        (and (consp (cdr x))
             (natp (cadr x))
             (consp (cddr x))
             (consp (cdddr x))
             ;; TODO: think about optimal field order
             ;; prefix
             (digitp (caddr x))
             ;; suffix
             (digitp (cadddr x))
             ;; middle
             (ftreep (cddddr x))))
    ;; empty
    (eq x nil)))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t ftreep)))

(defrule ftreep-compound-recognizer
  (if (ftreep tree)
      (or (equal tree nil)
          (consp tree))
    (not (equal tree nil)))
  :rule-classes :compound-recognizer
  :enable ftreep)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ftree-fix ((tree ftreep))
  :returns (tree$ ftreep :rule-classes (:rewrite :type-prescription))
  (mbe :logic (if (ftreep tree)
                  tree
                nil)
       :exec (the (or null cons) tree))
  :inline t)

;;;;;;;;;;;;;;;;;;;;

(defrule ftree-fix-when-ftreep
  (implies (ftreep tree)
           (equal (ftree-fix tree)
                  tree))
  :enable ftree-fix)

(defruled ftree-fix-when-not-ftreep
  (implies (not (ftreep tree))
           (equal (ftree-fix tree)
                  nil))
  :enable ftree-fix)

(defrule ftree-fix-when-not-ftreep-cheap
  (implies (not (ftreep tree))
           (equal (ftree-fix tree)
                  nil))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by ftree-fix-when-not-ftreep)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ftree-equal ((x ftreep) (y ftreep))
  :returns (yes/no booleanp :rule-classes (:rewrite :type-prescription))
  ;; (mbe :logic (equal (ftree-fix x) (ftree-fix y))
  ;;      :exec (or (and (endp x) (endp y))
  ;;                (and (eq (the symbol (car x)) (the symbol (car y)))
  ;;                     (if (car x)
  ;;                         (equal (cdr x) (cdr y))
  ;;                       (and (digit-equal (cadr x) (cadr y))
  ;;                            (digit-equal (cdddr x) (cdddr y))
  ;;                            (ftree-equal (caddr x) (caddr y)))))))
  (equal (ftree-fix x) (ftree-fix y))
  :inline t
  ;; Verified below
  ;; :verify-guards nil
  ;; :guard-hints (("Goal" :in-theory (enable ftreep
  ;;                                          ftree-equal$inline
  ;;                                          digit-equal
  ;;                                          )))
  )

;; TODO: I'm guessing I need to induct over x and y simultaneously
;; (defruled ftree-equal-becomes-exec
;;   (implies (and (ftreep x)
;;                 (ftreep y))
;;            (equal (ftree-equal x y)
;;                   (or (and (not (consp x)) (not (consp y)))
;;                       (and (equal (car x) (car y))
;;                            (if (car x)
;;                                (equal (cdr x) (cdr y))
;;                              (and (digit-equal (cadr x) (cadr y))
;;                                   (digit-equal (cdddr x) (cdddr y))
;;                                   (ftree-equal (caddr x) (caddr y))))))))
;;   :induct t
;;   :enable (ftreep
;;            ftree-equal
;;            digit-equal))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t ftree-equal)))

(defequiv ftree-equal
  :hints (("Goal" :in-theory (enable ftree-equal))))

(defrule ftree-fix-when-ftree-equal-congruence
  (implies (ftree-equal tree0 tree1)
           (equal (ftree-fix tree0)
                  (ftree-fix tree1)))
  :rule-classes :congruence
  :enable ftree-equal)

(defrule ftree-fix-under-ftree-equal
  (ftree-equal (ftree-fix tree)
               tree)
  :enable ftree-equal)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ftree-empty-p ((tree ftreep))
  :returns (yes/no booleanp
                   :rule-classes (:rewrite :type-prescription))
  (endp (ftree-fix tree))
  :inline t)

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t ftree-empty-p)))

(defrule ftree-empty-p-when-ftree-equal-congruence
  (implies (ftree-equal tree0 tree1)
           (equal (ftree-empty-p tree0)
                  (ftree-empty-p tree1)))
  :rule-classes :congruence
  :enable ftree-empty-p)

(defruled ftree-empty-p-when-not-ftreep
  (implies (not (ftreep tree))
           (ftree-empty-p tree))
  :enable ftree-empty-p)

(defrule ftree-empty-p-when-not-ftreep-cheap
  (implies (not (ftreep tree))
           (ftree-empty-p tree))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by ftree-empty-p-when-not-ftreep)

(defruled ftreep-when-not-ftree-empty-p
  (implies (not (ftree-empty-p (double-rewrite tree)))
           (ftreep tree)))

(defrule ftreep-when-not-ftree-empty-p-cheap
  (implies (not (ftree-empty-p (double-rewrite tree)))
           (ftreep tree))
  :rule-classes ((:rewrite :backchain-limit-lst (0))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; If not single, then deep
(define ftree-single-p ((tree ftreep))
  :guard (not (ftree-empty-p tree))
  :returns (yes/no booleanp
                   :rule-classes (:rewrite :type-prescription)
                   :hints (("Goal" :in-theory (enable ftree-fix
                                                      ftreep))))
  (the symbol (car (ftree-fix tree)))
  :inline t
  :guard-hints (("Goal" :in-theory (enable ftreep
                                           ftree-empty-p))))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t ftree-single-p)))

(defrule ftree-single-p-when-ftree-equal-congruence
  (implies (ftree-equal tree0 tree1)
           (equal (ftree-single-p tree0)
                  (ftree-single-p tree1)))
  :rule-classes :congruence
  :enable ftree-single-p)

(defruled ftree-single-p-when-not-ftreep
  (implies (not (ftreep tree))
           (not (ftree-single-p tree)))
  :enable ftree-single-p)

(defrule ftree-single-p-when-not-ftreep-cheap
  (implies (not (ftreep tree))
           (not (ftree-single-p tree)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :enable ftree-single-p)

(defruled ftreep-when-ftree-single-p
  (implies (ftree-single-p (double-rewrite tree))
           (ftreep tree)))

(defrule ftreep-when-ftree-single-p-forward-chaining
  (implies (ftree-single-p tree)
           (ftreep tree))
  :rule-classes :forward-chaining)

(defruled ftree-single-p-when-ftree-empty-p
  (implies (ftree-empty-p tree)
           (not (ftree-single-p tree)))
  :enable (ftree-single-p
           ftree-empty-p))

(defrule ftree-single-p-when-ftree-empty-p-cheap
  (implies (ftree-empty-p tree)
           (not (ftree-single-p tree)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by ftree-single-p-when-ftree-empty-p)

(defruled ftree-empty-p-when-ftree-single-p
  (implies (ftree-single-p tree)
           (not (ftree-empty-p tree))))

(defrule ftree-empty-p-when-ftree-single-p-forward-chaining
  (implies (ftree-single-p tree)
           (not (ftree-empty-p tree)))
  :rule-classes :forward-chaining)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ftree-single-p-no-guard (tree)
  (mbe :logic (ftree-single-p tree)
       :exec (and (consp tree)
                  (eq (car tree) t)))
  :enabled t
  :inline t
  :guard-hints (("Goal" :in-theory (enable ftree-single-p
                                           ftree-fix
                                           ftreep))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ftree-single->elem ((tree ftree-single-p-no-guard))
  (mbe :logic (if (ftree-single-p tree)
                  (cdr tree)
                nil)
       :exec (cdr (the cons tree)))
  :inline t
  :guard-hints (("Goal" :in-theory (enable ftree-single-p
                                           ftree-fix))))

;;;;;;;;;;;;;;;;;;;;

(defrule ftree-single->elem-when-ftree-equal-congruence
  (implies (ftree-equal tree0 tree1)
           (equal (ftree-single->elem tree0)
                  (ftree-single->elem tree1)))
  :rule-classes :congruence
  :enable (ftree-single->elem
           ftree-equal
           ftree-fix))

(defruled ftree-single->elem-when-not-ftreep
  (implies (not (ftreep tree))
           (equal (ftree-single->elem tree)
                  nil))
  :enable ftree-single->elem)

(defrule ftree-single->elem-when-not-ftreep-cheap
  (implies (not (ftreep tree))
           (equal (ftree-single->elem tree)
                  nil))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by ftree-single->elem-when-not-ftreep)

(defruled ftree-single->elem-when-ftree-empty-p
  (implies (ftree-empty-p tree)
           (equal (ftree-single->elem tree)
                  nil))
  :enable ftree-single->elem)

(defrule ftree-single->elem-when-ftree-empty-p-cheap
  (implies (ftree-empty-p tree)
           (equal (ftree-single->elem tree)
                  nil))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by ftree-single->elem-when-ftree-empty-p)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ftree-deep-p-no-guard (tree)
  (mbe :logic (and (not (ftree-empty-p tree))
                   (not (ftree-single-p tree)))
       :exec (and (consp tree)
                  (not (car tree))
                  (consp (cdr tree))
                  (natp (cadr tree))
                  (consp (cddr tree))
                  (consp (cdddr tree))
                  (digitp (caddr tree))
                  (digitp (cadddr tree))
                  (ftreep (cddddr tree))))
  :enabled t
  :inline t
  :guard-hints (("Goal" :in-theory (enable ftree-empty-p
                                           ftree-single-p
                                           ftree-fix
                                           ftreep))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ftree-deep->len ((tree ftree-deep-p-no-guard))
  :returns (len natp
                :rule-classes :type-prescription
                :hints (("Goal" :in-theory (enable ftree-single-p
                                                   ftree-empty-p
                                                   ftree-fix
                                                   ftreep))))
  (mbe :logic (if (and (not (ftree-empty-p tree))
                       (not (ftree-single-p tree)))
                  (cadr tree)
                0)
       :exec (car (the cons (cdr (the cons tree)))))
  :inline t
  :guard-hints (("Goal" :in-theory (enable ftree-empty-p
                                           ftree-single-p
                                           ftree-fix
                                           ftreep))))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t ftree-deep->len)))

(defrule ftree-deep->len-when-ftree-equal-congruence
  (implies (ftree-equal tree0 tree1)
           (equal (ftree-deep->len tree0)
                  (ftree-deep->len tree1)))
  :rule-classes :congruence
  :Enable (ftree-deep->len
           ftree-equal
           ftree-fix
           irr-digit))

(defruled ftree-deep->len-when-not-ftreep
  (implies (not (ftreep tree))
           (equal (ftree-deep->len tree)
                  0))
  :enable ftree-deep->len)

(defrule ftree-deep->len-when-not-ftreep-cheap
  (implies (not (ftreep tree))
           (equal (ftree-deep->len tree)
                  0))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by ftree-deep->len-when-not-ftreep)

(defruled ftree-deep->len-when-ftree-empty-p
  (implies (ftree-empty-p tree)
           (equal (ftree-deep->len tree)
                  0))
  :enable ftree-deep->len)

(defrule ftree-deep->len-when-ftree-empty-p-cheap
  (implies (ftree-empty-p tree)
           (equal (ftree-deep->len tree)
                  0))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by ftree-deep->len-when-ftree-empty-p)

(defruled ftree-deep->len-when-ftree-single-p
  (implies (ftree-single-p tree)
           (equal (ftree-deep->len tree)
                  0))
  :enable ftree-deep->len)

(defrule ftree-deep->len-when-ftree-single-p-cheap
  (implies (ftree-single-p tree)
           (equal (ftree-deep->len tree)
                  0))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by ftree-deep->len-when-ftree-single-p)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ftree-deep->prefix ((tree ftree-deep-p-no-guard))
  :returns (digit digitp
                  :rule-classes (:rewrite :type-prescription)
                  :hints (("Goal" :in-theory (enable ftree-single-p
                                                     ftree-empty-p
                                                     ftree-fix
                                                     ftreep))))
  (mbe :logic (if (and (not (ftree-empty-p tree))
                       (not (ftree-single-p tree)))
                  (caddr tree)
                (irr-digit))
       :exec (car (the cons (cdr (the cons (cdr (the cons tree)))))))
  :inline t
  :guard-hints (("Goal" :in-theory (enable ftree-empty-p
                                           ftree-single-p
                                           ftree-fix
                                           ftreep))))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t ftree-deep->prefix)))

(defrule ftree-deep->prefix-when-ftree-equal-congruence
  (implies (ftree-equal tree0 tree1)
           (equal (ftree-deep->prefix tree0)
                  (ftree-deep->prefix tree1)))
  :rule-classes :congruence
  :Enable (ftree-deep->prefix
           ftree-equal
           ftree-fix
           irr-digit))

(defruled ftree-deep->prefix-when-not-ftreep
  (implies (not (ftreep tree))
           (equal (ftree-deep->prefix tree)
                  (irr-digit)))
  :enable ftree-deep->prefix)

(defrule ftree-deep->prefix-when-not-ftreep-cheap
  (implies (not (ftreep tree))
           (equal (ftree-deep->prefix tree)
                  (irr-digit)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by ftree-deep->prefix-when-not-ftreep)

(defruled ftree-deep->prefix-when-ftree-empty-p
  (implies (ftree-empty-p tree)
           (equal (ftree-deep->prefix tree)
                  (irr-digit)))
  :enable ftree-deep->prefix)

(defrule ftree-deep->prefix-when-ftree-empty-p-cheap
  (implies (ftree-empty-p tree)
           (equal (ftree-deep->prefix tree)
                  (irr-digit)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by ftree-deep->prefix-when-ftree-empty-p)

(defruled ftree-deep->prefix-when-ftree-single-p
  (implies (ftree-single-p tree)
           (equal (ftree-deep->prefix tree)
                  (irr-digit)))
  :enable ftree-deep->prefix)

(defrule ftree-deep->prefix-when-ftree-single-p-cheap
  (implies (ftree-single-p tree)
           (equal (ftree-deep->prefix tree)
                  (irr-digit)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by ftree-deep->prefix-when-ftree-single-p)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ftree-deep->middle ((tree ftree-deep-p-no-guard))
  :returns (tree$ ftreep
                  :rule-classes (:rewrite :type-prescription)
                  :hints (("Goal" :in-theory (enable ftree-single-p
                                                     ftree-empty-p
                                                     ftree-fix
                                                     ftreep))))
  (mbe :logic (if (and (not (ftree-empty-p tree))
                       (not (ftree-single-p tree)))
                  (cddddr tree)
                nil)
       :exec (cdr
               (the cons
                 (cdr (the cons (cdr (the cons (cdr (the cons tree)))))))))
  :inline t
  :guard-hints (("Goal" :in-theory (enable ftree-empty-p
                                           ftree-single-p
                                           ftree-fix
                                           ftreep))))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t ftree-deep->middle)))

(defrule ftree-deep->middle-when-ftree-equal-congruence
  (implies (ftree-equal tree0 tree1)
           (equal (ftree-deep->middle tree0)
                  (ftree-deep->middle tree1)))
  :rule-classes :congruence
  :Enable (ftree-deep->middle
           ftree-equal
           ftree-fix
           irr-digit))

(defruled ftree-deep->middle-when-not-ftreep
  (implies (not (ftreep tree))
           (equal (ftree-deep->middle tree)
                  nil))
  :enable ftree-deep->middle)

(defrule ftree-deep->middle-when-not-ftreep-cheap
  (implies (not (ftreep tree))
           (equal (ftree-deep->middle tree)
                  nil))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by ftree-deep->middle-when-not-ftreep)

(defruled ftree-deep->middle-when-ftree-empty-p
  (implies (ftree-empty-p tree)
           (equal (ftree-deep->middle tree)
                  nil))
  :enable ftree-deep->middle)

(defrule ftree-deep->middle-when-ftree-empty-p-cheap
  (implies (ftree-empty-p tree)
           (equal (ftree-deep->middle tree)
                  nil))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by ftree-deep->middle-when-ftree-empty-p)

(defruled ftree-deep->middle-when-ftree-single-p
  (implies (ftree-single-p tree)
           (equal (ftree-deep->middle tree)
                  nil))
  :enable ftree-deep->middle)

(defrule ftree-deep->middle-when-ftree-single-p-cheap
  (implies (ftree-single-p tree)
           (equal (ftree-deep->middle tree)
                  nil))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by ftree-deep->middle-when-ftree-single-p)

(defrule acl2-count-of-ftree-deep->middle-strong-linear
  (implies (and (not (ftree-empty-p tree))
                (not (ftree-single-p tree)))
           (< (acl2-count (ftree-deep->middle tree))
              (acl2-count tree)))
  :rule-classes :linear
  :enable (ftree-deep->middle
           ftree-empty-p
           ftree-single-p
           ftree-fix
           ftreep))

(defrule acl2-count-of-ftree-deep->middle-weak-linear
  (<= (acl2-count (ftree-deep->middle tree))
      (acl2-count tree))
  :rule-classes :linear
  :enable (ftree-deep->middle
           ftree-empty-p
           ftree-single-p
           ftree-fix
           ftreep))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ftree-deep->suffix ((tree ftree-deep-p-no-guard))
  :returns (digit digitp
                  :rule-classes (:rewrite :type-prescription)
                  :hints (("Goal" :in-theory (enable ftree-single-p
                                                     ftree-empty-p
                                                     ftree-fix
                                                     ftreep))))
  (mbe :logic (if (and (not (ftree-empty-p tree))
                       (not (ftree-single-p tree)))
                  (cadddr tree)
                (irr-digit))
       :exec (car
               (the cons
                 (cdr (the cons (cdr (the cons (cdr (the cons tree)))))))))
  :inline t
  :guard-hints (("Goal" :in-theory (enable ftree-empty-p
                                           ftree-single-p
                                           ftree-fix
                                           ftreep))))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t ftree-deep->suffix)))

(defrule ftree-deep->suffix-when-ftree-equal-congruence
  (implies (ftree-equal tree0 tree1)
           (equal (ftree-deep->suffix tree0)
                  (ftree-deep->suffix tree1)))
  :rule-classes :congruence
  :Enable (ftree-deep->suffix
           ftree-equal
           ftree-fix
           irr-digit))

(defruled ftree-deep->suffix-when-not-ftreep
  (implies (not (ftreep tree))
           (equal (ftree-deep->suffix tree)
                  (irr-digit)))
  :enable ftree-deep->suffix)

(defrule ftree-deep->suffix-when-not-ftreep-cheap
  (implies (not (ftreep tree))
           (equal (ftree-deep->suffix tree)
                  (irr-digit)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by ftree-deep->suffix-when-not-ftreep)

(defruled ftree-deep->suffix-when-ftree-empty-p
  (implies (ftree-empty-p tree)
           (equal (ftree-deep->suffix tree)
                  (irr-digit)))
  :enable ftree-deep->suffix)

(defrule ftree-deep->suffix-when-ftree-empty-p-cheap
  (implies (ftree-empty-p tree)
           (equal (ftree-deep->suffix tree)
                  (irr-digit)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by ftree-deep->suffix-when-ftree-empty-p)

(defruled ftree-deep->suffix-when-ftree-single-p
  (implies (ftree-single-p tree)
           (equal (ftree-deep->suffix tree)
                  (irr-digit)))
  :enable ftree-deep->suffix)

(defrule ftree-deep->suffix-when-ftree-single-p-cheap
  (implies (ftree-single-p tree)
           (equal (ftree-deep->suffix tree)
                  (irr-digit)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by ftree-deep->suffix-when-ftree-single-p)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ftree-single (a)
  :returns (tree ftreep
                 :hints (("Goal" :in-theory (enable ftreep))))
  (cons t a)
  :inline t)

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t ftree-single)))

(defrule ftree-single-type-prescription
  (consp (ftree-single a))
  :rule-classes :type-prescription
  :enable ftree-single)

(defrule ftree-empty-p-of-ftree-single
  (not (ftree-empty-p (ftree-single a)))
  :enable (ftree-single
           ftree-empty-p
           ftreep))

(defrule ftree-single-p-of-ftree-single
  (ftree-single-p (ftree-single a))
  :enable (ftree-single
           ftree-single-p
           ftreep))

(defrule ftree-single->elem-of-ftree-single
  (equal (ftree-single->elem (ftree-single a))
         a)
  :enable (ftree-single
           ftree-single->elem
           ftree-single-p
           ftreep))

(defrule ftree-single-elim
  (implies (ftree-single-p tree)
           (equal (ftree-single (ftree-single->elem tree))
                  tree))
  :rule-classes :elim
  :enable (ftree-single
           ftree-single->elem
           ftree-single-p
           ftree-fix
           ftreep))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ftree-deep
  ((len natp)
   (prefix digitp)
   (middle ftreep)
   (suffix digitp))
  :returns (tree ftreep
                 :hints (("Goal" :in-theory (enable ftreep))))
  (cons nil
        (cons (nat-fix len)
              (cons (digit-fix prefix)
                    (cons (digit-fix suffix)
                          (ftree-fix middle)))))
  :inline t)

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t ftree-deep)))

(defrule ftree-deep-type-prescription
  (consp (ftree-deep len prefix middle suffix))
  :rule-classes :type-prescription
  :enable ftree-deep)

(defrule ftree-deep-when-nat-equiv-congruence
  (implies (nat-equiv len0 len1)
           (equal (ftree-deep len0 prefix middle suffix)
                  (ftree-deep len1 prefix middle suffix)))
  :rule-classes :congruence
  :enable ftree-deep)

(defrule ftree-deep-when-digit-equal-of-arg2-congruence
  (implies (digit-equal prefix0 prefix1)
           (equal (ftree-deep len prefix0 middle suffix)
                  (ftree-deep len prefix1 middle suffix)))
  :rule-classes :congruence
  :enable ftree-deep)

(defrule ftree-deep-when-ftree-equal-congruence
  (implies (ftree-equal middle0 middle1)
           (equal (ftree-deep len prefix middle0 suffix)
                  (ftree-deep len prefix middle1 suffix)))
  :rule-classes :congruence
  :enable ftree-deep)

(defrule ftree-deep-when-digit-equal-of-arg4-congruence
  (implies (digit-equal suffix0 suffix1)
           (equal (ftree-deep len prefix middle suffix0)
                  (ftree-deep len prefix middle suffix1)))
  :rule-classes :congruence
  :enable ftree-deep)

(defrule ftree-empty-p-of-ftree-deep
  (not (ftree-empty-p (ftree-deep len prefix middle suffix)))
  :enable (ftree-deep
           ftree-empty-p
           ftreep))

(defrule ftree-single-p-of-ftree-deep
  (not (ftree-single-p (ftree-deep len prefix middle suffix)))
  :enable (ftree-deep
           ftree-single-p
           ftreep))

(defrule ftree-deep->len-of-ftree-deep
  (equal (ftree-deep->len (ftree-deep len prefix middle suffix))
         (nfix len))
  :enable (ftree-deep
           ftree-deep->len
           ftree-empty-p
           ftree-single-p
           ftreep))

(defrule ftree-deep->prefix-of-ftree-deep
  (equal (ftree-deep->prefix (ftree-deep len prefix middle suffix))
         (digit-fix prefix))
  :enable (ftree-deep
           ftree-deep->prefix
           ftree-empty-p
           ftree-single-p
           ftreep))

(defrule ftree-deep->middle-of-ftree-deep
  (equal (ftree-deep->middle (ftree-deep len prefix middle suffix))
         (ftree-fix middle))
  :enable (ftree-deep
           ftree-deep->middle
           ftree-empty-p
           ftree-single-p
           ftreep))

(defrule ftree-deep->suffix-of-ftree-deep
  (equal (ftree-deep->suffix (ftree-deep len prefix middle suffix))
         (digit-fix suffix))
  :enable (ftree-deep
           ftree-deep->suffix
           ftree-empty-p
           ftree-single-p
           ftreep))

(defrule ftree-deep-elim
  (implies (and (not (ftree-empty-p tree))
                (not (ftree-single-p tree)))
           (equal (ftree-deep (ftree-deep->len tree)
                              (ftree-deep->prefix tree)
                              (ftree-deep->middle tree)
                              (ftree-deep->suffix tree))
                  tree))
  :rule-classes :elim
  :enable (ftree-deep
           ftree-deep->len
           ftree-deep->prefix
           ftree-deep->middle
           ftree-deep->suffix
           ftree-empty-p
           ftree-single-p
           ftree-fix
           ftreep))
