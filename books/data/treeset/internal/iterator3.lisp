; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "TREESET")

(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)

(include-book "tree-defs")
(include-book "bst-defs")
(include-book "heap-defs")
(include-book "in-defs")
(include-book "subset-defs")
(include-book "insert-defs")
(include-book "union-defs")
(include-book "diff-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(local (include-book "kestrel/lists-light/append" :dir :system))
(local (include-book "kestrel/lists-light/last" :dir :system))
;; Unnecessary?
(local (include-book "kestrel/lists-light/member-equal" :dir :system))

(local (include-book "kestrel/utilities/ordinals" :dir :system))

(local (include-book "../hash"))
(local (include-book "tree"))
(local (include-book "bst"))
(local (include-book "heap"))
(local (include-book "in"))
(local (include-book "subset"))
(local (include-book "antisymmetry"))
(local (include-book "insert"))
(local (include-book "union"))
(local (include-book "diff"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; An iterator is a list of nonempty sets
;; The interpretation is that each set in the list represents the head,
;; followed by the iterator-expansion of the right child, and then the rest of
;; the iterator. Note that this implies that the left child is irrelevant. It
;; is, because we also expand out the string of left children when expanding a
;; tree to an iterator.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; More invariants
;; next element of this list is always an ancestor of the current element.

(define tree-iterator-p (x)
  :returns (yes/no booleanp :rule-classes :type-prescription)
  (if (consp x)
      (and (mbe :logic (and (treep (first x))
                            (not (tree-empty-p (first x))))
                :exec (and (consp (first x))
                           (tagged-element-p (car (first x)))
                           (consp (cdr (first x)))
                           (treep (cadr (first x)))
                           (treep (cddr (first x)))))
           (tree-iterator-p (rest x)))
    (null x))
  :guard-hints (("Goal" :in-theory (enable treep
                                           tree-empty-p))))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t tree-iterator-p)))

(defruled true-listp-when-tree-iterator-p
  (implies (tree-iterator-p x)
           (true-listp x))
  :induct t
  :enable tree-iterator-p)

(defrule tree-iterator-p-compound-recognizer
  (implies (tree-iterator-p x)
           (true-listp x))
  :rule-classes :compound-recognizer
  :by true-listp-when-tree-iterator-p)

(defruled tree-listp-when-tree-iterator-p
  (implies (tree-iterator-p x)
           (tree-listp x))
  :induct t
  :enable (tree-iterator-p
           tree-listp))

(defrule tree-listp-when-tree-iterator-p-forward-chaining
  (implies (tree-iterator-p x)
           (tree-listp x))
  :rule-classes :forward-chaining
  :by tree-listp-when-tree-iterator-p)

(defruled treep-of-car-when-tree-iterator-p
  (implies (tree-iterator-p iter)
           (treep (car iter)))
  :enable tree-iterator-p)

(defrule treep-of-car-when-tree-iterator-p-cheap
  (implies (tree-iterator-p iter)
           (treep (car iter)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by treep-of-car-when-tree-iterator-p)

(defruled tree-empty-p-of-car-when-tree-iterator-p
  (implies (tree-iterator-p iter)
           (equal (tree-empty-p (car iter))
                  (not (consp iter))))
  :enable tree-iterator-p)

(defrule tree-empty-p-of-car-when-tree-iterator-p-cheap
  (implies (tree-iterator-p iter)
           (equal (tree-empty-p (car iter))
                  (not (consp iter))))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by tree-empty-p-of-car-when-tree-iterator-p)

(defrule tree-iterator-p-of-cdr
  (implies (tree-iterator-p iter)
           (tree-iterator-p (cdr iter)))
  :enable tree-iterator-p)

(defrule tree-iterator-p-of-append
  (implies (tree-iterator-p x)
           (equal (tree-iterator-p (append x y))
                  (tree-iterator-p y)))
  :induct t
  :enable tree-iterator-p)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define all-well-formed-p ((trees tree-listp))
  :returns (yes/no booleanp :rule-classes :type-prescription)
  (or (endp trees)
      (and (bstp (first trees))
           (heapp (first trees))
           (all-well-formed-p (rest trees)))))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t all-well-formed-p)))

(defrule all-well-formed-p-of-append
  (equal (all-well-formed-p (append x y))
         (and (all-well-formed-p x)
              (all-well-formed-p y)))
  :induct t
  :enable all-well-formed-p)

(defrule bstp-when-all-well-formed-p
  (implies (and (all-well-formed-p trees)
                (member-equal tree trees))
           (bstp tree))
  :induct t
  :enable (all-well-formed-p
           member-equal))

(defrule heapp-when-all-well-formed-p
  (implies (and (all-well-formed-p trees)
                (member-equal tree trees))
           (heapp tree))
  :induct t
  :enable (all-well-formed-p
           member-equal))

(defrule bstp-of-car-when-all-well-formed-p
  (implies (all-well-formed-p trees)
           (bstp (car trees)))
  :enable all-well-formed-p)

(defrule heapp-of-car-when-all-well-formed-p
  (implies (all-well-formed-p trees)
           (heapp (car trees)))
  :enable all-well-formed-p)

(defrule bstp-of-car-last-when-all-well-formed-p
  (implies (all-well-formed-p trees)
           (bstp (car (last trees))))
  :induct t
  :enable (last
           all-well-formed-p))

(defrule heapp-of-car-last-when-all-well-formed-p
  (implies (all-well-formed-p trees)
           (heapp (car (last trees))))
  :induct t
  :enable (last
           all-well-formed-p))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The well-formedness invariant states that each tree is a subset of the
;; left child of the following tree.
;; This is weaker than the strongest possible invariant.
;; Each tree should actually be a descendant (not just a subset) of the
;; following tree.
;; Most precisely, each tree is iter-predecessor-p of the following tree,
;; where iter-predecessor-p is the smallest relation s.t.:
;; - (iter-predecessor-p (tree->left tree) tree)
;;     (assuming (tree->left tree) is nonempty)
;; - (implies (iter-predecessor-p x y)
;;            (iter-predecessor-p (tree->right x) y))
;;     (assuming (tree->right x) is nonempty)
;; In other words, the right spine of the immediate left child are the
;; predecessors of a tree.
;; For now, we go with the weak subset invariant. This should be sufficient for
;; our purposes (showing that the value is the min). It won't be sufficient to
;; show uniqueness of an iterator, but at the moment this is not of concern.

(define pairwise-tree-subset-p-of-left-loop ((iter tree-iterator-p))
  :guard (and (consp iter)
              (all-well-formed-p iter))
  (or (endp (rest iter))
      (and (tree-subset-p (first iter) (tree->left (second iter)))
           (pairwise-tree-subset-p-of-left-loop (rest iter))))
  :hints (("Goal" :in-theory (enable acl2-count)))
  :guard-hints (("Goal" :in-theory (enable all-well-formed-p))))

(define pairwise-tree-subset-p-of-left ((iter tree-iterator-p))
  :guard (all-well-formed-p iter)
  :returns (yes/no booleanp :rule-classes :type-prescription)
  (or (endp iter)
      (mbe :logic (or (endp (rest iter))
                      (and (tree-subset-p (first iter)
                                          (tree->left (second iter)))
                           (pairwise-tree-subset-p-of-left (rest iter))))
           :exec (pairwise-tree-subset-p-of-left-loop iter)))
  ;; Verified below
  :verify-guards nil)

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t pairwise-tree-subset-p-of-left)))

(defrulel loop-becomes-pairwise-tree-subset-p-of-left
  (implies (consp iter)
           (equal (pairwise-tree-subset-p-of-left-loop iter)
                  (pairwise-tree-subset-p-of-left iter)))
  :induct t
  :enable (pairwise-tree-subset-p-of-left-loop
           pairwise-tree-subset-p-of-left))

(verify-guards pairwise-tree-subset-p-of-left
  :hints (("Goal" :in-theory (enable pairwise-tree-subset-p-of-left))))
;; #|
(defrule tree-subset-p-of-car-and-car-last
  (implies (pairwise-tree-subset-p-of-left iter)
           (tree-subset-p (car iter) (car (last iter))))
  :induct t
  :enable pairwise-tree-subset-p-of-left)

;; MOVE
;; Also one for ->right
;; Also, do we have rules like this for ../subset?
(defrule tree-subset-p-of-arg1-and-tree->left-of-arg1
  (implies (bstp x)
           (equal (tree-subset-p x (tree->left x))
                  (tree-empty-p x)))
  :enable tree-subset-p)

;; TODO: improve proof (or just delete, not sure its used)
(defrule tree-subset-p-of-car-and-tree->left-of-car-last
  (implies (and (tree-iterator-p iter)
                (all-well-formed-p iter)
                (pairwise-tree-subset-p-of-left iter))
           (equal (tree-subset-p (car iter) (tree->left (car (last iter))))
                  (or (not (consp iter))
                      (consp (cdr iter)))))
  :induct t
  :enable (pairwise-tree-subset-p-of-left
           tree-iterator-p
           all-well-formed-p)
  :hints ('(:cases ((consp (cddr iter))))))
;; |#
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tree-iterator-to-tree ((iter tree-iterator-p))
  :returns (tree treep)
  (if (endp iter)
      nil
    (mv-let (in tree)
            (tree-insert (tagged-element->elem (tree->head (first iter)))
                         (tagged-element->hash (tree->head (first iter)))
                         (tree-union (tree->right (first iter))
                                     (tree-iterator-to-tree (rest iter))))
      (declare (ignore in))
      tree))
  :verify-guards :after-returns)

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t tree-iterator-to-tree)))

(defrule tree-iterator-to-tree-type-prescription
  (or (consp (tree-iterator-to-tree tree))
      (equal (tree-iterator-to-tree tree) nil))
  :rule-classes :type-prescription
  :induct t
  :enable tree-iterator-to-tree)

;; (defrule tree-empty-p-of-tree-iterator-to-tree
;;   (implies (tree-iterator-p iter)
;;            (equal (tree-empty-p (tree-iterator-to-tree iter))
;;                   (not iter)))
;;   :induct t
;;   :enable tree-iterator-to-tree)

(defrule tree-empty-p-of-tree-iterator-to-tree
  (equal (tree-empty-p (tree-iterator-to-tree iter))
         (not (consp iter)))
  :expand (tree-iterator-to-tree iter))

(defrule bstp-of-tree-iterator-to-tree
  (implies (all-well-formed-p iter)
           (bstp (tree-iterator-to-tree iter)))
  :induct t
  :enable (tree-iterator-to-tree
           all-well-formed-p))

(defrule heapp-of-tree-iterator-to-tree
  (implies (all-well-formed-p iter)
           (heapp (tree-iterator-to-tree iter)))
  :induct t
  :enable (tree-iterator-to-tree
           all-well-formed-p))

;;;;;;;;;;;;;;;;;;;;

(defruled tree-in-of-tree-iterator-to-tree-of-cons
  (implies (and (bstp tree)
                (all-well-formed-p trees))
           (equal (tree-in elem (tree-iterator-to-tree (cons tree trees)))
                  (or (equal elem (tagged-element->elem (tree->head tree)))
                      (tree-in elem (tree->right tree))
                      (tree-in elem (tree-iterator-to-tree trees)))))
  :enable tree-iterator-to-tree)

;;;;;;;;;;

;; (bstp$inline (car (last iter)))
;; :explain bstp-of-car-last-when-all-well-formed-p
;; :explain bstp-of-tree->left-when-bstp
(rule
  (implies (and (consp iter)
                (consp (cdr iter))
                (treep (car iter))
                (car iter)
                (tree-iterator-p (cdr iter))
                (bstp (car iter))
                (heapp (car iter))
                (all-well-formed-p (cdr iter))
                (tree-subset-p (car iter)
                               (tree->left (cadr iter)))
                (pairwise-tree-subset-p-of-left (cdr iter))
                (not (equal elem
                            (tagged-element->elem (tree->head (car iter)))))
                (not (tree-in elem (tree->right (car iter))))
                (tree-in elem (car (last iter))))
           (equal (tree-in elem
                           (tree-diff (car (last iter))
                                      (tree->left (cadr iter))))
                  (not (tree-in elem (tree->left (car iter))))))
  :enable (all-well-formed-p
           bstp-extra-rules ;; bstp-of-tree->left-when-bstp
           ;; tree-in-extra-rules
           )
  :disable ())

;;;;;;;;;;

;; GJ resume
;; :explain tree-in-of-tree-diff
(defruled tree-iterator-to-tree-when-well-formed
  (implies (and (tree-iterator-p iter)
                (all-well-formed-p iter)
                (pairwise-tree-subset-p-of-left iter))
           (equal (tree-in elem (tree-iterator-to-tree iter))
                  (tree-in elem
                           ;; By coincidence, this works even when iter is nil.
                           (tree-diff (car (last iter))
                                      (tree->left (car iter))))))
  ;; :induct t
  :induct (tree-iterator-to-tree iter)
  :enable (tree-iterator-to-tree
           tree-iterator-p
           all-well-formed-p
           pairwise-tree-subset-p-of-left
           ;; bstp
           bstp-extra-rules

           tree-in-of-tree->left-when-tree-in-of-tree->right
           tree-in-of-tree->right-when-tree-in-of-tree->left

           endp
           ))

(defruled tree-iterator-to-tree-when-well-formed
  (implies (and (tree-iterator-p iter)
                (all-well-formed-p iter)
                (pairwise-tree-subset-p-of-left iter))
           (equal (tree-iterator-to-tree iter)
                  (if (consp iter)
                      (tree-diff (car (last iter))
                                 (tree->left (car iter)))
                    nil)))
  :induct t
  :enable (tree-iterator-to-tree
           tree-iterator-p
           all-well-formed-p
           tree-double-containment-no-backchain-limit
           tree-subset-p-becomes-tree-subset-p-sk
           tree-subset-p-sk
           ))

;;;;;;;;;;;;;;;;;;;;

(defruled tree-in-of-tree-iterator-to-tree-of-append
  (implies (and (all-well-formed-p x)
                (all-well-formed-p y))
           (equal (tree-in elem (tree-iterator-to-tree (append x y)))
                  (or (tree-in elem (tree-iterator-to-tree x))
                      (tree-in elem (tree-iterator-to-tree y)))))
  :induct t
  :enable (tree-iterator-to-tree
           all-well-formed-p))

(defrule tree-iterator-to-tree-of-append
  (implies (and (all-well-formed-p x)
                (all-well-formed-p y))
           (equal (tree-iterator-to-tree (append x y))
                  (tree-union (tree-iterator-to-tree x)
                              (tree-iterator-to-tree y))))
  :enable (tree-double-containment-no-backchain-limit
           tree-in-of-tree-iterator-to-tree-of-append
           tree-subset-p-becomes-tree-subset-p-sk
           tree-subset-p-sk))

;; Now when pairwise... in addition to all-well-formed-p,
;; tree-iterator-to-tree is car-last

;; I'm thinking we might not even need ...of-append?
(defrule tree-iterator-to-tree-of-cons-when-tree-subset-p
  (implies (and ()
                ()
                (tree-subset-p x (first y)))
           (equal (tree-iterator-to-tree (cons x y))
                  (tree-iterator-to-tree y))))

;; Whoops, this isn't true. It would be for left spine only because first
;; element has no left subtree.
;; The general statement could be that it is the difference of the last tree
;; and the left subtree of the first tree.
;; We could assume no left subtree, but that wouldn't generalize.
(defrule tree-iterator-to-tree-when-pairwise-tree-subset-p-of-left
  (implies (and (pairwise-tree-subset-p-of-left iter)
                (all-well-formed-p iter))
           (equal (tree-iterator-to-tree iter)
                  (if (consp iter)
                      (car (last iter))
                    nil)))
  ;; :induct t
  :induct (tree-iterator-to-tree iter)
  :enable (tree-iterator-to-tree
           pairwise-tree-subset-p-of-left
           all-well-formed-p
           tree-double-containment-no-backchain-limit
           ;; tree-in-of-tree-iterator-to-tree-of-append
           tree-subset-p-becomes-tree-subset-p-sk
           tree-subset-p-sk
           ))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tree-left-spine-acc
  ((tree treep)
   (acc tree-listp))
  :returns (spine tree-listp)
  (if (tree-empty-p tree)
      (tree-list-fix acc)
    (tree-left-spine-acc (tree->left tree)
                         (cons (tree-fix tree) (tree-list-fix acc)))))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t tree-left-spine-acc)))

(defrule tree-left-spine-acc-when-tree-equiv-congruence
  (implies (tree-equiv tree0 tree1)
           (equal (tree-left-spine-acc tree0 acc)
                  (tree-left-spine-acc tree1 acc)))
  :rule-classes :congruence
  :expand ((tree-left-spine-acc tree0 acc)
           (tree-left-spine-acc tree1 acc)))

(defrulel tree-left-spine-acc-of-arg1-and-tree-list-fix
  (equal (tree-left-spine-acc tree (tree-list-fix acc))
         (tree-left-spine-acc tree acc))
  :expand ((tree-left-spine-acc tree (tree-list-fix acc))
           (tree-left-spine-acc tree acc)))

(defruledl tree-left-spine-acc-of-append
  (implies (and (tree-listp x)
                (tree-listp y))
           (equal (tree-left-spine-acc tree (append x y))
                  (append (tree-left-spine-acc tree x)
                          y)))
  :induct t
  :enable tree-left-spine-acc)

(defruled tree-left-spine-acc-arg2-becomes-nil
  (equal (tree-left-spine-acc tree acc)
         (append (tree-left-spine-acc tree nil)
                 (tree-list-fix acc)))
  :use (:instance tree-left-spine-acc-of-append
                  (x nil)
                  (y (tree-list-fix acc))))

(defrule tree-left-spine-acc-arg2-becomes-nil-syntaxp
  (implies (syntaxp (not (equal acc ''nil)))
           (equal (tree-left-spine-acc tree acc)
                  (append (tree-left-spine-acc tree nil)
                          (tree-list-fix acc))))
  :by tree-left-spine-acc-arg2-becomes-nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Note: this serves as the iterator constructor, in addition to being used in
;; the "next" function.
(define tree-left-spine ((tree treep))
  :returns (spine tree-listp)
  (mbe :logic (if (tree-empty-p tree)
                  nil
                (append (tree-left-spine (tree->left tree))
                        (list (tree-fix tree))))
       :exec (tree-left-spine-acc tree nil))
  :inline t
  ;; Verified below
  :verify-guards nil)

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t tree-left-spine)))

(defrule tree-left-spine-type-prescription
  (true-listp (tree-left-spine tree))
  :rule-classes :type-prescription
  :induct t
  :enable tree-left-spine)

(defrule tree-left-spine-when-tree-equiv-congruence
  (implies (tree-equiv tree0 tree1)
           (equal (tree-left-spine tree0)
                  (tree-left-spine tree1)))
  :rule-classes :congruence
  :expand ((tree-left-spine tree0)
           (tree-left-spine tree1)))

(defrule tree-left-spine-acc-becomes-tree-left-spine
  (equal (tree-left-spine-acc tree acc)
         (append (tree-left-spine tree)
                 (tree-list-fix acc)))
  :induct t
  :enable (tree-left-spine-acc
           tree-left-spine))

(verify-guards tree-left-spine$inline
  :hints (("Goal" :in-theory (enable tree-left-spine
                                     true-list-fix))))

(defrule tree-iterator-p-tree-left-spine
  (tree-iterator-p (tree-left-spine tree))
  :induct t
  :enable (tree-left-spine
           tree-iterator-p))

(defrule car-last-of-tree-left-spine
  (equal (car (last (tree-left-spine tree)))
         (tree-fix tree))
  :induct t
  :enable (tree-left-spine
           last))

;; TODO: improve proof
(defruled tree-iterator-well-formed-p-of-append
  (equal (tree-iterator-well-formed-p (append x y))
         (and (tree-iterator-well-formed-p x)
              (tree-iterator-well-formed-p y)
              (or (not (consp x))
                  (not (consp y))
                  (tree-subset-p (car (last x))
                                 (tree->left (first y))))))
  :induct t
  :enable (append
           tree-iterator-well-formed-p
           last
           true-list-fix))

(defrule tree-iterator-well-formed-p-of-tree-left-spine
  (implies (and (bstp tree)
                (heapp tree))
           (tree-iterator-well-formed-p (tree-left-spine tree)))
  :induct t
  :enable (tree-left-spine
           tree-iterator-well-formed-p
           tree-iterator-well-formed-p-of-append))

;; MOVE up under tree-iterator-to-tree
(defruled tree-in-of-tree-iterator-to-tree
  (implies (tree-iterator-well-formed-p iter)
           (equal (tree-in x (tree-iterator-to-tree iter))
                  (and (consp iter)
                       (or (equal x (tagged-element->elem
                                      (tree->head (first iter))))
                           (tree-in x (tree->right (first iter)))
                           (tree-in x (tree-iterator-to-tree (rest iter)))))))
  :induct t
  :enable (tree-iterator-to-tree
           tree-iterator-well-formed-p))

(defruled tree-in-of-tree-iterator-to-tree-of-cons
  (implies (tree-iterator-well-formed-p (cons tree iter))
           (equal (tree-in x (tree-iterator-to-tree (cons tree iter)))
                  (or (equal x (tagged-element->elem (tree->head tree)))
                      (tree-in x (tree->right tree))
                      (tree-in x (tree-iterator-to-tree iter)))))
  :enable tree-in-of-tree-iterator-to-tree)

;; (defruled tree-in-of-tree-iterator-to-tree-of-append0
;;   (implies (and (tree-iterator-well-formed-p (append x y))
;;                 (tree-in elem (tree-iterator-to-tree y)))
;;            (tree-in elem (tree-iterator-to-tree (append x y))))
;;   :induct (append x y)
;;   :enable (append
;;            tree-iterator-well-formed-p
;;            tree-in-of-tree-iterator-to-tree-of-cons
;;            ))

;; MOVE up
(defrule tree-iterator-to-tree-when-not-consp-cheap
  (implies (not (consp iter))
           (equal (tree-iterator-to-tree iter)
                  nil))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :enable tree-iterator-to-tree)

;;;;;;;;;;

;; GJ: remember where I am.
;; Overall goal is to show that tree-iterator-to-tree of tree-left-spine is
;; equal to the original tree.
;; - This will require that all the trees in the iterator are well formed.
;;   We can get this with the tree-iterator-well-formed-p invariant.
;;   It gives us a little more than we need, but I don't think that is a
;;   problem.
;; - We can start by proving tree-in of _ only when tree-in of original
;;   - As an intermediate step, characterize when tree-in of iterator-to-tree
;;     -

;; Introduce new function, all-well-formed-p, separate from the other.

(defrule tree-iterator-well-formed-p-of-append
  (implies ()
           (tree-iterator-well-formed-p (append x y)))
  :enable)

bstp-of-tree-iterator-to-tree

(defruled tree-in-of-tree-iterator-to-tree-of-append
  (implies (and (tree-iterator-well-formed-p x)
                (tree-iterator-well-formed-p y)
                (tree-in elem (tree-iterator-to-tree y)))
           (equal (tree-in elem (tree-iterator-to-tree (append x y)))
                  (or (tree-in elem (tree-iterator-to-tree x))
                      (tree-in elem (tree-iterator-to-tree y)))))
  ;; :induct (append x y)
  :induct (tree-iterator-to-tree x)
  :enable (tree-iterator-to-tree
           tree-iterator-well-formed-p
           append
           ;; bstp
           ;; tree-in-of-tree-iterator-to-tree-of-cons
           ))

.

;;;;;;;;;;

(defruled tree-in-of-tree-iterator-to-tree-of-append1
  (implies (and (tree-iterator-well-formed-p x)
                (tree-iterator-well-formed-p (append x y))
                (tree-in elem (tree-iterator-to-tree x)))
           (tree-in elem (tree-iterator-to-tree (append x y))))
  :induct (append x y)
  :expand (tree-iterator-to-tree (cons (car x) (append (cdr x) y)))
  :enable (append
           tree-iterator-well-formed-p
           tree-in-of-tree-iterator-to-tree-of-cons
           ))

(defruled tree-in-of-tree-iterator-to-tree-of-append2
  (implies (and (tree-iterator-well-formed-p (append x y))
                (tree-in elem (tree-iterator-to-tree (append x y))))
           (or (tree-in elem (tree-iterator-to-tree x))
               (tree-in elem (tree-iterator-to-tree y))))
  :induct (append x y)
  :expand (tree-in (tagged-element->elem (tree->head (car x)))
                   (tree-iterator-to-tree x))
  :enable (append
           tree-iterator-well-formed-p
           tree-in-of-tree-iterator-to-tree-of-cons
           endp
           ))

(defruled tree-in-of-tree-iterator-to-tree-of-append
  (implies (and (tree-iterator-p (append x y))
                (tree-iterator-well-formed-p (append x y)))
           (equal (tree-in elem (tree-iterator-to-tree (append x y)))
                  (or (tree-in elem (tree-iterator-to-tree x))
                      (tree-in elem (tree-iterator-to-tree y)))))
  :induct (append x y)
  :enable (append
           tree-iterator-well-formed-p
           ;; tree-in-of-tree-iterator-to-tree
           tree-in-of-tree-iterator-to-tree-of-cons
           tree-iterator-p
           endp
           ))

(defruled tree-iterator-to-tree-of-append
  (tree-subset-p (tree-iterator-to-tree (append x y))
                 (tree-union (tree-iterator-to-tree x)
                             (tree-iterator-to-tree y)))
  :induct t
  :enable (tree-iterator-to-tree
           ;; tree-subset-p-becomes-tree-subset-p-sk
           ;; tree-subset-p-sk
           ))

(defruled tree-iterator-to-tree-of-append
  (equal (tree-iterator-to-tree (append x y))
         (tree-union (tree-iterator-to-tree x)
                     (tree-iterator-to-tree y)))
  :induct t
  :enable tree-iterator-to-tree)

(defrule tree-iterator-to-tree-of-tree-left-spine
  (implies (and (treep tree)
                ;; (bstp tree)
                ;; (heapp tree)
                )
           (tree-subset-p (tree-iterator-to-tree (tree-left-spine tree))
                          tree))
  :induct t
  :enable (tree-left-spine
           tree-iterator-to-tree
           ))

(defrule tree-iterator-to-tree-of-tree-left-spine
  (implies (and (treep tree)
                (bstp tree)
                (heapp tree))
           (equal (tree-iterator-to-tree (tree-left-spine tree))
                  tree))
  )

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tree-iterator-done-p ((iter tree-iterator-p))
  :returns (yes/no booleanp :rule-classes :type-prescription)
  (endp iter)
  :inline t)

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t tree-iterator-done-p)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tree-iterator-value ((iter tree-iterator-p))
  :guard (not (tree-iterator-done-p iter))
  (tagged-element->elem (tree->head (first iter)))
  :inline t
  :guard-hints (("Goal" :in-theory (enable tree-iterator-p
                                           tree-iterator-done-p))))

;; TODO: equals tree-min (need more conditions on tree-iterator-p)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tree-iterator-next ((iter tree-iterator-p))
  :guard (not (tree-iterator-done-p iter))
  :returns (next tree-iterator-p)
  (let* ((iter (mbe :logic (if (tree-iterator-p iter)
                               iter
                             nil)
                    :exec iter))
         (right (tree->right (first iter))))
    (if (tree-empty-p right)
        (rest iter)
      (mbe :logic (append (tree-left-spine right)
                          iter)
           :exec (tree-left-spine-acc right iter)))))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t tree-iterator-next)))
