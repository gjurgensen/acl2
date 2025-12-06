; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "SEQ")

(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)

(include-book "ftree-defs")
(include-book "pop-defs")
(include-book "well-formed-p-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(local (include-book "ftree"))
(local (include-book "pop"))
(local (include-book "well-formed-p"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ftree-drop-front ((tree ftreep))
  :guard (not (ftree-empty-p tree))
  :returns (tree$ ftreep :rule-classes (:rewrite :type-prescription))
  (mbe :logic
       (mv-let (front tree$)
               (ftree-pop-front tree)
         (declare (ignore front))
         tree$)
       :exec
       (if (ftree-single-p tree)
           nil
         (let* ((prefix (ftree-deep->prefix tree))
                (tail-prefix? (digit-tail prefix))
                (middle (ftree-deep->middle tree)))
           (if tail-prefix?
               (ftree-deep tail-prefix? middle (ftree-deep->suffix tree))
             (if (ftree-empty-p middle)
                 (digit-to-ftree (ftree-deep->suffix tree))
               (mv-let (front$ middle$)
                       (ftree-pop-front middle)
                 (ftree-deep (digit front$)
                             middle$
                             (ftree-deep->suffix tree))))))))
  :guard-hints (("Goal" :in-theory (enable ftree-pop-front)))
  :inline t)

;;;;;;;;;;;;;;;;;;;;

(defrule ftree-drop-front-when-ftree-equal-congruence
  (implies (ftree-equal tree0 tree1)
           (equal (ftree-drop-front tree0)
                  (ftree-drop-front tree1)))
  :rule-classes :congruence
  :enable ftree-drop-front)

(defrule ftree-well-formed-p-of-ftree-drop-front
  (implies (and (ftree-well-formed-p depth tree)
                (not (ftree-empty-p tree)))
           (ftree-well-formed-p depth (ftree-drop-front tree)))
  :enable ftree-drop-front)

(defrule ftree-well-formed-p-0-of-ftree-drop-front
  (implies (ftree-well-formed-p 0 tree)
           (ftree-well-formed-p 0 (ftree-drop-front tree)))
  :enable ftree-drop-front)

(defruled ftree-pop-front-becomes-front-and-drop-front
  (equal (ftree-pop-front tree)
         (mv (ftree-front tree)
             (ftree-drop-front tree)))
  :expand (ftree-pop-front tree)
  :enable ftree-drop-front)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ftree-drop-back ((tree ftreep))
  :guard (not (ftree-empty-p tree))
  :returns (tree$ ftreep :rule-classes (:rewrite :type-prescription))
  (mbe :logic
       (mv-let (back tree$)
               (ftree-pop-back tree)
         (declare (ignore back))
         tree$)
       :exec
       (if (ftree-single-p tree)
           nil
         (let* ((suffix (ftree-deep->suffix tree))
                (liat-suffix? (digit-liat suffix))
                (middle (ftree-deep->middle tree)))
           (if liat-suffix?
               (ftree-deep (ftree-deep->prefix tree) middle liat-suffix?)
             (if (ftree-empty-p middle)
                 (digit-to-ftree (ftree-deep->prefix tree))
               (mv-let (back$ middle$)
                       (ftree-pop-back middle)
                 (ftree-deep (ftree-deep->prefix tree)
                             middle$
                             (digit back$))))))))
  :guard-hints (("Goal" :in-theory (enable ftree-pop-back)))
  :inline t)

;;;;;;;;;;;;;;;;;;;;

(defrule ftree-drop-back-when-ftree-equal-congruence
  (implies (ftree-equal tree0 tree1)
           (equal (ftree-drop-back tree0)
                  (ftree-drop-back tree1)))
  :rule-classes :congruence
  :enable ftree-drop-back)

(defrule ftree-well-formed-p-of-ftree-drop-back
  (implies (and (ftree-well-formed-p depth tree)
                (not (ftree-empty-p tree)))
           (ftree-well-formed-p depth (ftree-drop-back tree)))
  :enable ftree-drop-back)

(defrule ftree-well-formed-p-0-of-ftree-drop-back
  (implies (ftree-well-formed-p 0 tree)
           (ftree-well-formed-p 0 (ftree-drop-back tree)))
  :enable ftree-drop-back)

(defruled ftree-pop-back-becomes-back-and-drop-back
  (equal (ftree-pop-back tree)
         (mv (ftree-back tree)
             (ftree-drop-back tree)))
  :expand (ftree-pop-back tree)
  :enable ftree-drop-back)
