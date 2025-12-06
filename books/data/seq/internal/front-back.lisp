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
(include-book "well-formed-p-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(local (include-book "ftree"))
(local (include-book "well-formed-p"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ftree-front ((tree ftreep))
  :guard (not (ftree-empty-p tree))
  (if (mbt (not (ftree-empty-p tree)))
      (if (ftree-single-p tree)
          (ftree-single->elem tree)
        (digit->fst (ftree-deep->prefix tree)))
    nil)
  :inline t)

;;;;;;;;;;;;;;;;;;;;

(defrule ftree-front-when-ftree-equal-congruence
  (implies (ftree-equal tree0 tree1)
           (equal (ftree-front tree0)
                  (ftree-front tree1)))
  :rule-classes :congruence
  :expand ((ftree-front tree0)
           (ftree-front tree1)))

(defruled node?-depth-p-of-ftree-front
  (implies (and (ftree-well-formed-p depth tree)
                (not (ftree-empty-p tree)))
           (node?-depth-p depth (ftree-front tree)))
  :enable ftree-front)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ftree-back ((tree ftreep))
  :guard (not (ftree-empty-p tree))
  (if (mbt (not (ftree-empty-p tree)))
      (if (ftree-single-p tree)
          (ftree-single->elem tree)
        (digit->last (ftree-deep->suffix tree)))
    nil)
  :inline t)

;;;;;;;;;;;;;;;;;;;;

(defrule ftree-back-when-ftree-equal-congruence
  (implies (ftree-equal tree0 tree1)
           (equal (ftree-back tree0)
                  (ftree-back tree1)))
  :rule-classes :congruence
  :expand ((ftree-back tree0)
           (ftree-back tree1)))

(defruled node?-depth-p-of-ftree-back
  (implies (and (ftree-well-formed-p depth tree)
                (not (ftree-empty-p tree)))
           (node?-depth-p depth (ftree-back tree)))
  :enable (ftree-back
           ;; TODO: there should be a node?-depth-p rule about digit->last
           ;; instead of opening it up.
           digit->last
           ))
