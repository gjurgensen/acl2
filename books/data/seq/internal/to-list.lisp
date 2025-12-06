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

;; TODO: where does well-formed-p come in? Do we even use it for anything?

(define ftree-to-list-acc
  ((tree ftreep)
   (acc true-listp))
  :returns (list true-listp :rule-classes (:rewrite :type-prescription))
  (if (ftree-empty-p tree)
      (data::list-fix acc)
    (mv-let (back tree$)
            (ftree-pop-back tree)
      (ftree-to-list-acc tree$ (cons back acc)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ftree-to-list-acc ((tree ftreep))
  :guard (ftree)
  )
