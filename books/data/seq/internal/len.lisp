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

;; (local (include-book "kestrel/utilities/ordinals" :dir :system))

(local (include-book "ftree"))
(local (include-book "well-formed-p"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define node?-depth-len
  ((depth natp)
   node)
  (declare (xargs :split-types t)
           (type unsigned-byte depth)
           (type cons digit))
  )

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define digit-len ((digit digitp))
  (declare (xargs :split-types t)
           (type cons digit))
  :returns (len natp :rule-classes :type-prescription)
  (the (integer 1 4) (digit-case digit))
  :inline t)

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t digit-len)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
