; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "SEQ")

(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)

(include-book "drop-defs")
(include-book "front-back-defs")

(include-book "internal/drop-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(local (include-book "drop"))
(local (include-book "front-back"))
(local (include-book "seq"))

(local (include-book "internal/drop"))
(local (include-book "internal/front-back"))
(local (include-book "internal/ftree"))
(local (include-book "internal/pop"))
(local (include-book "internal/well-formed-p"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pop-front ((seq seqp))
  :guard (not (emptyp seq))
  :returns (mv (front t) (seq$ seqp))
  (mbe :logic (mv (front seq) (drop-front seq))
       :exec (ftree-pop-front seq))
  :enabled t
  :inline t
  :guard-hints (("Goal" :in-theory (enable seqp
                                           ftree-pop-front-becomes-front-and-drop-front
                                           front
                                           drop-front
                                           emptyp
                                           empty
                                           ftree-empty-p))))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t pop-front)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; TODO: pop-back
