; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "SEQ")

(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)

(include-book "seq-defs")

(include-book "internal/drop-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(local (include-book "seq"))

(local (include-book "internal/ftree"))
(local (include-book "internal/drop"))
(local (include-book "internal/well-formed-p"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define drop-front ((seq seqp))
  :guard (not (emptyp seq))
  :returns (seq$ seqp
                 :hints (("Goal" :in-theory (enable seqp
                                                    seq-fix
                                                    empty))))
  (ftree-drop-front (seq-fix seq))
  :guard-hints (("Goal" :in-theory (enable seqp
                                           emptyp
                                           empty
                                           ftree-empty-p))))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t drop-front)))

(defrule drop-front-when-seq-equal-congruence
  (implies (seq-equal seq0 seq1)
           (equal (drop-front seq0)
                  (drop-front seq1)))
  :rule-classes :congruence
  :enable drop-front)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; TODO: drop-back
