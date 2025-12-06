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

(include-book "internal/front-back-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(local (include-book "seq"))

(local (include-book "internal/front-back"))
(local (include-book "internal/ftree"))
(local (include-book "internal/well-formed-p"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define front ((seq seqp))
  :guard (not (emptyp seq))
  (ftree-front (seq-fix seq))
  :guard-hints (("Goal" :in-theory (enable emptyp
                                           seqp
                                           empty
                                           ftree-empty-p))))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t front)))

(defrule front-when-seq-equal-congruence
  (implies (seq-equal seq0 seq1)
           (equal (front seq0)
                  (front seq1)))
  :rule-classes :congruence
  :enable front)
