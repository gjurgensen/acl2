; Copyright (C) 2025 by Kestrel Institute
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "SEQ")

(include-book "xdoc/constructors" :dir :system)

(include-book "seq")
(include-book "push")
(include-book "drop")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc sequences
  :parents (data-lib)
  :short
  (xdoc::topstring
    "A data structure for sequences.")
  :long
  (xdoc::topstring
    (xdoc::p
      "This sequence data structure offers O(1) amortized access to the front
       and back of the sequence, O(log n) random access, and O(log n)
       concatenation.")
    (xdoc::p
      "The implementation is based on finger trees.")))
