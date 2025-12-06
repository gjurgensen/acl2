; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "SEQ")

(include-book "data/utilities/true-list-defs" :dir :system)

(include-book "well-formed-p-defs")

(local (include-book "std/util/defredundant" :dir :system))
(local (include-book "to-list"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defredundant
  :names (node-to-list-with-depth-acc
          node-to-list-with-depth
          digit-to-list-with-depth-acc
          digit-to-list-with-depth
          ftree-to-list-with-depth-acc
          ftree-to-list-with-depth
          ))
