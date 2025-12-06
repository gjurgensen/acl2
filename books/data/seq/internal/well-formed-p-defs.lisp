; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "SEQ")

(include-book "data/utilities/nat-defs" :dir :system)

(include-book "ftree-defs")

(local (include-book "std/util/defredundant" :dir :system))
(local (include-book "well-formed-p"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defredundant
  :names (elem-depth-p
          digit-depth-p
          ftree-depth-p
          elem-len
          digit-len
          ftree-len
          elem-len-invariant?
          elem-len-invariant-p
          digit-len-invariant?
          digit-len-invariant-p
          ftree-len-invariant?
          ftree-len-invariant-p
          ftree-well-formed-p
          elem-len-cached
          digit-len-cached
          ftree-len-cached
          digit1$
          digit2$
          digit3$
          digit4$
          digit$
          digit1$node
          digit2$node
          digit3$node
          digit4$node
          digit$node
          node2$
          node3$
          node$
          node2$node
          node3$node
          node$node
          ftree-deep$
          ))
