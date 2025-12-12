; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "TREESET")

(include-book "data/utilities/total-order-defs" :dir :system)

(include-book "../hash-defs")

(local (include-book "std/util/defredundant" :dir :system))
(local (include-book "bst-order"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defredundant
  :names (bst<
          ;; bst<-with-hashes
          acl2-number-bst<
          symbol-bst<
          eqlable-bst<
          ))

;; (add-macro-alias bst< bst<$inline)
;; (add-macro-alias bst<-with-hashes bst<-with-hashes$inline)
