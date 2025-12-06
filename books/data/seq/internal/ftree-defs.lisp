; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "SEQ")

(include-book "data/utilities/nat-defs" :dir :system)

(local (include-book "std/util/defredundant" :dir :system))
(local (include-book "ftree"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defredundant
  :names (digitp
          irr-digit
          digit-fix
          digit-equal
          digit-case
          digit->len
          digit1->fst
          digit2->fst
          digit2->snd
          digit3->fst
          digit3->snd
          digit3->thd
          digit4->fst
          digit4->snd
          digit4->thd
          digit4->frth
          digit->head
          digit->last
          digit1
          digit2
          digit3
          digit4
          digit
          nodep
          irr-node
          node-fix
          node-equal
          node2p
          node->len
          node->fst
          node2->snd
          node2->snd
          node3->snd
          node3->thd
          node2
          node3
          node
          ftreep
          ftree-fix
          ftree-equal
          ftree-empty-p
          ftree-single-p
          ftree-single-p-no-guard
          ftree-single->elem
          ftree-deep-p-no-guard
          ftree-deep->len
          ftree-deep->prefix
          ftree-deep->suffix
          ftree-deep->middle
          ftree-single
          ftree-deep
          ))

(defequiv digit-equal)
(defequiv node-equal)
(defequiv ftree-equal)
