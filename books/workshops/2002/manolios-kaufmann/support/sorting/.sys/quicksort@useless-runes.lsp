(LESS)
(NOTLESS)
(QSORT
 (1320 616 (:REWRITE DEFAULT-+-2))
 (864 616 (:REWRITE DEFAULT-+-1))
 (418 110 (:REWRITE <<-TRICHOTOMY))
 (374 66 (:REWRITE <<-ASYMMETRIC))
 (290 58 (:DEFINITION LEN))
 (224 152 (:REWRITE DEFAULT-<-2))
 (204 202 (:REWRITE DEFAULT-CDR))
 (180 152 (:REWRITE DEFAULT-<-1))
 (152 150 (:REWRITE DEFAULT-CAR))
 (116 116 (:REWRITE DEFAULT-UNARY-MINUS))
 (110 110 (:REWRITE <<-TRANSITIVE))
 (58 58 (:REWRITE DEFAULT-NUMERATOR))
 (58 58 (:REWRITE DEFAULT-DENOMINATOR))
 (58 58 (:REWRITE DEFAULT-COERCE-2))
 (58 58 (:REWRITE DEFAULT-COERCE-1))
 (56 56 (:REWRITE DEFAULT-REALPART))
 (56 56 (:REWRITE DEFAULT-IMAGPART))
 )
(LESSP)
(NOTLESSP)
(PERM-LESS-NOTLESS
 (142 44 (:REWRITE <<-TRICHOTOMY))
 (140 12 (:DEFINITION IN))
 (132 44 (:TYPE-PRESCRIPTION TRUE-LISTP-APPEND))
 (126 26 (:REWRITE <<-ASYMMETRIC))
 (72 8 (:DEFINITION REMOVE-EL))
 (67 66 (:REWRITE DEFAULT-CAR))
 (53 52 (:REWRITE DEFAULT-CDR))
 (52 4 (:REWRITE PERM-REMOVE-EL-APP))
 (50 42 (:REWRITE <<-TRANSITIVE))
 (44 44 (:TYPE-PRESCRIPTION NOTLESS))
 (44 44 (:TYPE-PRESCRIPTION IN))
 (44 44 (:TYPE-PRESCRIPTION BINARY-APPEND))
 (24 24 (:REWRITE PERM-TRANSITIVE))
 (8 8 (:REWRITE CAR-PERM))
 (2 2 (:REWRITE <<-IRREFLEXIVE))
 )
(PERM-QSORT
 (180 6 (:DEFINITION NOTLESS))
 (171 45 (:REWRITE <<-TRICHOTOMY))
 (153 27 (:REWRITE <<-ASYMMETRIC))
 (108 108 (:TYPE-PRESCRIPTION <<))
 (90 3 (:DEFINITION LESS))
 (78 78 (:REWRITE DEFAULT-CAR))
 (64 64 (:REWRITE DEFAULT-CDR))
 (58 8 (:DEFINITION IN))
 (52 8 (:DEFINITION REMOVE-EL))
 (48 48 (:TYPE-PRESCRIPTION QSORT))
 (45 45 (:REWRITE <<-TRANSITIVE))
 (24 24 (:TYPE-PRESCRIPTION IN))
 (23 23 (:REWRITE PERM-TRANSITIVE))
 (14 8 (:REWRITE CAR-PERM))
 (12 12 (:TYPE-PRESCRIPTION NOTLESS))
 (12 12 (:TYPE-PRESCRIPTION LESS))
 )
(LESSP-LESS
 (192 56 (:REWRITE <<-TRICHOTOMY))
 (171 33 (:REWRITE <<-ASYMMETRIC))
 (62 54 (:REWRITE <<-TRANSITIVE))
 (16 15 (:REWRITE DEFAULT-CAR))
 (11 10 (:REWRITE DEFAULT-CDR))
 (2 2 (:REWRITE <<-IRREFLEXIVE))
 )
(NOTLESSP-NOTLESS
 (192 55 (:REWRITE <<-TRICHOTOMY))
 (171 33 (:REWRITE <<-ASYMMETRIC))
 (58 54 (:REWRITE <<-TRANSITIVE))
 (16 15 (:REWRITE DEFAULT-CAR))
 (11 10 (:REWRITE DEFAULT-CDR))
 (1 1 (:REWRITE <<-IRREFLEXIVE))
 )
(PERM-IMPLIES-EQUAL-LESSP-2
 (1511 423 (:REWRITE <<-TRICHOTOMY))
 (1348 252 (:REWRITE <<-ASYMMETRIC))
 (447 415 (:REWRITE <<-TRANSITIVE))
 (419 56 (:REWRITE PERM-SYMMETRIC))
 (279 279 (:REWRITE DEFAULT-CAR))
 (214 214 (:REWRITE DEFAULT-CDR))
 (77 7 (:REWRITE REMOVE-EL-SWAP))
 (56 56 (:REWRITE PERM-TRANSITIVE))
 (22 22 (:REWRITE CAR-PERM))
 (8 8 (:REWRITE <<-IRREFLEXIVE))
 (7 7 (:REWRITE REMOVE-EL-IN))
 )
(PERM-IMPLIES-EQUAL-NOTLESSP-2
 (1511 422 (:REWRITE <<-TRICHOTOMY))
 (1348 252 (:REWRITE <<-ASYMMETRIC))
 (443 415 (:REWRITE <<-TRANSITIVE))
 (419 56 (:REWRITE PERM-SYMMETRIC))
 (279 279 (:REWRITE DEFAULT-CAR))
 (214 214 (:REWRITE DEFAULT-CDR))
 (77 7 (:REWRITE REMOVE-EL-SWAP))
 (56 56 (:REWRITE PERM-TRANSITIVE))
 (22 22 (:REWRITE CAR-PERM))
 (7 7 (:REWRITE REMOVE-EL-IN))
 (7 7 (:REWRITE <<-IRREFLEXIVE))
 )
(LESSP-LESS-QSORT)
(NOTLESSP-NOTLESS-QSORT)
(ORDEREDP-LEMMA
 (2678 468 (:REWRITE <<-TRICHOTOMY))
 (1217 224 (:REWRITE <<-ASYMMETRIC))
 (468 468 (:REWRITE <<-TRANSITIVE))
 (277 178 (:REWRITE DEFAULT-CDR))
 (19 19 (:REWRITE <<-IRREFLEXIVE))
 )
(QSORT-IS-ORDERED
 (146 38 (:REWRITE <<-TRICHOTOMY))
 (120 4 (:DEFINITION NOTLESS))
 (110 22 (:REWRITE <<-ASYMMETRIC))
 (96 96 (:TYPE-PRESCRIPTION <<))
 (92 4 (:DEFINITION ORDEREDP))
 (60 2 (:DEFINITION LESS))
 (56 4 (:DEFINITION <<=))
 (48 4 (:REWRITE <<-IMPLIES-LEXORDER))
 (38 38 (:REWRITE DEFAULT-CAR))
 (38 38 (:REWRITE <<-TRANSITIVE))
 (36 36 (:REWRITE DEFAULT-CDR))
 (14 14 (:TYPE-PRESCRIPTION QSORT))
 (4 4 (:TYPE-PRESCRIPTION LEXORDER))
 (4 4 (:REWRITE LEXORDER-TRANSITIVE))
 )
(QSORT-MAIN)
