(INTEGERP-OF-MV-NTH-0-OF-GENRANDOM
 (227 5 (:REWRITE MOD-WHEN-<))
 (105 5 (:REWRITE MOD-WHEN-MULTIPLE))
 (105 5 (:REWRITE MOD-WHEN-INTEGERP-OF-QUOTIENT))
 (68 1 (:LINEAR MOD-BOUND-LINEAR-ARG1))
 (65 1 (:LINEAR MOD-BOUND-LINEAR-ARG2-STRONG))
 (61 1 (:LINEAR MOD-BOUND-LINEAR-ARG2))
 (58 10 (:REWRITE MULTIPLE-WHEN-MOD-0-CHEAP))
 (46 10 (:REWRITE COMMUTATIVITY-OF-*))
 (38 21 (:REWRITE DEFAULT-*-2))
 (37 21 (:REWRITE DEFAULT-*-1))
 (13 5 (:REWRITE MOD-WHEN-RATIONALP-ARG1-AND-NOT-RATIONALP-ARG2))
 (13 5 (:REWRITE MOD-WHEN-NOT-RATIONALP-ARG1-AND-RATIONALP-ARG2))
 (13 5 (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG1))
 (13 5 (:REWRITE MOD-WHEN-<-OF-0))
 (13 5 (:REWRITE DEFAULT-<-1))
 (11 11 (:REWRITE INTEGERP-FROM-UNSIGNED-BYTE-P-SIZE-PARAM))
 (10 1 (:REWRITE DEFAULT-CDR))
 (8 1 (:REWRITE CONSP-FROM-LEN-CHEAP))
 (5 5 (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG2))
 (5 5 (:REWRITE MOD-WHEN-EQUAL-OF-MOD-AND-0-FREE-CHEAP))
 (5 5 (:REWRITE DEFAULT-<-2))
 (5 5 (:REWRITE <-WHEN-BVLT))
 (4 4 (:TYPE-PRESCRIPTION LEN))
 (4 4 (:REWRITE MOD-OF-*-SUBST-CONSTANT-ARG2))
 (4 4 (:REWRITE MOD-OF-*-SUBST-CONSTANT-ARG1))
 (3 3 (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE))
 (3 1 (:LINEAR LEN-POSITIVE-WHEN-CONSP-LINEAR-CHEAP))
 (2 2 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
 (2 2 (:REWRITE DEFAULT-UNARY-/))
 (1 1 (:REWRITE MOD-OF-MOD-WHEN-MULTIPLE-SAFE))
 (1 1 (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT))
 )
(<=-OF-0-AND-MV-NTH-0-OF-GENRANDOM
 (227 5 (:REWRITE MOD-WHEN-<))
 (105 5 (:REWRITE MOD-WHEN-MULTIPLE))
 (105 5 (:REWRITE MOD-WHEN-INTEGERP-OF-QUOTIENT))
 (68 1 (:LINEAR MOD-BOUND-LINEAR-ARG1))
 (65 1 (:LINEAR MOD-BOUND-LINEAR-ARG2-STRONG))
 (61 1 (:LINEAR MOD-BOUND-LINEAR-ARG2))
 (58 10 (:REWRITE MULTIPLE-WHEN-MOD-0-CHEAP))
 (46 10 (:REWRITE COMMUTATIVITY-OF-*))
 (38 21 (:REWRITE DEFAULT-*-2))
 (37 21 (:REWRITE DEFAULT-*-1))
 (23 7 (:REWRITE DEFAULT-<-1))
 (13 5 (:REWRITE MOD-WHEN-RATIONALP-ARG1-AND-NOT-RATIONALP-ARG2))
 (13 5 (:REWRITE MOD-WHEN-NOT-RATIONALP-ARG1-AND-RATIONALP-ARG2))
 (13 5 (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG1))
 (13 5 (:REWRITE MOD-WHEN-<-OF-0))
 (11 11 (:REWRITE INTEGERP-FROM-UNSIGNED-BYTE-P-SIZE-PARAM))
 (10 1 (:REWRITE DEFAULT-CDR))
 (8 1 (:REWRITE CONSP-FROM-LEN-CHEAP))
 (7 7 (:REWRITE DEFAULT-<-2))
 (7 7 (:REWRITE <-WHEN-BVLT))
 (5 5 (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG2))
 (5 5 (:REWRITE MOD-WHEN-EQUAL-OF-MOD-AND-0-FREE-CHEAP))
 (4 4 (:TYPE-PRESCRIPTION LEN))
 (4 4 (:REWRITE MOD-OF-*-SUBST-CONSTANT-ARG2))
 (4 4 (:REWRITE MOD-OF-*-SUBST-CONSTANT-ARG1))
 (3 1 (:LINEAR LEN-POSITIVE-WHEN-CONSP-LINEAR-CHEAP))
 (2 2 (:REWRITE SIZE-NON-NEGATIVE-WHEN-UNSIGNED-BYTE-P-FREE))
 (2 2 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
 (2 2 (:REWRITE DEFAULT-UNARY-/))
 (2 2 (:REWRITE BOUND-WHEN-USB))
 (1 1 (:REWRITE MOD-OF-MOD-WHEN-MULTIPLE-SAFE))
 (1 1 (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT))
 )
(NATP-OF-MV-NTH-0-OF-GENRANDOM)
(GEN-RANDOM-BV
 (8 8 (:REWRITE BOUND-WHEN-USB))
 (8 8 (:REWRITE <-WHEN-BVLT))
 (7 7 (:REWRITE DEFAULT-<-2))
 (7 7 (:REWRITE DEFAULT-<-1))
 (5 5 (:REWRITE SIZE-NON-NEGATIVE-WHEN-UNSIGNED-BYTE-P-FREE))
 (3 3 (:REWRITE INTEGERP-FROM-UNSIGNED-BYTE-P-SIZE-PARAM))
 (2 2 (:REWRITE USE-ALL-NATP-2))
 (2 2 (:REWRITE USE-ALL-NATP))
 (2 2 (:REWRITE NATP-WHEN-UNSIGNED-BYTE-P-SIZE-ARG))
 (2 2 (:REWRITE NATP-WHEN-UNSIGNED-BYTE-P))
 (1 1 (:REWRITE DEFAULT-+-2))
 (1 1 (:REWRITE DEFAULT-+-1))
 )
(INTEGERP-OF-MV-NTH-0-OF-GEN-RANDOM-BV
 (1338 56 (:REWRITE MOD-WHEN-MULTIPLE))
 (702 112 (:REWRITE MULTIPLE-WHEN-MOD-0-CHEAP))
 (558 112 (:REWRITE COMMUTATIVITY-OF-*))
 (558 8 (:LINEAR MOD-BOUND-LINEAR-ARG1))
 (510 250 (:REWRITE DEFAULT-*-2))
 (488 8 (:LINEAR MOD-BOUND-LINEAR-ARG2))
 (472 250 (:REWRITE DEFAULT-*-1))
 (158 58 (:REWRITE MOD-WHEN-<-OF-0))
 (150 75 (:REWRITE DEFAULT-<-1))
 (142 51 (:REWRITE MOD-WHEN-RATIONALP-ARG1-AND-NOT-RATIONALP-ARG2))
 (126 51 (:REWRITE MOD-WHEN-NOT-RATIONALP-ARG1-AND-RATIONALP-ARG2))
 (126 51 (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG1))
 (124 124 (:REWRITE INTEGERP-FROM-UNSIGNED-BYTE-P-SIZE-PARAM))
 (122 14 (:REWRITE DEFAULT-CDR))
 (96 12 (:REWRITE CONSP-FROM-LEN-CHEAP))
 (91 75 (:REWRITE DEFAULT-<-2))
 (80 16 (:REWRITE DEFAULT-UNARY-/))
 (76 76 (:REWRITE <-WHEN-BVLT))
 (67 51 (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG2))
 (57 57 (:REWRITE MOD-WHEN-EQUAL-OF-MOD-AND-0-FREE-CHEAP))
 (48 48 (:TYPE-PRESCRIPTION LEN))
 (43 43 (:REWRITE MOD-OF-*-SUBST-CONSTANT-ARG2))
 (43 43 (:REWRITE MOD-OF-*-SUBST-CONSTANT-ARG1))
 (42 12 (:REWRITE COMMUTATIVITY-OF-+))
 (38 38 (:REWRITE DEFAULT-+-2))
 (38 38 (:REWRITE DEFAULT-+-1))
 (36 12 (:LINEAR LEN-POSITIVE-WHEN-CONSP-LINEAR-CHEAP))
 (25 25 (:REWRITE BOUND-WHEN-USB))
 (24 24 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
 (20 8 (:REWRITE ZIP-OPEN))
 (18 18 (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE))
 (16 2 (:REWRITE INTEGERP-OF-MOD))
 (12 12 (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT))
 (12 4 (:REWRITE FOLD-CONSTS-IN-+))
 (8 8 (:REWRITE USE-ALL-NATP-2))
 (8 8 (:REWRITE USE-ALL-NATP))
 (8 8 (:REWRITE SIZE-NON-NEGATIVE-WHEN-UNSIGNED-BYTE-P-FREE))
 (8 8 (:REWRITE NATP-WHEN-UNSIGNED-BYTE-P-SIZE-ARG))
 (8 8 (:REWRITE NATP-WHEN-UNSIGNED-BYTE-P))
 (5 1 (:REWRITE +-OF---AND-0))
 (2 2 (:REWRITE CDR-CONS))
 (1 1 (:REWRITE EQUAL-WHEN-BVLT-ALT))
 (1 1 (:REWRITE EQUAL-WHEN-BVLT))
 (1 1 (:REWRITE EQUAL-OF-CONSTANT-WHEN-SBVLT))
 (1 1 (:REWRITE EQUAL-OF-CONSTANT-WHEN-NOT-BVLT-CONSTANT-2))
 (1 1 (:REWRITE EQUAL-OF-CONSTANT-WHEN-NOT-BVLT-CONSTANT-1))
 (1 1 (:REWRITE EQUAL-OF-CONSTANT-WHEN-BVLT-CONSTANT-2-ALT))
 (1 1 (:REWRITE EQUAL-OF-CONSTANT-WHEN-BVLT-CONSTANT-2))
 (1 1 (:REWRITE EQUAL-OF-CONSTANT-WHEN-BVLT-CONSTANT-1-ALT))
 (1 1 (:REWRITE EQUAL-OF-CONSTANT-WHEN-BVLT-CONSTANT-1))
 (1 1 (:REWRITE EQUAL-OF-0-WHEN-BVLT))
 (1 1 (:REWRITE EQUAL-CONSTANT-WHEN-NOT-SBVLT))
 (1 1 (:REWRITE EQUAL-CONSTANT-WHEN-BVCHOP-EQUAL-CONSTANT-FALSE))
 )
(GEN-RANDOM-BV
 (128 118 (:REWRITE DEFAULT-<-2))
 (118 118 (:REWRITE DEFAULT-<-1))
 (118 118 (:REWRITE BOUND-WHEN-USB))
 (118 118 (:REWRITE <-WHEN-BVLT))
 (97 97 (:REWRITE DEFAULT-+-2))
 (97 97 (:REWRITE DEFAULT-+-1))
 (42 22 (:REWRITE DEFAULT-*-2))
 (22 22 (:REWRITE DEFAULT-*-1))
 (14 14 (:REWRITE INTEGERP-FROM-UNSIGNED-BYTE-P-SIZE-PARAM))
 (1 1 (:REWRITE ZIP-OPEN))
 (1 1 (:REWRITE USE-ALL-NATP-2))
 (1 1 (:REWRITE USE-ALL-NATP))
 (1 1 (:REWRITE SIZE-NON-NEGATIVE-WHEN-UNSIGNED-BYTE-P-FREE))
 (1 1 (:REWRITE NATP-WHEN-UNSIGNED-BYTE-P-SIZE-ARG))
 (1 1 (:REWRITE NATP-WHEN-UNSIGNED-BYTE-P))
 )
(GEN-RANDOM-INTEGER
 (5 4 (:REWRITE DEFAULT-<-2))
 (4 4 (:REWRITE DEFAULT-<-1))
 (4 4 (:REWRITE BOUND-WHEN-USB))
 (4 4 (:REWRITE <-WHEN-BVLT))
 (3 3 (:REWRITE EQUAL-WHEN-BVLT-ALT))
 (3 3 (:REWRITE EQUAL-WHEN-BVLT))
 (3 3 (:REWRITE EQUAL-OF-CONSTANT-WHEN-SBVLT))
 (3 3 (:REWRITE EQUAL-OF-CONSTANT-WHEN-NOT-BVLT-CONSTANT-2))
 (3 3 (:REWRITE EQUAL-OF-CONSTANT-WHEN-NOT-BVLT-CONSTANT-1))
 (3 3 (:REWRITE EQUAL-OF-CONSTANT-WHEN-BVLT-CONSTANT-2-ALT))
 (3 3 (:REWRITE EQUAL-OF-CONSTANT-WHEN-BVLT-CONSTANT-2))
 (3 3 (:REWRITE EQUAL-OF-CONSTANT-WHEN-BVLT-CONSTANT-1-ALT))
 (3 3 (:REWRITE EQUAL-OF-CONSTANT-WHEN-BVLT-CONSTANT-1))
 (3 3 (:REWRITE EQUAL-CONSTANT-WHEN-NOT-SBVLT))
 (3 3 (:REWRITE EQUAL-CONSTANT-WHEN-BVCHOP-EQUAL-CONSTANT-FALSE))
 (2 2 (:REWRITE INTEGERP-FROM-UNSIGNED-BYTE-P-SIZE-PARAM))
 (1 1 (:TYPE-PRESCRIPTION RATIONALP-OF-MOD))
 (1 1 (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE-2))
 (1 1 (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE))
 (1 1 (:TYPE-PRESCRIPTION INTEGERP-OF-MOD-TYPE))
 (1 1 (:REWRITE EQUAL-OF-0-WHEN-BVLT))
 )
(INTEGERP-OF-MV-NTH-0-OF-GEN-RANDOM-INTEGER
 (20 1 (:REWRITE MOD-WHEN-INTEGERP-OF-QUOTIENT))
 (14 1 (:REWRITE MOD-WHEN-MULTIPLE))
 (12 2 (:REWRITE MULTIPLE-WHEN-MOD-0-CHEAP))
 (9 2 (:REWRITE COMMUTATIVITY-OF-*))
 (7 4 (:REWRITE DEFAULT-*-2))
 (7 4 (:REWRITE DEFAULT-*-1))
 (7 1 (:REWRITE MOD-WHEN-<-OF-0))
 (6 3 (:REWRITE DEFAULT-<-1))
 (4 4 (:TYPE-PRESCRIPTION RATIONALP-OF-MOD))
 (4 4 (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE-2))
 (4 4 (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE))
 (4 4 (:TYPE-PRESCRIPTION INTEGERP-OF-MOD-TYPE))
 (4 4 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (4 4 (:REWRITE INTEGERP-FROM-UNSIGNED-BYTE-P-SIZE-PARAM))
 (4 4 (:REWRITE ACL2-NUMBERP-WHEN-UNSIGNED-BYTE-P))
 (4 4 (:REWRITE ACL2-NUMBERP-FROM-UNSIGNED-BYTE-P-SIZE-PARAM))
 (4 1 (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG1))
 (4 1 (:REWRITE MOD-WHEN-<))
 (3 3 (:REWRITE DEFAULT-<-2))
 (3 3 (:REWRITE <-WHEN-BVLT))
 (2 2 (:REWRITE DEFAULT-UNARY-/))
 (1 1 (:REWRITE MOD-WHEN-RATIONALP-ARG1-AND-NOT-RATIONALP-ARG2))
 (1 1 (:REWRITE MOD-WHEN-NOT-RATIONALP-ARG1-AND-RATIONALP-ARG2))
 (1 1 (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG2))
 (1 1 (:REWRITE MOD-WHEN-EQUAL-OF-MOD-AND-0-FREE-CHEAP))
 (1 1 (:REWRITE EQUAL-WHEN-BVLT-ALT))
 (1 1 (:REWRITE EQUAL-WHEN-BVLT))
 (1 1 (:REWRITE EQUAL-OF-CONSTANT-WHEN-SBVLT))
 (1 1 (:REWRITE EQUAL-OF-CONSTANT-WHEN-NOT-BVLT-CONSTANT-2))
 (1 1 (:REWRITE EQUAL-OF-CONSTANT-WHEN-NOT-BVLT-CONSTANT-1))
 (1 1 (:REWRITE EQUAL-OF-CONSTANT-WHEN-BVLT-CONSTANT-2-ALT))
 (1 1 (:REWRITE EQUAL-OF-CONSTANT-WHEN-BVLT-CONSTANT-2))
 (1 1 (:REWRITE EQUAL-OF-CONSTANT-WHEN-BVLT-CONSTANT-1-ALT))
 (1 1 (:REWRITE EQUAL-OF-CONSTANT-WHEN-BVLT-CONSTANT-1))
 (1 1 (:REWRITE EQUAL-CONSTANT-WHEN-NOT-SBVLT))
 (1 1 (:REWRITE EQUAL-CONSTANT-WHEN-BVCHOP-EQUAL-CONSTANT-FALSE))
 (1 1 (:REWRITE BOUND-WHEN-USB))
 )
(ACL2-NUMBERP-OF-MV-NTH-0-OF-GEN-RANDOM-INTEGER
 (27 1 (:REWRITE MOD-WHEN-INTEGERP-OF-QUOTIENT))
 (14 1 (:REWRITE MOD-WHEN-MULTIPLE))
 (12 2 (:REWRITE MULTIPLE-WHEN-MOD-0-CHEAP))
 (9 9 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (9 9 (:REWRITE ACL2-NUMBERP-WHEN-UNSIGNED-BYTE-P))
 (9 9 (:REWRITE ACL2-NUMBERP-FROM-UNSIGNED-BYTE-P-SIZE-PARAM))
 (9 2 (:REWRITE DEFAULT-UNARY-/))
 (9 2 (:REWRITE COMMUTATIVITY-OF-*))
 (7 4 (:REWRITE DEFAULT-*-2))
 (7 4 (:REWRITE DEFAULT-*-1))
 (7 1 (:REWRITE MOD-WHEN-<-OF-0))
 (7 1 (:REWRITE MOD-WHEN-<))
 (5 2 (:REWRITE DEFAULT-<-2))
 (5 2 (:REWRITE DEFAULT-<-1))
 (4 1 (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG2))
 (4 1 (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG1))
 (4 1 (:DEFINITION NOT))
 (3 3 (:TYPE-PRESCRIPTION RATIONALP-OF-MOD))
 (3 3 (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE-2))
 (3 3 (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE))
 (3 3 (:TYPE-PRESCRIPTION INTEGERP-OF-MOD-TYPE))
 (2 2 (:REWRITE INTEGERP-FROM-UNSIGNED-BYTE-P-SIZE-PARAM))
 (2 2 (:REWRITE <-WHEN-BVLT))
 (1 1 (:REWRITE MOD-WHEN-RATIONALP-ARG1-AND-NOT-RATIONALP-ARG2))
 (1 1 (:REWRITE MOD-WHEN-NOT-RATIONALP-ARG1-AND-RATIONALP-ARG2))
 (1 1 (:REWRITE MOD-WHEN-EQUAL-OF-MOD-AND-0-FREE-CHEAP))
 (1 1 (:REWRITE EQUAL-WHEN-BVLT-ALT))
 (1 1 (:REWRITE EQUAL-WHEN-BVLT))
 (1 1 (:REWRITE EQUAL-OF-CONSTANT-WHEN-SBVLT))
 (1 1 (:REWRITE EQUAL-OF-CONSTANT-WHEN-NOT-BVLT-CONSTANT-2))
 (1 1 (:REWRITE EQUAL-OF-CONSTANT-WHEN-NOT-BVLT-CONSTANT-1))
 (1 1 (:REWRITE EQUAL-OF-CONSTANT-WHEN-BVLT-CONSTANT-2-ALT))
 (1 1 (:REWRITE EQUAL-OF-CONSTANT-WHEN-BVLT-CONSTANT-2))
 (1 1 (:REWRITE EQUAL-OF-CONSTANT-WHEN-BVLT-CONSTANT-1-ALT))
 (1 1 (:REWRITE EQUAL-OF-CONSTANT-WHEN-BVLT-CONSTANT-1))
 (1 1 (:REWRITE EQUAL-CONSTANT-WHEN-NOT-SBVLT))
 (1 1 (:REWRITE EQUAL-CONSTANT-WHEN-BVCHOP-EQUAL-CONSTANT-FALSE))
 )
(GEN-RANDOM-INTEGER-IN-RANGE
 (2 2 (:REWRITE INTEGERP-FROM-UNSIGNED-BYTE-P-SIZE-PARAM))
 (2 2 (:REWRITE DEFAULT-<-2))
 (2 2 (:REWRITE DEFAULT-<-1))
 (2 2 (:REWRITE BOUND-WHEN-USB))
 (2 2 (:REWRITE <-WHEN-BVLT))
 (1 1 (:REWRITE DEFAULT-UNARY-MINUS))
 (1 1 (:REWRITE DEFAULT-+-2))
 (1 1 (:REWRITE DEFAULT-+-1))
 )
(TEST-CASE-TYPEP
 (362 167 (:REWRITE DEFAULT-+-2))
 (227 167 (:REWRITE DEFAULT-+-1))
 (196 28 (:DEFINITION INTEGER-ABS))
 (190 71 (:REWRITE DEFAULT-CDR))
 (127 47 (:REWRITE DEFAULT-CAR))
 (112 28 (:REWRITE COMMUTATIVITY-OF-+))
 (82 52 (:REWRITE DEFAULT-<-2))
 (60 52 (:REWRITE DEFAULT-<-1))
 (56 14 (:DEFINITION LENGTH))
 (52 52 (:REWRITE <-WHEN-BVLT))
 (36 36 (:REWRITE BOUND-WHEN-USB))
 (28 28 (:REWRITE SIZE-NON-NEGATIVE-WHEN-UNSIGNED-BYTE-P-FREE))
 (28 28 (:REWRITE DEFAULT-UNARY-MINUS))
 (18 9 (:REWRITE INTEGERP-OF-CAR-WHEN-ALL-NATP-CHEAP))
 (18 9 (:REWRITE INTEGERP-OF-CAR-WHEN-ALL-INTEGERP-CHEAP))
 (18 9 (:REWRITE CONSP-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (16 16 (:REWRITE CONSP-WHEN-LEN-GREATER))
 (15 15 (:REWRITE LEN-OF-CDDR-WHEN-EQUAL-OF-LEN))
 (14 14 (:REWRITE INTEGERP-FROM-UNSIGNED-BYTE-P-SIZE-PARAM))
 (14 14 (:REWRITE EQUAL-WHEN-BVLT-ALT))
 (14 14 (:REWRITE EQUAL-WHEN-BVLT))
 (14 14 (:REWRITE EQUAL-OF-CONSTANT-WHEN-SBVLT))
 (14 14 (:REWRITE EQUAL-OF-CONSTANT-WHEN-NOT-BVLT-CONSTANT-2))
 (14 14 (:REWRITE EQUAL-OF-CONSTANT-WHEN-NOT-BVLT-CONSTANT-1))
 (14 14 (:REWRITE EQUAL-OF-CONSTANT-WHEN-BVLT-CONSTANT-2-ALT))
 (14 14 (:REWRITE EQUAL-OF-CONSTANT-WHEN-BVLT-CONSTANT-2))
 (14 14 (:REWRITE EQUAL-OF-CONSTANT-WHEN-BVLT-CONSTANT-1-ALT))
 (14 14 (:REWRITE EQUAL-OF-CONSTANT-WHEN-BVLT-CONSTANT-1))
 (14 14 (:REWRITE EQUAL-CONSTANT-WHEN-NOT-SBVLT))
 (14 14 (:REWRITE EQUAL-CONSTANT-WHEN-BVCHOP-EQUAL-CONSTANT-FALSE))
 (14 14 (:REWRITE DEFAULT-REALPART))
 (14 14 (:REWRITE DEFAULT-NUMERATOR))
 (14 14 (:REWRITE DEFAULT-IMAGPART))
 (14 14 (:REWRITE DEFAULT-DENOMINATOR))
 (14 14 (:REWRITE DEFAULT-COERCE-2))
 (14 14 (:REWRITE DEFAULT-COERCE-1))
 (9 9 (:TYPE-PRESCRIPTION SYMBOL-TERM-ALISTP))
 (9 9 (:TYPE-PRESCRIPTION ALL-NATP))
 (9 9 (:TYPE-PRESCRIPTION ALL-INTEGERP))
 )
(TEST-CASE-TYPE-ALISTP)
(GEN-RANDOM-VALUE
 (741 357 (:REWRITE DEFAULT-+-2))
 (508 304 (:REWRITE DEFAULT-CDR))
 (450 357 (:REWRITE DEFAULT-+-1))
 (436 295 (:REWRITE DEFAULT-CAR))
 (322 46 (:DEFINITION INTEGER-ABS))
 (320 186 (:REWRITE DEFAULT-<-2))
 (192 186 (:REWRITE DEFAULT-<-1))
 (187 187 (:REWRITE <-WHEN-BVLT))
 (184 46 (:REWRITE COMMUTATIVITY-OF-+))
 (117 117 (:REWRITE CONSP-WHEN-LEN-GREATER))
 (100 5 (:DEFINITION SYMBOL-LISTP))
 (79 79 (:REWRITE EQUAL-WHEN-BVLT-ALT))
 (79 79 (:REWRITE EQUAL-WHEN-BVLT))
 (79 79 (:REWRITE EQUAL-OF-CONSTANT-WHEN-SBVLT))
 (79 79 (:REWRITE EQUAL-OF-CONSTANT-WHEN-NOT-BVLT-CONSTANT-2))
 (79 79 (:REWRITE EQUAL-OF-CONSTANT-WHEN-NOT-BVLT-CONSTANT-1))
 (79 79 (:REWRITE EQUAL-OF-CONSTANT-WHEN-BVLT-CONSTANT-2-ALT))
 (79 79 (:REWRITE EQUAL-OF-CONSTANT-WHEN-BVLT-CONSTANT-2))
 (79 79 (:REWRITE EQUAL-OF-CONSTANT-WHEN-BVLT-CONSTANT-1-ALT))
 (79 79 (:REWRITE EQUAL-OF-CONSTANT-WHEN-BVLT-CONSTANT-1))
 (79 79 (:REWRITE EQUAL-CONSTANT-WHEN-NOT-SBVLT))
 (79 79 (:REWRITE EQUAL-CONSTANT-WHEN-BVCHOP-EQUAL-CONSTANT-FALSE))
 (71 71 (:REWRITE BOUND-WHEN-USB))
 (53 53 (:REWRITE SIZE-NON-NEGATIVE-WHEN-UNSIGNED-BYTE-P-FREE))
 (52 26 (:REWRITE CONSP-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (46 46 (:REWRITE DEFAULT-UNARY-MINUS))
 (42 21 (:REWRITE INTEGERP-OF-CAR-WHEN-ALL-NATP-CHEAP))
 (42 21 (:REWRITE INTEGERP-OF-CAR-WHEN-ALL-INTEGERP-CHEAP))
 (41 41 (:TYPE-PRESCRIPTION SYMBOL-TERM-ALISTP))
 (41 41 (:REWRITE CONSP-OF-CDR-WHEN-LEN-KNOWN))
 (37 37 (:REWRITE LEN-OF-CDDR-WHEN-EQUAL-OF-LEN))
 (35 35 (:REWRITE INTEGERP-FROM-UNSIGNED-BYTE-P-SIZE-PARAM))
 (30 15 (:REWRITE SYMBOL-ALISTP-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (28 28 (:REWRITE DEFAULT-COERCE-2))
 (28 28 (:REWRITE DEFAULT-COERCE-1))
 (23 23 (:REWRITE DEFAULT-REALPART))
 (23 23 (:REWRITE DEFAULT-NUMERATOR))
 (23 23 (:REWRITE DEFAULT-IMAGPART))
 (23 23 (:REWRITE DEFAULT-DENOMINATOR))
 (21 21 (:TYPE-PRESCRIPTION ALL-NATP))
 (21 21 (:TYPE-PRESCRIPTION ALL-INTEGERP))
 (20 10 (:REWRITE SYMBOLP-OF-CAR-OF-CAR-WHEN-SYMBOL-ALISTP-CHEAP))
 (10 10 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (8 8 (:REWRITE USE-ALL-NATP-2))
 (8 8 (:REWRITE USE-ALL-NATP))
 (8 8 (:REWRITE NATP-WHEN-UNSIGNED-BYTE-P-SIZE-ARG))
 (8 8 (:REWRITE NATP-WHEN-UNSIGNED-BYTE-P))
 (6 6 (:REWRITE EQUAL-OF-0-WHEN-BVLT))
 (6 1 (:LINEAR LEN-OF-CDR-LINEAR-STRONG))
 (5 5 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (3 3 (:REWRITE ZP-OPEN))
 )
(TEST-CASEP)
(TEST-CASEP-OF-CONS-OF-CONS
 (4 2 (:REWRITE SYMBOL-ALISTP-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (2 2 (:TYPE-PRESCRIPTION SYMBOL-TERM-ALISTP))
 (1 1 (:REWRITE DEFAULT-CAR))
 )
(TEST-CASESP)
(TEST-CASESP-OF-CONS
 (22 2 (:REWRITE CONSP-FROM-LEN-CHEAP))
 (10 10 (:TYPE-PRESCRIPTION LEN))
 (4 2 (:REWRITE DEFAULT-<-2))
 (3 3 (:REWRITE DEFAULT-CDR))
 (3 3 (:REWRITE DEFAULT-CAR))
 (2 2 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
 (2 2 (:REWRITE DEFAULT-<-1))
 (2 2 (:REWRITE CONSP-WHEN-LEN-GREATER))
 (2 2 (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT))
 (2 2 (:REWRITE <-WHEN-BVLT))
 (2 2 (:LINEAR LEN-POSITIVE-WHEN-CONSP-LINEAR-CHEAP))
 )
(TEST-CASESP-OF-REVERSE-LIST
 (706 62 (:REWRITE CONSP-FROM-LEN-CHEAP))
 (114 94 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
 (108 62 (:REWRITE DEFAULT-<-2))
 (80 16 (:REWRITE LEN-OF-CDR))
 (70 70 (:REWRITE DEFAULT-CDR))
 (62 62 (:REWRITE DEFAULT-<-1))
 (62 62 (:REWRITE CONSP-WHEN-LEN-GREATER))
 (62 62 (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT))
 (62 62 (:REWRITE <-WHEN-BVLT))
 (50 50 (:REWRITE DEFAULT-CAR))
 (42 21 (:REWRITE SYMBOL-ALISTP-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (21 21 (:TYPE-PRESCRIPTION SYMBOL-TERM-ALISTP))
 (18 17 (:REWRITE DEFAULT-+-2))
 (17 17 (:REWRITE DEFAULT-+-1))
 (16 16 (:REWRITE CONSP-OF-CDR-WHEN-LEN-KNOWN))
 )
(TEST-CASESP-OF-CAR
 (11 1 (:REWRITE CONSP-FROM-LEN-CHEAP))
 (5 5 (:TYPE-PRESCRIPTION LEN))
 (2 1 (:REWRITE DEFAULT-<-2))
 (1 1 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
 (1 1 (:REWRITE DEFAULT-CAR))
 (1 1 (:REWRITE DEFAULT-<-1))
 (1 1 (:REWRITE CONSP-WHEN-LEN-GREATER))
 (1 1 (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT))
 (1 1 (:REWRITE <-WHEN-BVLT))
 (1 1 (:LINEAR LEN-POSITIVE-WHEN-CONSP-LINEAR-CHEAP))
 )
(TEST-CASESP-FORWARD-TO-TRUE-LISTP
 (65 6 (:REWRITE CONSP-FROM-LEN-CHEAP))
 (30 2 (:DEFINITION TRUE-LISTP))
 (18 4 (:REWRITE TEST-CASESP-OF-CAR))
 (12 6 (:REWRITE DEFAULT-<-2))
 (7 7 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
 (7 6 (:LINEAR LEN-POSITIVE-WHEN-CONSP-LINEAR-CHEAP))
 (6 6 (:REWRITE DEFAULT-<-1))
 (6 6 (:REWRITE CONSP-WHEN-LEN-GREATER))
 (6 6 (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT))
 (6 6 (:REWRITE <-WHEN-BVLT))
 (4 4 (:REWRITE DEFAULT-CDR))
 (4 4 (:REWRITE DEFAULT-CAR))
 )
(MAKE-TEST-CASE
 (107 11 (:REWRITE CONSP-FROM-LEN-CHEAP))
 (22 13 (:REWRITE DEFAULT-CAR))
 (20 13 (:LINEAR LEN-POSITIVE-WHEN-CONSP-LINEAR-CHEAP))
 (17 17 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
 (17 9 (:REWRITE DEFAULT-<-2))
 (16 8 (:REWRITE CONSP-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (15 10 (:REWRITE DEFAULT-CDR))
 (12 6 (:REWRITE SYMBOLP-OF-CAR-OF-CAR-WHEN-SYMBOL-ALISTP-CHEAP))
 (11 11 (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT))
 (10 10 (:REWRITE CONSP-WHEN-LEN-GREATER))
 (9 9 (:TYPE-PRESCRIPTION SYMBOL-TERM-ALISTP))
 (9 9 (:REWRITE DEFAULT-<-1))
 (9 9 (:REWRITE <-WHEN-BVLT))
 (5 1 (:REWRITE LEN-OF-CDR))
 (2 1 (:REWRITE SYMBOL-ALISTP-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (1 1 (:REWRITE DEFAULT-+-2))
 (1 1 (:REWRITE DEFAULT-+-1))
 (1 1 (:REWRITE CONSP-OF-CDR-WHEN-LEN-KNOWN))
 )
(TEST-CASEP-OF-MV-NTH-1-OF-MAKE-TEST-CASE
 (252 26 (:REWRITE CONSP-FROM-LEN-CHEAP))
 (83 20 (:REWRITE DEFAULT-CDR))
 (57 30 (:REWRITE DEFAULT-CAR))
 (50 26 (:LINEAR LEN-POSITIVE-WHEN-CONSP-LINEAR-CHEAP))
 (40 40 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
 (32 16 (:REWRITE DEFAULT-<-2))
 (26 26 (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT))
 (22 11 (:REWRITE SYMBOL-ALISTP-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (18 18 (:TYPE-PRESCRIPTION SYMBOL-TERM-ALISTP))
 (16 16 (:REWRITE DEFAULT-<-1))
 (16 16 (:REWRITE CONSP-WHEN-LEN-GREATER))
 (16 16 (:REWRITE <-WHEN-BVLT))
 (16 8 (:REWRITE SYMBOLP-OF-CAR-OF-CAR-WHEN-SYMBOL-ALISTP-CHEAP))
 (14 7 (:REWRITE CONSP-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 )
(TEST-CASE-SATISFIES-ASSUMPTIONSP
 (188 1 (:DEFINITION PSEUDO-TERMP))
 (88 9 (:REWRITE CONSP-FROM-LEN-CHEAP))
 (28 18 (:REWRITE DEFAULT-CAR))
 (27 5 (:REWRITE LEN-OF-CDR))
 (22 16 (:REWRITE DEFAULT-CDR))
 (21 21 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
 (20 1 (:DEFINITION SYMBOL-LISTP))
 (19 2 (:DEFINITION TRUE-LISTP))
 (16 3 (:DEFINITION LENGTH))
 (13 7 (:LINEAR LEN-POSITIVE-WHEN-CONSP-LINEAR-CHEAP))
 (12 12 (:TYPE-PRESCRIPTION BOOLEANP))
 (11 6 (:REWRITE DEFAULT-<-2))
 (9 9 (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT))
 (9 3 (:REWRITE EQUAL-OF-T-WHEN-BOOLEANP-ARG2))
 (9 3 (:REWRITE EQUAL-OF-T-WHEN-BOOLEANP))
 (8 8 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (7 7 (:REWRITE EQUAL-WHEN-BVLT-ALT))
 (7 7 (:REWRITE EQUAL-WHEN-BVLT))
 (7 7 (:REWRITE EQUAL-OF-CONSTANT-WHEN-SBVLT))
 (7 7 (:REWRITE EQUAL-OF-CONSTANT-WHEN-NOT-BVLT-CONSTANT-2))
 (7 7 (:REWRITE EQUAL-OF-CONSTANT-WHEN-NOT-BVLT-CONSTANT-1))
 (7 7 (:REWRITE EQUAL-OF-CONSTANT-WHEN-BVLT-CONSTANT-2-ALT))
 (7 7 (:REWRITE EQUAL-OF-CONSTANT-WHEN-BVLT-CONSTANT-2))
 (7 7 (:REWRITE EQUAL-OF-CONSTANT-WHEN-BVLT-CONSTANT-1-ALT))
 (7 7 (:REWRITE EQUAL-OF-CONSTANT-WHEN-BVLT-CONSTANT-1))
 (7 7 (:REWRITE EQUAL-CONSTANT-WHEN-NOT-SBVLT))
 (7 7 (:REWRITE EQUAL-CONSTANT-WHEN-BVCHOP-EQUAL-CONSTANT-FALSE))
 (6 6 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (6 6 (:REWRITE DEFAULT-<-1))
 (6 6 (:REWRITE CONSP-WHEN-LEN-GREATER))
 (6 6 (:REWRITE <-WHEN-BVLT))
 (6 3 (:REWRITE CONSP-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (5 3 (:REWRITE DEFAULT-+-2))
 (4 4 (:TYPE-PRESCRIPTION SYMBOL-TERM-ALISTP))
 (4 2 (:REWRITE SYMBOLP-OF-CAR-OF-CAR-WHEN-SYMBOL-ALISTP-CHEAP))
 (3 3 (:REWRITE DEFAULT-+-1))
 (2 2 (:REWRITE EQUAL-OF-LEN-AND-0))
 (2 2 (:REWRITE CONSP-OF-CDR-WHEN-LEN-KNOWN))
 (2 1 (:REWRITE SYMBOL-ALISTP-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (1 1 (:TYPE-PRESCRIPTION SYMBOL-LISTP))
 (1 1 (:REWRITE LEN-OF-CDDR-WHEN-EQUAL-OF-LEN))
 (1 1 (:REWRITE DEFAULT-COERCE-2))
 (1 1 (:REWRITE DEFAULT-COERCE-1))
 )
(MAKE-TEST-CASES-AUX
 (44 4 (:REWRITE CONSP-FROM-LEN-CHEAP))
 (20 20 (:TYPE-PRESCRIPTION LEN))
 (10 6 (:REWRITE DEFAULT-<-2))
 (8 8 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (6 6 (:REWRITE DEFAULT-<-1))
 (6 6 (:REWRITE <-WHEN-BVLT))
 (4 4 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (4 4 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
 (4 4 (:REWRITE DEFAULT-CDR))
 (4 4 (:REWRITE DEFAULT-CAR))
 (4 4 (:REWRITE DEFAULT-+-2))
 (4 4 (:REWRITE DEFAULT-+-1))
 (4 4 (:REWRITE CONSP-WHEN-LEN-GREATER))
 (4 4 (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT))
 (4 4 (:LINEAR LEN-POSITIVE-WHEN-CONSP-LINEAR-CHEAP))
 (2 2 (:REWRITE SIZE-NON-NEGATIVE-WHEN-UNSIGNED-BYTE-P-FREE))
 (2 2 (:REWRITE BOUND-WHEN-USB))
 (1 1 (:REWRITE ZP-OPEN))
 (1 1 (:REWRITE INTEGERP-FROM-UNSIGNED-BYTE-P-SIZE-PARAM))
 )
(TEST-CASESP-OF-MV-NTH-1-OF-MAKE-TEST-CASES-AUX
 (20 8 (:REWRITE DEFAULT-+-2))
 (8 8 (:REWRITE ZP-OPEN))
 (8 8 (:REWRITE DEFAULT-+-1))
 (4 4 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (4 4 (:REWRITE ACL2-NUMBERP-WHEN-UNSIGNED-BYTE-P))
 (4 4 (:REWRITE ACL2-NUMBERP-FROM-UNSIGNED-BYTE-P-SIZE-PARAM))
 )
(MAKE-TEST-CASES)
(TEST-CASESP-OF-MV-NTH-1-OF-MAKE-TEST-CASES)
