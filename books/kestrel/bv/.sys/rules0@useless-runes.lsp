(BVPLUS-MINUS-CANCEL
 (473 18 (:REWRITE BVCHOP-IDENTITY))
 (274 8 (:REWRITE USB-PLUS-FROM-BOUNDS))
 (170 170 (:TYPE-PRESCRIPTION IFIX))
 (62 24 (:REWRITE DEFAULT-+-2))
 (56 30 (:REWRITE DEFAULT-<-2))
 (55 17 (:REWRITE UNSIGNED-BYTE-P-FROM-BOUNDS))
 (53 14 (:REWRITE BVCHOP-WITH-N-NEGATIVE))
 (48 24 (:REWRITE DEFAULT-+-1))
 (46 30 (:REWRITE DEFAULT-<-1))
 (38 4 (:LINEAR <=-OF-BVCHOP-SAME-LINEAR))
 (30 30 (:TYPE-PRESCRIPTION UNSIGNED-BYTE-P))
 (26 14 (:REWRITE BVCHOP-WHEN-I-IS-NOT-AN-INTEGER-CHEAP))
 (26 14 (:REWRITE BVCHOP-WHEN-I-IS-NOT-AN-INTEGER))
 (20 4 (:REWRITE UNSIGNED-BYTE-P-OF-0-ARG1))
 (18 18 (:REWRITE BVCHOP-WHEN-TOP-BIT-NOT-1-FAKE-FREE))
 (18 18 (:REWRITE BVCHOP-SUBST-CONSTANT))
 (18 18 (:REWRITE BVCHOP-IDENTITY-CHEAP))
 (18 18 (:REWRITE BOUND-WHEN-USB))
 (17 17 (:REWRITE UNSIGNED-BYTE-P-WHEN-<=-CHEAP))
 (17 17 (:REWRITE UNSIGNED-BYTE-P-TIGHTEN-WHEN-SLICE-IS-0))
 (17 17 (:REWRITE UNSIGNED-BYTE-P-FROM-BOUND))
 (17 17 (:REWRITE UBP-LONGER-BETTER))
 (17 9 (:REWRITE DEFAULT-UNARY-MINUS))
 (14 14 (:TYPE-PRESCRIPTION POSP))
 (14 14 (:REWRITE BVCHOP-WITH-N-NOT-AN-INTEGER))
 (14 14 (:REWRITE BVCHOP-WHEN-SIZE-IS-NOT-NATP))
 (14 14 (:REWRITE BVCHOP-WHEN-NOT-NATP-ARG1-CHEAP))
 (8 8 (:REWRITE UNSIGNED-BYTE-P-OF-+-OF-CONSTANT-STRONG))
 (8 8 (:REWRITE BVCHOP-SUM-SUBST-CONST-ARG2))
 (8 8 (:REWRITE BVCHOP-SUM-SUBST-CONST))
 (8 8 (:REWRITE BVCHOP-CHOP-LEADING-CONSTANT))
 (5 5 (:REWRITE SIZE-NON-NEGATIVE-WHEN-UNSIGNED-BYTE-P-FREE))
 (4 4 (:REWRITE INTEGERP-FROM-UNSIGNED-BYTE-P-SIZE-PARAM))
 (4 4 (:LINEAR EXPT-BOUND-LINEAR))
 (2 2 (:LINEAR EXPT-BOUND-LINEAR-2))
 (1 1 (:REWRITE FOLD-CONSTS-IN-+))
 )
(BVMULT-1-BECOMES-BITAND
 (355 5 (:REWRITE BVAND-WITH-MASK-BETTER))
 (345 5 (:DEFINITION LOGMASKP))
 (223 15 (:REWRITE GETBIT-OF-0-WHEN-BITP))
 (195 13 (:REWRITE BITP-BECOMES-UNSIGNED-BYTE-P))
 (156 26 (:DEFINITION NATP))
 (148 28 (:REWRITE UNSIGNED-BYTE-P-FROM-BOUNDS))
 (130 13 (:LINEAR <=-OF-BVAND-ARG2-LINEAR))
 (130 13 (:LINEAR <=-OF-BVAND-ARG1-LINEAR))
 (106 56 (:REWRITE DEFAULT-<-1))
 (106 15 (:REWRITE GETBIT-IDENTITY))
 (95 55 (:TYPE-PRESCRIPTION <=-OF-0-AND-EXPT))
 (80 80 (:REWRITE INTEGERP-FROM-UNSIGNED-BYTE-P-SIZE-PARAM))
 (70 5 (:DEFINITION EXPT2$INLINE))
 (65 5 (:DEFINITION NFIX))
 (60 10 (:LINEAR INTEGER-LENGTH-BOUND))
 (56 56 (:REWRITE DEFAULT-<-2))
 (55 55 (:TYPE-PRESCRIPTION INTEGERP-OF-EXPT-TYPE))
 (55 55 (:TYPE-PRESCRIPTION INTEGER-LENGTH))
 (55 55 (:TYPE-PRESCRIPTION <-OF-0-AND-EXPT))
 (52 52 (:REWRITE GETBIT-WHEN-SLICE-IS-KNOWN-CONSTANT))
 (41 25 (:REWRITE BVMULT-WHEN-ARG1-IS-NOT-AN-INTEGER))
 (38 25 (:REWRITE BVMULT-WHEN-ARG2-IS-NOT-AN-INTEGER))
 (36 36 (:REWRITE SIZE-NON-NEGATIVE-WHEN-UNSIGNED-BYTE-P-FREE))
 (36 36 (:REWRITE BOUND-WHEN-USB))
 (32 2 (:REWRITE BVCHOP-IDENTITY))
 (30 15 (:REWRITE GETBIT-TOO-HIGH-CHEAP-2))
 (28 28 (:REWRITE UNSIGNED-BYTE-P-WHEN-<=-CHEAP))
 (28 28 (:REWRITE UNSIGNED-BYTE-P-TIGHTEN-WHEN-SLICE-IS-0))
 (28 28 (:REWRITE UNSIGNED-BYTE-P-FROM-BOUND))
 (28 28 (:REWRITE UBP-LONGER-BETTER))
 (28 15 (:REWRITE GETBIT-WHEN-VAL-IS-NOT-AN-INTEGER))
 (26 26 (:REWRITE NATP-WHEN-UNSIGNED-BYTE-P-SIZE-ARG))
 (26 26 (:REWRITE NATP-WHEN-UNSIGNED-BYTE-P))
 (25 25 (:REWRITE BVMULT-WHEN-SIZE-IS-NOT-POSITIVE))
 (25 25 (:REWRITE BVMULT-SUBST2-CONSTANT-VERSION))
 (25 25 (:REWRITE BVMULT-SUBST2-ALT-CONSTANT-VERSION))
 (25 5 (:REWRITE DEFAULT-+-2))
 (25 5 (:REWRITE <-OF-INTEGER-LENGTH-ARG1))
 (20 20 (:LINEAR EXPT-BOUND-LINEAR-WEAK))
 (20 20 (:LINEAR EXPT-BOUND-LINEAR))
 (15 15 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (15 15 (:REWRITE INTEGER-LENGTH-WHEN-NOT-INTEGERP-CHEAP))
 (15 15 (:REWRITE GETBIT-WHEN-NOT-INTEGERP-ARG1))
 (15 15 (:REWRITE GETBIT-WHEN-N-IS-NEGATIVE))
 (15 15 (:REWRITE GETBIT-WHEN-EQUAL-OF-CONSTANT-AND-BVCHOP-CONSTANT-VERSION))
 (15 15 (:REWRITE GETBIT-IDENTITY-FREE))
 (15 15 (:REWRITE EQUAL-CONSTANT-WHEN-BVCHOP-EQUAL-CONSTANT-FALSE))
 (15 15 (:REWRITE ACL2-NUMBERP-WHEN-UNSIGNED-BYTE-P))
 (15 15 (:REWRITE ACL2-NUMBERP-FROM-UNSIGNED-BYTE-P-SIZE-PARAM))
 (15 5 (:DEFINITION POSP))
 (13 13 (:TYPE-PRESCRIPTION BITP))
 (10 10 (:LINEAR EXPT-BOUND-LINEAR-2))
 (10 5 (:REWRITE BVAND-WHEN-Y-IS-NOT-AN-INTEGER))
 (10 5 (:REWRITE BVAND-WHEN-X-IS-NOT-AN-INTEGER))
 (5 5 (:TYPE-PRESCRIPTION POSP))
 (5 5 (:TYPE-PRESCRIPTION LOGMASKP))
 (5 5 (:REWRITE DEFAULT-+-1))
 (5 5 (:REWRITE BVAND-WITH-MASK-BETTER-ERIC-ALT))
 (5 5 (:REWRITE BVAND-WITH-MASK-BETTER-ERIC))
 (5 5 (:REWRITE BVAND-WITH-MASK))
 (5 5 (:REWRITE BVAND-WHEN-SIZE-IS-NOT-POSITIVE))
 (5 5 (:REWRITE BVAND-WHEN-SIZE-IS-NOT-INTEGERP))
 (5 5 (:REWRITE BVAND-OF-CONSTANT-CHOP-ARG3))
 (5 5 (:REWRITE BVAND-OF-CONSTANT-CHOP-ARG2))
 (2 2 (:REWRITE UNSIGNED-BYTE-P-OF-0-ARG1))
 (2 2 (:REWRITE BVCHOP-SUBST-CONSTANT))
 (2 2 (:REWRITE BVCHOP-IDENTITY-CHEAP))
 )
(BVPLUS-1-BECOMES-BITXOR
 (238 14 (:REWRITE GETBIT-OF-0-WHEN-BITP))
 (210 14 (:REWRITE BITP-BECOMES-UNSIGNED-BYTE-P))
 (140 28 (:REWRITE UNSIGNED-BYTE-P-FROM-BOUNDS))
 (112 14 (:REWRITE GETBIT-IDENTITY))
 (56 14 (:REWRITE DEFAULT-<-1))
 (37 37 (:REWRITE GETBIT-WHEN-SLICE-IS-KNOWN-CONSTANT))
 (28 28 (:REWRITE UNSIGNED-BYTE-P-WHEN-<=-CHEAP))
 (28 28 (:REWRITE UNSIGNED-BYTE-P-TIGHTEN-WHEN-SLICE-IS-0))
 (28 28 (:REWRITE UNSIGNED-BYTE-P-FROM-BOUND))
 (28 28 (:REWRITE UBP-LONGER-BETTER))
 (28 14 (:REWRITE GETBIT-WHEN-VAL-IS-NOT-AN-INTEGER))
 (28 14 (:REWRITE GETBIT-TOO-HIGH-CHEAP-2))
 (22 22 (:REWRITE INTEGERP-FROM-UNSIGNED-BYTE-P-SIZE-PARAM))
 (17 17 (:REWRITE EQUAL-CONSTANT-WHEN-BVCHOP-EQUAL-CONSTANT-FALSE))
 (17 12 (:REWRITE BVPLUS-TRIM-LEADING-CONSTANT))
 (14 14 (:TYPE-PRESCRIPTION INTEGERP-OF-EXPT-TYPE))
 (14 14 (:TYPE-PRESCRIPTION BITP))
 (14 14 (:TYPE-PRESCRIPTION <=-OF-0-AND-EXPT))
 (14 14 (:TYPE-PRESCRIPTION <-OF-0-AND-EXPT))
 (14 14 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (14 14 (:REWRITE GETBIT-WHEN-NOT-INTEGERP-ARG1))
 (14 14 (:REWRITE GETBIT-WHEN-N-IS-NEGATIVE))
 (14 14 (:REWRITE GETBIT-WHEN-EQUAL-OF-CONSTANT-AND-BVCHOP-CONSTANT-VERSION))
 (14 14 (:REWRITE GETBIT-IDENTITY-FREE))
 (14 14 (:REWRITE DEFAULT-<-2))
 (14 14 (:REWRITE ACL2-NUMBERP-WHEN-UNSIGNED-BYTE-P))
 (14 14 (:REWRITE ACL2-NUMBERP-FROM-UNSIGNED-BYTE-P-SIZE-PARAM))
 (12 12 (:REWRITE BVPLUS-WHEN-EQUAL-OF-CONSTANT-AND-BVCHOP-ARG3))
 (12 12 (:REWRITE BVPLUS-WHEN-EQUAL-OF-CONSTANT-AND-BVCHOP-ARG2))
 (4 2 (:REWRITE BVPLUS-WHEN-ARG2-IS-NOT-AN-INTEGER))
 (4 2 (:REWRITE BVPLUS-WHEN-ARG1-IS-NOT-AN-INTEGER))
 (4 2 (:REWRITE BITXOR-WHEN-Y-IS-NOT-AN-INTEGER))
 (4 2 (:REWRITE BITXOR-WHEN-X-IS-NOT-AN-INTEGER))
 (2 2 (:REWRITE EQUAL-OF-CONSTANT-AND-BITXOR-OF-CONSTANT))
 (2 2 (:REWRITE BVPLUS-WHEN-SIZE-IS-NOT-POSITIVE))
 (2 2 (:REWRITE BVPLUS-WHEN-NOT-NATP-ARG1-CHEAP))
 (2 2 (:REWRITE BVPLUS-SUBST-VALUE-ALT))
 (2 2 (:REWRITE BVPLUS-SUBST-VALUE))
 (2 2 (:REWRITE BITXOR-OF-CONSTANT-CHOP-ARG2))
 (2 2 (:REWRITE BITXOR-OF-CONSTANT-CHOP-ARG1))
 )
(BVMULT-OF-2
 (173 8 (:REWRITE BVCHOP-IDENTITY))
 (95 1 (:REWRITE UNSIGNED-BYTE-P-OF-IF))
 (92 9 (:REWRITE UNSIGNED-BYTE-P-FROM-BOUND))
 (26 11 (:REWRITE DEFAULT-<-1))
 (24 3 (:LINEAR <=-OF-BVCHOP-SAME-LINEAR))
 (23 14 (:REWRITE DEFAULT-+-2))
 (20 14 (:REWRITE DEFAULT-+-1))
 (19 9 (:REWRITE UNSIGNED-BYTE-P-FROM-BOUNDS))
 (16 16 (:TYPE-PRESCRIPTION UNSIGNED-BYTE-P))
 (14 6 (:REWRITE DEFAULT-*-2))
 (11 11 (:REWRITE DEFAULT-<-2))
 (10 10 (:REWRITE BOUND-WHEN-USB))
 (9 9 (:REWRITE UNSIGNED-BYTE-P-WHEN-<=-CHEAP))
 (9 9 (:REWRITE UBP-LONGER-BETTER))
 (9 1 (:REWRITE UNSIGNED-BYTE-P-OF-TIMES-2))
 (8 8 (:REWRITE UNSIGNED-BYTE-P-TIGHTEN-WHEN-SLICE-IS-0))
 (8 8 (:REWRITE BVCHOP-WHEN-TOP-BIT-NOT-1-FAKE-FREE))
 (8 8 (:REWRITE BVCHOP-SUBST-CONSTANT))
 (8 8 (:REWRITE BVCHOP-IDENTITY-CHEAP))
 (7 7 (:TYPE-PRESCRIPTION NATP-OF-EXPT))
 (7 6 (:REWRITE DEFAULT-*-1))
 (6 6 (:TYPE-PRESCRIPTION POSP))
 (6 6 (:REWRITE SIZE-NON-NEGATIVE-WHEN-UNSIGNED-BYTE-P-FREE))
 (6 6 (:LINEAR <=-OF-BVCHOP-SAME-LINEAR-2))
 (5 5 (:REWRITE INTEGERP-FROM-UNSIGNED-BYTE-P-SIZE-PARAM))
 (5 2 (:REWRITE BVCHOP-WITH-N-NEGATIVE))
 (4 4 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (4 4 (:REWRITE ACL2-NUMBERP-WHEN-UNSIGNED-BYTE-P))
 (4 4 (:REWRITE ACL2-NUMBERP-FROM-UNSIGNED-BYTE-P-SIZE-PARAM))
 (3 3 (:TYPE-PRESCRIPTION NATP))
 (3 2 (:REWRITE BVCHOP-WHEN-SIZE-IS-NOT-NATP))
 (3 2 (:REWRITE BVCHOP-WHEN-NOT-NATP-ARG1-CHEAP))
 (3 2 (:REWRITE BVCHOP-WHEN-I-IS-NOT-AN-INTEGER))
 (2 2 (:REWRITE BVCHOP-WITH-N-NOT-AN-INTEGER))
 (1 1 (:REWRITE UNSIGNED-BYTE-P-OF-0-ARG2))
 (1 1 (:REWRITE UNSIGNED-BYTE-P-OF-*-GEN))
 (1 1 (:REWRITE NATP-WHEN-UNSIGNED-BYTE-P-SIZE-ARG))
 (1 1 (:REWRITE NATP-WHEN-UNSIGNED-BYTE-P))
 (1 1 (:REWRITE EQUAL-CONSTANT-WHEN-BVCHOP-EQUAL-CONSTANT-FALSE))
 (1 1 (:REWRITE <-OF-EXPT-2-AND-CONSTANT))
 )
