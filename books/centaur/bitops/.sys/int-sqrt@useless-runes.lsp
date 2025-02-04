(BITOPS::INT-SQRT/REM
 (81 5 (:REWRITE NFIX-WHEN-NOT-NATP))
 (36 21 (:REWRITE DEFAULT-<-2))
 (30 8 (:REWRITE ZP-WHEN-GT-0))
 (25 5 (:REWRITE POSP-RW))
 (23 21 (:REWRITE DEFAULT-<-1))
 (21 5 (:REWRITE NATP-POSP))
 (15 8 (:REWRITE DEFAULT-+-2))
 (14 5 (:REWRITE BITOPS::LOGCDR-OF-BIT))
 (9 8 (:REWRITE DEFAULT-+-1))
 (8 8 (:TYPE-PRESCRIPTION NATP))
 (7 1 (:REWRITE LOGTAIL-IDENTITY))
 (6 6 (:TYPE-PRESCRIPTION BITP))
 (4 2 (:REWRITE NATP-WHEN-GTE-0))
 (4 1 (:DEFINITION UNSIGNED-BYTE-P))
 (3 3 (:REWRITE ZP-OPEN))
 (3 1 (:DEFINITION INTEGER-RANGE-P))
 (2 2 (:REWRITE NATP-WHEN-INTEGERP))
 (2 2 (:REWRITE NATP-RW))
 (1 1 (:REWRITE-QUOTED-CONSTANT NFIX-UNDER-NAT-EQUIV))
 (1 1 (:REWRITE-QUOTED-CONSTANT IFIX-UNDER-INT-EQUIV))
 (1 1 (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR))
 (1 1 (:REWRITE NFIX-EQUAL-TO-NONZERO-CONST))
 (1 1 (:REWRITE NFIX-EQUAL-TO-NONZERO))
 )
(BITOPS::NATP-OF-INT-SQRT/REM.SQRT
 (70 10 (:REWRITE LOGHEAD-IDENTITY))
 (61 51 (:REWRITE DEFAULT-<-2))
 (56 14 (:DEFINITION UNSIGNED-BYTE-P))
 (51 51 (:REWRITE DEFAULT-<-1))
 (48 16 (:REWRITE NATP-WHEN-GTE-0))
 (42 14 (:DEFINITION INTEGER-RANGE-P))
 (36 23 (:REWRITE DEFAULT-+-1))
 (33 23 (:REWRITE DEFAULT-+-2))
 (33 23 (:REWRITE DEFAULT-*-2))
 (33 11 (:REWRITE ZP-WHEN-GT-0))
 (30 6 (:REWRITE LOGTAIL-IDENTITY))
 (23 23 (:REWRITE DEFAULT-*-1))
 (16 16 (:REWRITE-QUOTED-CONSTANT NFIX-UNDER-NAT-EQUIV))
 (16 16 (:REWRITE-QUOTED-CONSTANT IFIX-UNDER-INT-EQUIV))
 (16 16 (:REWRITE NATP-WHEN-INTEGERP))
 (16 16 (:REWRITE NATP-RW))
 (14 14 (:TYPE-PRESCRIPTION UNSIGNED-BYTE-P))
 (14 14 (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR))
 (11 11 (:REWRITE ZP-WHEN-INTEGERP))
 (11 11 (:REWRITE ZP-OPEN))
 (10 10 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (4 4 (:REWRITE FOLD-CONSTS-IN-+))
 (3 3 (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
 (2 2 (:REWRITE DEFAULT-UNARY-MINUS))
 (1 1 (:TYPE-PRESCRIPTION |x < y  =>  0 < y-x|))
 )
(BITOPS::LOGHEAD-PLUS-LOGTAIL
 (2513 7 (:REWRITE LOGTAIL-IDENTITY))
 (1470 14 (:DEFINITION UNSIGNED-BYTE-P))
 (1384 14 (:DEFINITION INTEGER-RANGE-P))
 (1313 565 (:TYPE-PRESCRIPTION BITOPS::LOGCDR-NATP))
 (1082 42 (:REWRITE UNSIGNED-BYTE-P-PLUS))
 (980 21 (:DEFINITION UNSIGNED-BYTE-P**))
 (400 5 (:REWRITE ASH-0))
 (327 31 (:REWRITE BITOPS::LOGCDR-<-CONST))
 (307 22 (:REWRITE BITOPS::LOGCDR-OF-BIT))
 (298 7 (:REWRITE ZIP-OPEN))
 (246 3 (:REWRITE <-*-/-RIGHT-COMMUTED))
 (200 200 (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
 (141 63 (:REWRITE DEFAULT-<-1))
 (109 63 (:REWRITE DEFAULT-<-2))
 (107 39 (:REWRITE IFIX-WHEN-NOT-INTEGERP))
 (102 102 (:LINEAR BITOPS::LOGCDR-<=-LOGCDR))
 (87 29 (:REWRITE <-0-+-NEGATIVE-1))
 (84 14 (:REWRITE IFIX-NEGATIVE-TO-NEGP))
 (83 67 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP))
 (82 42 (:REWRITE DEFAULT-+-2))
 (72 8 (:LINEAR EXPT->-1))
 (67 67 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-POSITIVE))
 (67 67 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONZERO))
 (66 12 (:REWRITE ZP-WHEN-GT-0))
 (62 12 (:REWRITE ZP-WHEN-INTEGERP))
 (56 56 (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR))
 (46 46 (:TYPE-PRESCRIPTION BITP))
 (45 9 (:REWRITE DEFAULT-*-2))
 (44 42 (:REWRITE DEFAULT-+-1))
 (42 14 (:REWRITE NEGP-WHEN-LESS-THAN-0))
 (40 36 (:REWRITE EXPT-WITH-VIOLATED-GUARDS))
 (36 12 (:REWRITE FOLD-CONSTS-IN-+))
 (36 9 (:REWRITE DEFAULT-*-1))
 (36 3 (:REWRITE COMMUTATIVITY-OF-*))
 (28 7 (:REWRITE EXPONENTS-ADD))
 (24 24 (:REWRITE-QUOTED-CONSTANT NFIX-UNDER-NAT-EQUIV))
 (24 24 (:REWRITE-QUOTED-CONSTANT IFIX-UNDER-INT-EQUIV))
 (24 24 (:REWRITE-QUOTED-CONSTANT BFIX-UNDER-BIT-EQUIV))
 (16 16 (:LINEAR EXPT-IS-INCREASING-FOR-BASE>1))
 (14 14 (:TYPE-PRESCRIPTION NEGP))
 (14 14 (:REWRITE NEGP-WHEN-INTEGERP))
 (11 1 (:REWRITE BFIX-WHEN-NOT-1))
 (6 3 (:REWRITE POSP-NATP))
 (6 2 (:REWRITE BITOPS::LOGCAR-OF-BIT))
 (6 2 (:REWRITE <-+-NEGATIVE-0-1))
 (5 5 (:TYPE-PRESCRIPTION ZIP))
 (5 1 (:LINEAR BITOPS::LOGCAR-BOUND))
 (4 4 (:REWRITE EXPONENTS-ADD-FOR-NONNEG-EXPONENTS))
 (3 3 (:REWRITE EQUAL-CONSTANT-+))
 (3 2 (:REWRITE NFIX-WHEN-NOT-NATP))
 (2 2 (:TYPE-PRESCRIPTION BIT->BOOL$INLINE))
 (2 2 (:REWRITE ZP-OPEN))
 (2 1 (:REWRITE BFIX-WHEN-NOT-BITP))
 (2 1 (:REWRITE BFIX-WHEN-NOT-BIT->BOOL))
 (2 1 (:REWRITE BFIX-WHEN-BIT->BOOL))
 )
(BITOPS::INT-SQRT/REM-INVARIANT
 (846 347 (:REWRITE DEFAULT-+-2))
 (494 347 (:REWRITE DEFAULT-+-1))
 (467 56 (:REWRITE LOGHEAD-IDENTITY))
 (464 110 (:REWRITE LOGTAIL-IDENTITY))
 (460 115 (:DEFINITION UNSIGNED-BYTE-P))
 (424 215 (:REWRITE DEFAULT-*-2))
 (345 115 (:DEFINITION INTEGER-RANGE-P))
 (336 239 (:REWRITE DEFAULT-<-2))
 (288 239 (:REWRITE DEFAULT-<-1))
 (239 215 (:REWRITE DEFAULT-*-1))
 (227 34 (:REWRITE ZP-WHEN-GT-0))
 (200 25 (:REWRITE UNSIGNED-BYTE-P-OF-LOGTAIL))
 (200 25 (:REWRITE BITOPS::LOGTAIL-OF-LOGTAIL))
 (188 82 (:REWRITE DEFAULT-UNARY-MINUS))
 (155 155 (:REWRITE-QUOTED-CONSTANT IFIX-UNDER-INT-EQUIV))
 (153 153 (:REWRITE-QUOTED-CONSTANT NFIX-UNDER-NAT-EQUIV))
 (123 123 (:REWRITE FOLD-CONSTS-IN-+))
 (115 115 (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR))
 (110 8 (:LINEAR X*Y>1-POSITIVE))
 (54 54 (:TYPE-PRESCRIPTION NATP))
 (31 29 (:REWRITE IFIX-WHEN-NOT-INTEGERP))
 (27 27 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (20 20 (:REWRITE EQUAL-CONSTANT-+))
 (7 7 (:REWRITE ZP-OPEN))
 (6 4 (:REWRITE NFIX-WHEN-NOT-NATP))
 )
(BITOPS::INT-SQRT/REM-SQRT-BOUNDS
 (39 12 (:REWRITE DEFAULT-+-2))
 (24 3 (:REWRITE NFIX-WHEN-NATP))
 (22 12 (:REWRITE DEFAULT-*-2))
 (20 12 (:REWRITE DEFAULT-*-1))
 (19 12 (:REWRITE DEFAULT-+-1))
 (18 3 (:REWRITE NFIX-WHEN-NOT-NATP))
 (13 7 (:REWRITE DEFAULT-<-2))
 (12 12 (:TYPE-PRESCRIPTION NATP))
 (12 6 (:REWRITE NATP-WHEN-GTE-0))
 (10 7 (:REWRITE DEFAULT-<-1))
 (6 6 (:REWRITE NATP-WHEN-INTEGERP))
 (6 6 (:REWRITE NATP-RW))
 (5 5 (:REWRITE FOLD-CONSTS-IN-+))
 (3 1 (:REWRITE DEFAULT-UNARY-MINUS))
 (2 2 (:REWRITE INEQUALITY-WITH-NFIX-HYP-2))
 (1 1 (:REWRITE EQUAL-CONSTANT-+))
 )
(BITOPS::INT-SQRT/REM-REM-NATP)
(BITOPS::INTEGER-LENGTH-OF-LOGCONS
 (8 8 (:TYPE-PRESCRIPTION NATP))
 (8 4 (:TYPE-PRESCRIPTION BITOPS::LOGCONS-POSP-2))
 (8 4 (:TYPE-PRESCRIPTION BITOPS::LOGCONS-POSP-1))
 (8 4 (:TYPE-PRESCRIPTION BITOPS::LOGCONS-NEGP))
 (8 4 (:TYPE-PRESCRIPTION BITOPS::LOGCONS-NATP))
 (6 6 (:TYPE-PRESCRIPTION BITP))
 (4 4 (:TYPE-PRESCRIPTION POSP))
 (4 4 (:TYPE-PRESCRIPTION NEGP))
 (4 4 (:TYPE-PRESCRIPTION BIT->BOOL$INLINE))
 (4 2 (:REWRITE DEFAULT-+-2))
 (4 2 (:REWRITE BFIX-WHEN-NOT-BITP))
 (4 2 (:REWRITE BFIX-WHEN-NOT-BIT->BOOL))
 (4 2 (:REWRITE BFIX-WHEN-BITP))
 (4 2 (:REWRITE BFIX-WHEN-BIT->BOOL))
 (4 2 (:REWRITE BFIX-BITP))
 (3 3 (:REWRITE IFIX-WHEN-NOT-INTEGERP))
 (2 2 (:REWRITE DEFAULT-+-1))
 (2 2 (:REWRITE BFIX-WHEN-NOT-1))
 )
(BITOPS::INTEGER-LENGTH-OF-*2
 (5 3 (:REWRITE DEFAULT-+-2))
 (3 3 (:REWRITE DEFAULT-+-1))
 (2 2 (:REWRITE IFIX-WHEN-NOT-INTEGERP))
 (2 2 (:REWRITE DEFAULT-*-2))
 (2 2 (:REWRITE DEFAULT-*-1))
 (1 1 (:REWRITE EQUAL-CONSTANT-+))
 )
(BITOPS::LOGHEAD-EQUAL-0-WHEN-LOGTAIL-EQUAL-0
 (1894 35 (:DEFINITION UNSIGNED-BYTE-P))
 (1713 30 (:DEFINITION INTEGER-RANGE-P))
 (1238 70 (:REWRITE UNSIGNED-BYTE-P-PLUS))
 (855 465 (:TYPE-PRESCRIPTION BITOPS::LOGCDR-NATP))
 (393 51 (:REWRITE BITOPS::LOGCDR-<-CONST))
 (294 41 (:REWRITE BITOPS::LOGCDR-OF-BIT))
 (250 145 (:REWRITE DEFAULT-<-2))
 (195 145 (:REWRITE DEFAULT-<-1))
 (186 186 (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
 (158 158 (:LINEAR BITOPS::LOGCDR-<=-LOGCDR))
 (135 34 (:REWRITE ZP-WHEN-GT-0))
 (113 34 (:REWRITE ZP-WHEN-INTEGERP))
 (108 3 (:REWRITE <-*-/-RIGHT-COMMUTED))
 (106 106 (:TYPE-PRESCRIPTION BITP))
 (104 104 (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR))
 (103 92 (:REWRITE EXPT-WITH-VIOLATED-GUARDS))
 (99 33 (:REWRITE <-0-+-NEGATIVE-1))
 (62 51 (:REWRITE DEFAULT-+-2))
 (60 10 (:REWRITE IFIX-NEGATIVE-TO-NEGP))
 (53 35 (:REWRITE IFIX-WHEN-NOT-INTEGERP))
 (51 51 (:REWRITE DEFAULT-+-1))
 (50 50 (:LINEAR EXPT-IS-INCREASING-FOR-BASE>1))
 (36 12 (:REWRITE BITOPS::LOGCAR-OF-BIT))
 (35 14 (:REWRITE EXPONENTS-ADD))
 (33 11 (:REWRITE FOLD-CONSTS-IN-+))
 (30 30 (:REWRITE-QUOTED-CONSTANT NFIX-UNDER-NAT-EQUIV))
 (30 30 (:REWRITE-QUOTED-CONSTANT IFIX-UNDER-INT-EQUIV))
 (30 30 (:REWRITE-QUOTED-CONSTANT BFIX-UNDER-BIT-EQUIV))
 (30 10 (:REWRITE NEGP-WHEN-LESS-THAN-0))
 (24 9 (:REWRITE DEFAULT-*-2))
 (24 8 (:REWRITE NATP-WHEN-GTE-0))
 (15 15 (:REWRITE ZP-OPEN))
 (15 9 (:REWRITE DEFAULT-*-1))
 (15 3 (:REWRITE COMMUTATIVITY-OF-*))
 (11 11 (:REWRITE EXPONENTS-ADD-FOR-NONNEG-EXPONENTS))
 (10 10 (:TYPE-PRESCRIPTION NEGP))
 (10 10 (:REWRITE NEGP-WHEN-INTEGERP))
 (10 5 (:TYPE-PRESCRIPTION BITOPS::LOGCONS-POSP-2))
 (8 8 (:REWRITE NATP-WHEN-INTEGERP))
 (8 8 (:REWRITE NATP-RW))
 (5 5 (:TYPE-PRESCRIPTION BIT->BOOL$INLINE))
 (5 5 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (2 2 (:TYPE-PRESCRIPTION POSP))
 )
(BITOPS::INT-SQRT/REM-POSP
 (65 30 (:REWRITE DEFAULT-+-2))
 (63 39 (:REWRITE DEFAULT-<-2))
 (63 9 (:REWRITE LOGHEAD-IDENTITY))
 (55 7 (:REWRITE ZP-WHEN-GT-0))
 (54 5 (:REWRITE POSP-RW))
 (48 12 (:DEFINITION UNSIGNED-BYTE-P))
 (46 30 (:REWRITE DEFAULT-+-1))
 (43 39 (:REWRITE DEFAULT-<-1))
 (41 5 (:REWRITE NATP-POSP))
 (36 12 (:DEFINITION INTEGER-RANGE-P))
 (31 18 (:REWRITE DEFAULT-*-2))
 (21 3 (:REWRITE LOGTAIL-IDENTITY))
 (18 18 (:REWRITE DEFAULT-*-1))
 (12 12 (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR))
 (12 6 (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
 (10 10 (:REWRITE-QUOTED-CONSTANT NFIX-UNDER-NAT-EQUIV))
 (10 10 (:REWRITE-QUOTED-CONSTANT IFIX-UNDER-INT-EQUIV))
 (8 8 (:REWRITE FOLD-CONSTS-IN-+))
 (7 1 (:REWRITE ZERO-IS-ONLY-ZERO-DIVISOR))
 (6 6 (:TYPE-PRESCRIPTION NATP))
 (6 4 (:REWRITE DEFAULT-UNARY-MINUS))
 (3 2 (:TYPE-PRESCRIPTION |x < y  =>  0 < y-x|))
 (2 2 (:REWRITE ZP-OPEN))
 (2 1 (:DEFINITION FIX))
 )
(BITOPS::INT-SQRT/REM-EQUAL-0
 (84 33 (:REWRITE DEFAULT-+-2))
 (84 6 (:REWRITE COMMUTATIVITY-2-OF-+))
 (66 6 (:REWRITE COMMUTATIVITY-OF-+))
 (48 33 (:REWRITE DEFAULT-+-1))
 (30 30 (:TYPE-PRESCRIPTION BITOPS::INT-SQRT/REM-REM-NATP))
 (30 15 (:REWRITE DEFAULT-*-2))
 (28 6 (:DEFINITION UNSIGNED-BYTE-P))
 (24 24 (:TYPE-PRESCRIPTION LOGHEAD-TYPE))
 (23 3 (:REWRITE LOGTAIL-IDENTITY))
 (23 3 (:REWRITE LOGHEAD-IDENTITY))
 (22 16 (:REWRITE DEFAULT-<-2))
 (22 6 (:DEFINITION INTEGER-RANGE-P))
 (21 9 (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
 (19 16 (:REWRITE DEFAULT-<-1))
 (18 3 (:REWRITE DISTRIBUTIVITY-OF-MINUS-OVER-+))
 (16 6 (:REWRITE ZP-WHEN-GT-0))
 (15 15 (:REWRITE DEFAULT-*-1))
 (12 12 (:REWRITE FOLD-CONSTS-IN-+))
 (12 6 (:REWRITE DEFAULT-UNARY-MINUS))
 (6 6 (:TYPE-PRESCRIPTION UNSIGNED-BYTE-P))
 (6 6 (:REWRITE-QUOTED-CONSTANT NFIX-UNDER-NAT-EQUIV))
 (6 6 (:REWRITE-QUOTED-CONSTANT IFIX-UNDER-INT-EQUIV))
 (6 6 (:REWRITE ZP-WHEN-INTEGERP))
 (6 6 (:REWRITE ZP-OPEN))
 (6 6 (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR))
 (6 3 (:TYPE-PRESCRIPTION |x < y  =>  0 < y-x|))
 )
(BITOPS::INTEGER-LENGTH-OF-INT-SQRT/REM
 (757 72 (:DEFINITION UNSIGNED-BYTE-P))
 (685 72 (:DEFINITION INTEGER-RANGE-P))
 (619 50 (:REWRITE LOGTAIL-IDENTITY))
 (420 171 (:REWRITE DEFAULT-+-2))
 (362 30 (:REWRITE LOGHEAD-IDENTITY))
 (360 49 (:REWRITE BITOPS::LOGCDR-<-CONST))
 (251 171 (:REWRITE DEFAULT-+-1))
 (157 118 (:REWRITE DEFAULT-<-2))
 (138 138 (:LINEAR BITOPS::LOGCDR-<=-LOGCDR))
 (135 118 (:REWRITE DEFAULT-<-1))
 (130 65 (:REWRITE DEFAULT-*-2))
 (120 120 (:TYPE-PRESCRIPTION BITP))
 (120 120 (:REWRITE-QUOTED-CONSTANT NFIX-UNDER-NAT-EQUIV))
 (120 120 (:REWRITE-QUOTED-CONSTANT IFIX-UNDER-INT-EQUIV))
 (101 83 (:REWRITE IFIX-WHEN-NOT-INTEGERP))
 (73 32 (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
 (72 72 (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR))
 (69 69 (:REWRITE-QUOTED-CONSTANT BFIX-UNDER-BIT-EQUIV))
 (65 65 (:REWRITE DEFAULT-*-1))
 (56 4 (:REWRITE BFIX-WHEN-NOT-1))
 (44 22 (:REWRITE DEFAULT-UNARY-MINUS))
 (32 4 (:LINEAR BITOPS::LOGCAR-BOUND))
 (22 11 (:TYPE-PRESCRIPTION |x < y  =>  0 < y-x|))
 (12 1 (:REWRITE *-PRESERVES->=-FOR-NONNEGATIVES))
 (10 6 (:REWRITE NFIX-WHEN-NOT-NATP))
 (8 8 (:TYPE-PRESCRIPTION BIT->BOOL$INLINE))
 (8 4 (:REWRITE BFIX-WHEN-NOT-BITP))
 (8 4 (:REWRITE BFIX-WHEN-NOT-BIT->BOOL))
 (8 4 (:REWRITE BFIX-WHEN-BIT->BOOL))
 (7 7 (:REWRITE ZP-OPEN))
 (6 6 (:REWRITE EQUAL-CONSTANT-+))
 (1 1 (:REWRITE X*Y>1-POSITIVE-LEMMA))
 (1 1 (:REWRITE *-PRESERVES->-FOR-NONNEGATIVES-1))
 )
(BITOPS::INT-SQRT/REM
 (2 2 (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
 )
(BITOPS::INT-SQRT)
(BITOPS::NATP-OF-INT-SQRT)
(BITOPS::INT-SQRT-BOUNDS)
(BITOPS::INT-SQRT-POSP)
(BITOPS::INT-SQRT-EQUAL-0)
(BITOPS::INTEGER-LENGTH-OF-INT-SQRT)
(BITOPS::INT-SQRT/REM-REDEF
 (16 2 (:LINEAR X*Y>1-POSITIVE))
 (9 2 (:REWRITE NFIX-WHEN-NATP))
 (7 2 (:REWRITE NFIX-WHEN-NOT-NATP))
 (6 2 (:REWRITE DEFAULT-UNARY-MINUS))
 (6 2 (:REWRITE DEFAULT-+-2))
 (5 3 (:REWRITE DEFAULT-<-2))
 (4 4 (:TYPE-PRESCRIPTION NATP))
 (4 2 (:REWRITE NATP-WHEN-GTE-0))
 (4 2 (:REWRITE DEFAULT-+-1))
 (4 2 (:REWRITE DEFAULT-*-2))
 (4 2 (:REWRITE DEFAULT-*-1))
 (3 3 (:REWRITE DEFAULT-<-1))
 (2 2 (:REWRITE NATP-WHEN-INTEGERP))
 (2 2 (:REWRITE NATP-RW))
 )
(BITOPS::INT-SQRT-CEILING)
(BITOPS::NATP-OF-INT-SQRT-CEILING
 (72 1 (:REWRITE NFIX-EQUAL-TO-NONZERO))
 (48 2 (:REWRITE 0-<-*))
 (39 5 (:REWRITE ZP-WHEN-GT-0))
 (33 5 (:REWRITE ZP-WHEN-INTEGERP))
 (12 4 (:REWRITE BITOPS::INT-SQRT-EQUAL-0))
 (12 3 (:DEFINITION NOT))
 (10 6 (:REWRITE DEFAULT-<-2))
 (9 5 (:REWRITE DEFAULT-+-2))
 (8 5 (:REWRITE DEFAULT-+-1))
 (8 2 (:DEFINITION IFF))
 (8 1 (:REWRITE NFIX-WHEN-NATP))
 (6 6 (:REWRITE DEFAULT-<-1))
 (6 1 (:REWRITE NFIX-WHEN-NOT-NATP))
 (4 4 (:TYPE-PRESCRIPTION ZP))
 (4 4 (:REWRITE ZP-OPEN))
 (4 2 (:REWRITE NATP-WHEN-GTE-0))
 (3 1 (:REWRITE DEFAULT-UNARY-MINUS))
 (2 2 (:REWRITE NATP-WHEN-INTEGERP))
 (2 2 (:REWRITE NATP-RW))
 (2 1 (:REWRITE DEFAULT-*-2))
 (2 1 (:REWRITE DEFAULT-*-1))
 (2 1 (:LINEAR X*Y>1-POSITIVE))
 (1 1 (:REWRITE NFIX-EQUAL-TO-NONZERO-CONST))
 (1 1 (:REWRITE EQUAL-CONSTANT-+))
 )
(BITOPS::INT-SQRT-CEILING-BOUNDS
 (153 59 (:REWRITE DEFAULT-+-2))
 (134 7 (:REWRITE 0-<-*))
 (102 16 (:REWRITE ZP-WHEN-GT-0))
 (101 55 (:REWRITE DEFAULT-<-2))
 (99 24 (:REWRITE NFIX-WHEN-NOT-NATP))
 (94 53 (:REWRITE DEFAULT-*-2))
 (88 53 (:REWRITE DEFAULT-*-1))
 (87 59 (:REWRITE DEFAULT-+-1))
 (79 16 (:REWRITE ZP-WHEN-INTEGERP))
 (76 55 (:REWRITE DEFAULT-<-1))
 (63 31 (:REWRITE NATP-WHEN-GTE-0))
 (62 62 (:TYPE-PRESCRIPTION NATP))
 (43 8 (:REWRITE INEQUALITY-WITH-NFIX-HYP-2))
 (34 5 (:LINEAR X*Y>1-POSITIVE))
 (31 31 (:REWRITE NATP-WHEN-INTEGERP))
 (31 31 (:REWRITE NATP-RW))
 (22 10 (:REWRITE DEFAULT-UNARY-MINUS))
 (13 13 (:REWRITE ZP-OPEN))
 (8 1 (:REWRITE NATP-POSP))
 (3 3 (:REWRITE NFIX-EQUAL-TO-NONZERO-CONST))
 (3 3 (:REWRITE INEQUALITY-WITH-NFIX-HYP-1))
 (1 1 (:REWRITE POSP-RW))
 (1 1 (:REWRITE EQUAL-CONSTANT-+))
 )
(BITOPS::UPPER-BOUND-BY-INT-SQRT
 (63 11 (:LINEAR X*Y>1-POSITIVE))
 (60 17 (:REWRITE DEFAULT-+-2))
 (50 23 (:REWRITE DEFAULT-<-2))
 (29 17 (:REWRITE DEFAULT-*-2))
 (28 17 (:REWRITE DEFAULT-*-1))
 (27 17 (:REWRITE DEFAULT-+-1))
 (26 23 (:REWRITE DEFAULT-<-1))
 (9 9 (:REWRITE FOLD-CONSTS-IN-+))
 (2 2 (:REWRITE NFIX-WHEN-NOT-NATP))
 (1 1 (:REWRITE NATP-RW))
 )
(BITOPS::LOWER-BOUND-BY-INT-SQRT
 (91 49 (:REWRITE DEFAULT-+-2))
 (51 35 (:REWRITE DEFAULT-<-2))
 (49 49 (:REWRITE DEFAULT-+-1))
 (37 37 (:REWRITE DEFAULT-*-2))
 (37 37 (:REWRITE DEFAULT-*-1))
 (35 35 (:REWRITE DEFAULT-<-1))
 (27 27 (:REWRITE FOLD-CONSTS-IN-+))
 (6 6 (:REWRITE NATP-RW))
 (5 5 (:REWRITE NATP-WHEN-INTEGERP))
 (2 2 (:REWRITE NFIX-WHEN-NOT-NATP))
 )
(BITOPS::LOWER-BOUND-BY-NEGATIVE-INT-SQRT
 (60 17 (:REWRITE DEFAULT-+-2))
 (53 11 (:LINEAR X*Y>1-POSITIVE))
 (48 18 (:REWRITE DEFAULT-<-2))
 (29 17 (:REWRITE DEFAULT-*-2))
 (28 17 (:REWRITE DEFAULT-*-1))
 (27 17 (:REWRITE DEFAULT-+-1))
 (18 18 (:REWRITE DEFAULT-<-1))
 (9 9 (:REWRITE FOLD-CONSTS-IN-+))
 (6 3 (:REWRITE DEFAULT-UNARY-MINUS))
 (2 2 (:REWRITE NFIX-WHEN-NOT-NATP))
 (1 1 (:REWRITE NATP-RW))
 )
(BITOPS::BOUNDS-BY-INT-SQRT-CEILING
 (74 18 (:REWRITE DEFAULT-+-2))
 (69 39 (:REWRITE DEFAULT-<-1))
 (59 10 (:LINEAR X*Y>1-POSITIVE))
 (48 39 (:REWRITE DEFAULT-<-2))
 (33 18 (:REWRITE DEFAULT-*-2))
 (32 18 (:REWRITE DEFAULT-*-1))
 (30 18 (:REWRITE DEFAULT-+-1))
 (21 10 (:REWRITE DEFAULT-UNARY-MINUS))
 (12 4 (:REWRITE NATP-WHEN-GTE-0))
 (9 9 (:REWRITE FOLD-CONSTS-IN-+))
 (4 4 (:REWRITE NATP-WHEN-INTEGERP))
 (4 4 (:REWRITE NATP-RW))
 (4 2 (:TYPE-PRESCRIPTION |x < y  =>  0 < y-x|))
 (3 1 (:REWRITE ZP-WHEN-GT-0))
 (3 1 (:REWRITE POSP-RW))
 (2 2 (:REWRITE NFIX-WHEN-NOT-NATP))
 (1 1 (:REWRITE NATP-POSP))
 )
(BITOPS::LOWER-BOUND-BY-INT-SQRT-CEILING
 (3 1 (:LINEAR X*Y>1-POSITIVE))
 (1 1 (:REWRITE DEFAULT-<-2))
 (1 1 (:REWRITE DEFAULT-<-1))
 )
(BITOPS::LOWER-BOUND-BY-INT-SQRT-CEILING-GENERAL)
(BITOPS::UPPER-BOUND-BY-NEGATIVE-INT-SQRT-CEILING
 (6 5 (:REWRITE DEFAULT-<-2))
 (6 5 (:REWRITE DEFAULT-<-1))
 (2 1 (:REWRITE DEFAULT-UNARY-MINUS))
 (1 1 (:REWRITE DEFAULT-*-2))
 (1 1 (:REWRITE DEFAULT-*-1))
 (1 1 (:LINEAR X*Y>1-POSITIVE))
 )
(BITOPS::UPPER-BOUND-BY-NEGATIVE-INT-SQRT-CEILING-GENERAL)
(BITOPS::INT-SQRT-UNIQUE
 (57 33 (:REWRITE DEFAULT-+-2))
 (33 33 (:REWRITE DEFAULT-+-1))
 (30 30 (:REWRITE DEFAULT-*-2))
 (30 30 (:REWRITE DEFAULT-*-1))
 (20 13 (:REWRITE DEFAULT-<-2))
 (15 15 (:REWRITE FOLD-CONSTS-IN-+))
 (14 13 (:REWRITE DEFAULT-<-1))
 (9 3 (:LINEAR X*Y>1-POSITIVE))
 (4 4 (:REWRITE NATP-RW))
 (2 2 (:REWRITE NATP-WHEN-INTEGERP))
 )
(BITOPS::INT-SQRT-UNIQUE-BY-REMAINDER
 (22 13 (:REWRITE DEFAULT-+-2))
 (13 13 (:REWRITE DEFAULT-+-1))
 (13 13 (:REWRITE DEFAULT-*-2))
 (13 13 (:REWRITE DEFAULT-*-1))
 (9 6 (:REWRITE DEFAULT-<-2))
 (8 6 (:REWRITE DEFAULT-<-1))
 (5 5 (:REWRITE FOLD-CONSTS-IN-+))
 (3 1 (:LINEAR X*Y>1-POSITIVE))
 (2 2 (:REWRITE NATP-RW))
 (2 1 (:REWRITE DEFAULT-UNARY-MINUS))
 (1 1 (:REWRITE NATP-WHEN-INTEGERP))
 )
(BITOPS::INT-SQRT-MONOTONIC
 (126 49 (:REWRITE DEFAULT-+-2))
 (81 38 (:REWRITE DEFAULT-<-2))
 (61 49 (:REWRITE DEFAULT-+-1))
 (55 41 (:REWRITE DEFAULT-*-2))
 (54 41 (:REWRITE DEFAULT-*-1))
 (42 38 (:REWRITE DEFAULT-<-1))
 (27 27 (:REWRITE FOLD-CONSTS-IN-+))
 (4 4 (:REWRITE NFIX-WHEN-NOT-NATP))
 (2 2 (:REWRITE NATP-RW))
 (1 1 (:REWRITE NATP-WHEN-INTEGERP))
 )
