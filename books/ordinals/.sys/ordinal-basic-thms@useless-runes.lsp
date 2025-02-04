(OLEN-POSP
 (40 4 (:REWRITE POSP-RW))
 (36 4 (:REWRITE NATP-POSP))
 (12 6 (:REWRITE DEFAULT-+-2))
 (8 8 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (8 8 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (8 4 (:REWRITE DEFAULT-<-2))
 (6 6 (:REWRITE DEFAULT-CDR))
 (6 6 (:REWRITE DEFAULT-+-1))
 (4 4 (:REWRITE DEFAULT-<-1))
 (4 4 (:META CANCEL_PLUS-LESSP-CORRECT))
 )
(MAKE-ORD-O-FIRST-EXPT
 (2 2 (:REWRITE DEFAULT-CAR))
 )
(MAKE-ORD-O-FIRST-COEFF
 (1 1 (:REWRITE DEFAULT-CDR))
 (1 1 (:REWRITE DEFAULT-CAR))
 )
(MAKE-ORD-O-RST)
(MAKE-ORD-O-INFP)
(MAKE-ORD-O-P
 (1407 14 (:DEFINITION O<))
 (1022 56 (:REWRITE O-FIRST-EXPT-<))
 (306 306 (:REWRITE DEFAULT-CAR))
 (210 210 (:TYPE-PRESCRIPTION O-FINP))
 (168 56 (:REWRITE O-FIRST-COEFF-<))
 (168 56 (:REWRITE O-FINP-<))
 (168 56 (:REWRITE AC-<))
 (99 99 (:REWRITE DEFAULT-CDR))
 (63 21 (:REWRITE O<=-O-FINP-DEF))
 (63 21 (:REWRITE O-INFP-O-FINP-O<=))
 (56 56 (:REWRITE |a < b & b < c  =>  a < c|))
 (56 56 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (56 28 (:REWRITE DEFAULT-<-2))
 (56 28 (:REWRITE DEFAULT-<-1))
 (36 36 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (36 36 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (28 28 (:META CANCEL_PLUS-LESSP-CORRECT))
 (28 7 (:REWRITE NATP-POSP))
 (14 14 (:TYPE-PRESCRIPTION NATP))
 (11 11 (:REWRITE NATP-RW))
 (7 7 (:REWRITE POSP-RW))
 )
(O-FIRST-EXPT-O-FIRST-COEFF-O-RST-ELIM
 (402 4 (:DEFINITION O<))
 (292 16 (:REWRITE O-FIRST-EXPT-<))
 (100 100 (:REWRITE DEFAULT-CAR))
 (60 60 (:TYPE-PRESCRIPTION O-FINP))
 (48 16 (:REWRITE O-FIRST-COEFF-<))
 (48 16 (:REWRITE O-FINP-<))
 (48 16 (:REWRITE AC-<))
 (35 35 (:REWRITE DEFAULT-CDR))
 (18 6 (:REWRITE O<=-O-FINP-DEF))
 (18 6 (:REWRITE O-INFP-O-FINP-O<=))
 (16 16 (:REWRITE |a < b & b < c  =>  a < c|))
 (16 16 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (16 8 (:REWRITE DEFAULT-<-2))
 (16 8 (:REWRITE DEFAULT-<-1))
 (11 11 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (11 11 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (8 8 (:META CANCEL_PLUS-LESSP-CORRECT))
 (8 2 (:REWRITE NATP-POSP))
 (4 4 (:TYPE-PRESCRIPTION NATP))
 (2 2 (:REWRITE POSP-RW))
 (2 2 (:REWRITE NATP-RW))
 )
(MAKE-ORD-EQUAL-2
 (9 9 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (9 9 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (6 6 (:REWRITE DEFAULT-CDR))
 (6 6 (:REWRITE DEFAULT-CAR))
 )
(MAKE-ORD-CAR
 (5 5 (:REWRITE DEFAULT-CAR))
 (1 1 (:REWRITE DEFAULT-CDR))
 )
(MAKE-ORD-DEF-CONSP)
(OMEGA-O-INFP)
(OMEGA-O-P)
(OMEGA-O-FIRST-EXPT)
(OMEGA-O-FIRST-COEFF)
(OMEGA-O-RST)
(OMEGA-LIMITP)
(O-FINP-O-RST)
(ACL2-COUNT-O-RST)
(ACL2-COUNT-O-RST-2
 (118 57 (:REWRITE DEFAULT-+-2))
 (79 57 (:REWRITE DEFAULT-+-1))
 (60 12 (:DEFINITION INTEGER-ABS))
 (48 12 (:REWRITE COMMUTATIVITY-OF-+))
 (48 6 (:DEFINITION LENGTH))
 (30 6 (:DEFINITION LEN))
 (18 15 (:REWRITE DEFAULT-<-2))
 (17 17 (:REWRITE DEFAULT-CDR))
 (17 15 (:REWRITE DEFAULT-<-1))
 (16 16 (:REWRITE FOLD-CONSTS-IN-+))
 (12 12 (:REWRITE DEFAULT-UNARY-MINUS))
 (9 9 (:REWRITE DEFAULT-CAR))
 (6 6 (:TYPE-PRESCRIPTION LEN))
 (6 6 (:REWRITE NUMERATOR-WHEN-INTEGERP))
 (6 6 (:REWRITE INTEGERP==>DENOMINATOR=1))
 (6 6 (:REWRITE DEFAULT-REALPART))
 (6 6 (:REWRITE DEFAULT-NUMERATOR))
 (6 6 (:REWRITE DEFAULT-IMAGPART))
 (6 6 (:REWRITE DEFAULT-DENOMINATOR))
 (6 6 (:REWRITE DEFAULT-COERCE-2))
 (6 6 (:REWRITE DEFAULT-COERCE-1))
 )
(O-FIRST-EXPT-1-O-FINP-O-RST
 (216 14 (:REWRITE O-FIRST-EXPT-<))
 (108 108 (:REWRITE DEFAULT-CAR))
 (42 14 (:REWRITE O-FINP-<))
 (42 14 (:REWRITE AC-<))
 (40 40 (:REWRITE DEFAULT-CDR))
 (40 10 (:REWRITE NATP-POSP))
 (30 14 (:REWRITE O-FIRST-COEFF-<))
 (27 14 (:REWRITE DEFAULT-<-1))
 (20 20 (:TYPE-PRESCRIPTION NATP))
 (20 14 (:REWRITE DEFAULT-<-2))
 (19 19 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (18 6 (:REWRITE O<=-O-FINP-DEF))
 (18 6 (:REWRITE O-INFP-O-FINP-O<=))
 (14 14 (:REWRITE |a < b & b < c  =>  a < c|))
 (14 14 (:META CANCEL_PLUS-LESSP-CORRECT))
 (12 12 (:REWRITE O-FINP-O-RST))
 (12 12 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (12 12 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (11 11 (:REWRITE NATP-RW))
 (10 10 (:REWRITE POSP-RW))
 )
(CDR-O-RST)
(O-FIRST-EXPT-O-P
 (442 4 (:DEFINITION O<))
 (312 16 (:REWRITE O-FIRST-EXPT-<))
 (104 18 (:DEFINITION O-FIRST-COEFF))
 (97 97 (:REWRITE DEFAULT-CAR))
 (76 76 (:TYPE-PRESCRIPTION O-FINP))
 (68 18 (:REWRITE CDR-O-RST))
 (62 30 (:REWRITE O-FINP-O-RST))
 (48 16 (:REWRITE O-FIRST-COEFF-<))
 (48 16 (:REWRITE O-FINP-<))
 (48 16 (:REWRITE AC-<))
 (36 36 (:TYPE-PRESCRIPTION O<))
 (18 6 (:REWRITE O<=-O-FINP-DEF))
 (18 6 (:REWRITE O-INFP-O-FINP-O<=))
 (16 16 (:REWRITE |a < b & b < c  =>  a < c|))
 (16 16 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (16 8 (:REWRITE DEFAULT-<-2))
 (16 8 (:REWRITE DEFAULT-<-1))
 (10 10 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (10 10 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (8 8 (:META CANCEL_PLUS-LESSP-CORRECT))
 (8 2 (:REWRITE NATP-POSP))
 (4 4 (:TYPE-PRESCRIPTION NATP))
 (4 4 (:REWRITE NATP-RW))
 (2 2 (:REWRITE POSP-RW))
 )
(|(o-first-expt a) < a|
 (4308 38 (:DEFINITION O<))
 (3125 156 (:REWRITE O-FIRST-EXPT-<))
 (1085 181 (:DEFINITION O-FIRST-COEFF))
 (800 800 (:REWRITE DEFAULT-CAR))
 (708 181 (:REWRITE CDR-O-RST))
 (687 156 (:REWRITE O-FIRST-COEFF-<))
 (622 273 (:REWRITE O-FINP-O-RST))
 (466 156 (:REWRITE O-FINP-<))
 (466 156 (:REWRITE AC-<))
 (168 84 (:REWRITE DEFAULT-<-1))
 (162 162 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (162 84 (:REWRITE DEFAULT-<-2))
 (160 54 (:REWRITE O-INFP-O-FINP-O<=))
 (156 156 (:REWRITE |a < b & b < c  =>  a < c|))
 (133 54 (:REWRITE O<=-O-FINP-DEF))
 (90 90 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (90 90 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (84 84 (:META CANCEL_PLUS-LESSP-CORRECT))
 (40 10 (:REWRITE NATP-POSP))
 (20 20 (:TYPE-PRESCRIPTION NATP))
 (15 15 (:REWRITE NATP-RW))
 (10 10 (:REWRITE POSP-RW))
 (9 9 (:REWRITE MAKE-ORD-O-FIRST-EXPT))
 (9 9 (:REWRITE MAKE-ORD-O-FIRST-COEFF))
 (3 3 (:REWRITE MAKE-ORD-O-RST))
 )
(O-FIRST-EXPT-<=
 (245 6 (:DEFINITION O<))
 (202 12 (:REWRITE O-FIRST-EXPT-<))
 (76 76 (:REWRITE DEFAULT-CAR))
 (60 11 (:DEFINITION O-FIRST-COEFF))
 (38 11 (:REWRITE CDR-O-RST))
 (37 21 (:REWRITE O-FINP-O-RST))
 (36 12 (:REWRITE O-FINP-<))
 (36 12 (:REWRITE AC-<))
 (28 12 (:REWRITE O-FIRST-COEFF-<))
 (22 11 (:REWRITE DEFAULT-<-1))
 (16 4 (:REWRITE NATP-POSP))
 (15 15 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (15 11 (:REWRITE DEFAULT-<-2))
 (15 5 (:REWRITE O<=-O-FINP-DEF))
 (15 5 (:REWRITE O-INFP-O-FINP-O<=))
 (12 12 (:REWRITE |a < b & b < c  =>  a < c|))
 (11 11 (:META CANCEL_PLUS-LESSP-CORRECT))
 (8 8 (:TYPE-PRESCRIPTION NATP))
 (5 5 (:REWRITE NATP-RW))
 (5 5 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (5 5 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (4 4 (:REWRITE POSP-RW))
 )
(O-FIRST-EXPT-0-NATP
 (221 2 (:DEFINITION O<))
 (156 8 (:REWRITE O-FIRST-EXPT-<))
 (53 53 (:REWRITE DEFAULT-CAR))
 (52 9 (:DEFINITION O-FIRST-COEFF))
 (34 9 (:REWRITE CDR-O-RST))
 (31 15 (:REWRITE O-FINP-O-RST))
 (24 8 (:REWRITE O-FIRST-COEFF-<))
 (24 8 (:REWRITE O-FINP-<))
 (24 8 (:REWRITE AC-<))
 (9 3 (:REWRITE O<=-O-FINP-DEF))
 (9 3 (:REWRITE O-INFP-O-FINP-O<=))
 (8 8 (:REWRITE |a < b & b < c  =>  a < c|))
 (8 8 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (8 4 (:REWRITE DEFAULT-<-2))
 (8 4 (:REWRITE DEFAULT-<-1))
 (6 6 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (6 6 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (4 4 (:META CANCEL_PLUS-LESSP-CORRECT))
 (4 1 (:REWRITE NATP-POSP))
 (2 2 (:TYPE-PRESCRIPTION NATP))
 (2 2 (:REWRITE NATP-RW))
 (1 1 (:REWRITE POSP-RW))
 )
(<=-O-FIRST-EXPT-<=)
(O-FIRST-EXPT-NATP
 (9 9 (:REWRITE DEFAULT-CAR))
 (1 1 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (1 1 (:META CANCEL_PLUS-EQUAL-CORRECT))
 )
(O-FIRST-EXPT-O-INFP)
(O-FIRST-EXPT-O-INFP-2
 (675 29 (:REWRITE O-FIRST-EXPT-<))
 (420 1 (:REWRITE |~(a<0)|))
 (296 4 (:REWRITE O-INFP-O-FINP-O<=))
 (271 17 (:REWRITE O-FIRST-EXPT-0-NATP))
 (212 212 (:REWRITE DEFAULT-CAR))
 (164 33 (:DEFINITION O-FIRST-COEFF))
 (98 33 (:REWRITE CDR-O-RST))
 (95 63 (:REWRITE O-FINP-O-RST))
 (89 29 (:REWRITE O-FIRST-COEFF-<))
 (75 29 (:REWRITE O-FINP-<))
 (75 29 (:REWRITE AC-<))
 (51 51 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (51 51 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (38 23 (:REWRITE DEFAULT-<-1))
 (32 10 (:REWRITE NATP-POSP))
 (29 29 (:REWRITE |a < b & b < c  =>  a < c|))
 (27 23 (:REWRITE DEFAULT-<-2))
 (23 23 (:META CANCEL_PLUS-LESSP-CORRECT))
 (19 19 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (16 16 (:REWRITE NATP-RW))
 (12 4 (:REWRITE O<=-O-FINP-DEF))
 (10 10 (:REWRITE POSP-RW))
 (4 2 (:REWRITE O-FIRST-EXPT-O-P))
 )
(O-FIRST-EXPT-DEF-O-FINP)
(O-FIRST-EXPT-EQUAL-O-FINP)
(ACL2-COUNT-O-FIRST-EXPT
 (236 110 (:REWRITE DEFAULT-+-2))
 (154 110 (:REWRITE DEFAULT-+-1))
 (110 22 (:DEFINITION INTEGER-ABS))
 (88 11 (:DEFINITION LENGTH))
 (55 11 (:DEFINITION LEN))
 (34 27 (:REWRITE DEFAULT-<-2))
 (30 27 (:REWRITE DEFAULT-<-1))
 (27 27 (:REWRITE DEFAULT-CDR))
 (22 22 (:REWRITE DEFAULT-UNARY-MINUS))
 (11 11 (:TYPE-PRESCRIPTION LEN))
 (11 11 (:REWRITE NUMERATOR-WHEN-INTEGERP))
 (11 11 (:REWRITE INTEGERP==>DENOMINATOR=1))
 (11 11 (:REWRITE DEFAULT-REALPART))
 (11 11 (:REWRITE DEFAULT-NUMERATOR))
 (11 11 (:REWRITE DEFAULT-IMAGPART))
 (11 11 (:REWRITE DEFAULT-DENOMINATOR))
 (11 11 (:REWRITE DEFAULT-COERCE-2))
 (11 11 (:REWRITE DEFAULT-COERCE-1))
 (1 1 (:REWRITE O-FIRST-EXPT-DEF-O-FINP))
 )
(NATP-O-FIRST-COEFF
 (316 2 (:DEFINITION O<))
 (211 8 (:REWRITE O-FIRST-EXPT-<))
 (143 25 (:REWRITE O-FIRST-EXPT-O-INFP))
 (101 46 (:REWRITE O-FIRST-EXPT-DEF-O-FINP))
 (72 72 (:TYPE-PRESCRIPTION O-FINP))
 (48 8 (:REWRITE O-FIRST-COEFF-<))
 (46 9 (:LINEAR O-FIRST-EXPT-<=))
 (42 10 (:REWRITE O-FIRST-EXPT-0-NATP))
 (35 17 (:REWRITE O-FINP-O-RST))
 (24 8 (:REWRITE O-FINP-<))
 (24 8 (:REWRITE AC-<))
 (19 11 (:REWRITE O-FIRST-EXPT-O-P))
 (18 18 (:TYPE-PRESCRIPTION O<))
 (18 3 (:REWRITE O-INFP-O-FINP-O<=))
 (13 13 (:REWRITE DEFAULT-CAR))
 (9 3 (:REWRITE O<=-O-FINP-DEF))
 (8 8 (:REWRITE |a < b & b < c  =>  a < c|))
 (8 8 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (8 8 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (8 8 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (8 4 (:REWRITE DEFAULT-<-2))
 (8 4 (:REWRITE DEFAULT-<-1))
 (4 4 (:META CANCEL_PLUS-LESSP-CORRECT))
 (4 1 (:REWRITE NATP-POSP))
 (3 3 (:REWRITE NATP-RW))
 (1 1 (:REWRITE POSP-RW))
 )
(POSP-O-FIRST-COEFF
 (316 2 (:DEFINITION O<))
 (211 8 (:REWRITE O-FIRST-EXPT-<))
 (143 25 (:REWRITE O-FIRST-EXPT-O-INFP))
 (101 46 (:REWRITE O-FIRST-EXPT-DEF-O-FINP))
 (72 72 (:TYPE-PRESCRIPTION O-FINP))
 (48 8 (:REWRITE O-FIRST-COEFF-<))
 (46 9 (:LINEAR O-FIRST-EXPT-<=))
 (42 10 (:REWRITE O-FIRST-EXPT-0-NATP))
 (35 17 (:REWRITE O-FINP-O-RST))
 (24 8 (:REWRITE O-FINP-<))
 (24 8 (:REWRITE AC-<))
 (19 11 (:REWRITE O-FIRST-EXPT-O-P))
 (18 3 (:REWRITE O-INFP-O-FINP-O<=))
 (13 13 (:REWRITE DEFAULT-CAR))
 (12 3 (:REWRITE NATP-POSP))
 (10 10 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (10 10 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (9 3 (:REWRITE O<=-O-FINP-DEF))
 (8 8 (:REWRITE |a < b & b < c  =>  a < c|))
 (8 8 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (8 4 (:REWRITE DEFAULT-<-2))
 (8 4 (:REWRITE DEFAULT-<-1))
 (6 6 (:TYPE-PRESCRIPTION NATP))
 (5 5 (:REWRITE NATP-RW))
 (4 4 (:META CANCEL_PLUS-LESSP-CORRECT))
 (3 3 (:REWRITE POSP-RW))
 )
(O-FIRST-COEFF-0
 (316 2 (:DEFINITION O<))
 (211 8 (:REWRITE O-FIRST-EXPT-<))
 (143 25 (:REWRITE O-FIRST-EXPT-O-INFP))
 (101 46 (:REWRITE O-FIRST-EXPT-DEF-O-FINP))
 (72 72 (:TYPE-PRESCRIPTION O-FINP))
 (48 8 (:REWRITE O-FIRST-COEFF-<))
 (46 9 (:LINEAR O-FIRST-EXPT-<=))
 (42 10 (:REWRITE O-FIRST-EXPT-0-NATP))
 (35 17 (:REWRITE O-FINP-O-RST))
 (24 8 (:REWRITE O-FINP-<))
 (24 8 (:REWRITE AC-<))
 (19 11 (:REWRITE O-FIRST-EXPT-O-P))
 (18 3 (:REWRITE O-INFP-O-FINP-O<=))
 (13 13 (:REWRITE DEFAULT-CAR))
 (10 10 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (10 10 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (9 3 (:REWRITE O<=-O-FINP-DEF))
 (8 8 (:REWRITE |a < b & b < c  =>  a < c|))
 (8 8 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (8 4 (:REWRITE DEFAULT-<-2))
 (8 4 (:REWRITE DEFAULT-<-1))
 (4 4 (:META CANCEL_PLUS-LESSP-CORRECT))
 (4 1 (:REWRITE NATP-POSP))
 (2 2 (:TYPE-PRESCRIPTION NATP))
 (2 2 (:REWRITE NATP-RW))
 (1 1 (:REWRITE POSP-RW))
 )
(POSP-O-FIRST-COEFF-2)
(O-FIRST-COEFF-DEF-O-FINP)
(O-P-O-INFP-CAR
 (828 6 (:DEFINITION O<))
 (573 24 (:REWRITE O-FIRST-EXPT-<))
 (407 71 (:REWRITE O-FIRST-EXPT-O-INFP))
 (285 128 (:REWRITE O-FIRST-EXPT-DEF-O-FINP))
 (144 24 (:REWRITE O-FIRST-COEFF-<))
 (130 25 (:LINEAR O-FIRST-EXPT-<=))
 (108 25 (:REWRITE O-FIRST-EXPT-0-NATP))
 (72 24 (:REWRITE O-FINP-<))
 (72 24 (:REWRITE AC-<))
 (54 9 (:REWRITE O-INFP-O-FINP-O<=))
 (45 30 (:REWRITE O-FIRST-EXPT-O-P))
 (27 27 (:REWRITE O-FIRST-COEFF-DEF-O-FINP))
 (27 9 (:REWRITE O<=-O-FINP-DEF))
 (24 24 (:REWRITE |a < b & b < c  =>  a < c|))
 (24 24 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (24 24 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (24 24 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (24 12 (:REWRITE DEFAULT-<-2))
 (24 12 (:REWRITE DEFAULT-<-1))
 (18 18 (:REWRITE O-FINP-O-RST))
 (12 12 (:META CANCEL_PLUS-LESSP-CORRECT))
 (12 3 (:REWRITE POSP-O-FIRST-COEFF))
 (12 3 (:REWRITE NATP-POSP))
 (7 7 (:REWRITE DEFAULT-CAR))
 (6 6 (:TYPE-PRESCRIPTION NATP))
 (6 6 (:REWRITE NATP-RW))
 (3 3 (:REWRITE POSP-RW))
 )
(O-P-O-INFP-CAR-2
 (1 1 (:REWRITE DEFAULT-CAR))
 )
(O-P-O-FIRST-EXPT-NEQ-0)
(O-P-O-P-O-RST
 (4 1 (:REWRITE POSP-O-FIRST-COEFF))
 (4 1 (:REWRITE O-P-O-INFP-CAR))
 (4 1 (:REWRITE O-P-O-FIRST-EXPT-NEQ-0))
 (4 1 (:REWRITE O-FIRST-EXPT-O-P))
 (4 1 (:REWRITE O-FIRST-EXPT-0-NATP))
 (4 1 (:REWRITE NATP-POSP))
 (2 2 (:TYPE-PRESCRIPTION NATP))
 (2 2 (:REWRITE O-FIRST-EXPT-DEF-O-FINP))
 (1 1 (:REWRITE POSP-RW))
 (1 1 (:REWRITE O-FIRST-COEFF-DEF-O-FINP))
 (1 1 (:REWRITE O-FINP-O-RST))
 (1 1 (:REWRITE NATP-RW))
 (1 1 (:REWRITE DEFAULT-CAR))
 (1 1 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (1 1 (:META CANCEL_PLUS-EQUAL-CORRECT))
 )
(O-P-<-O-FIRST-EXPT-O-FIRST-EXPT-O-RST
 (203 8 (:REWRITE O-FIRST-EXPT-<))
 (142 28 (:REWRITE O-FIRST-EXPT-O-INFP))
 (90 41 (:REWRITE O-FIRST-EXPT-DEF-O-FINP))
 (48 8 (:REWRITE O-FIRST-COEFF-<))
 (38 7 (:LINEAR O-FIRST-EXPT-<=))
 (31 7 (:REWRITE O-FIRST-EXPT-0-NATP))
 (28 7 (:REWRITE O-P-O-FIRST-EXPT-NEQ-0))
 (24 8 (:REWRITE O-FINP-<))
 (24 8 (:REWRITE AC-<))
 (18 3 (:REWRITE O-INFP-O-FINP-O<=))
 (15 10 (:REWRITE O-FIRST-EXPT-O-P))
 (9 9 (:REWRITE O-FIRST-COEFF-DEF-O-FINP))
 (9 3 (:REWRITE O<=-O-FINP-DEF))
 (8 8 (:REWRITE |a < b & b < c  =>  a < c|))
 (8 8 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (8 4 (:REWRITE DEFAULT-<-2))
 (8 4 (:REWRITE DEFAULT-<-1))
 (6 6 (:REWRITE O-FINP-O-RST))
 (6 6 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (6 6 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (4 4 (:META CANCEL_PLUS-LESSP-CORRECT))
 (4 1 (:REWRITE POSP-O-FIRST-COEFF))
 (4 1 (:REWRITE O-P-O-INFP-CAR))
 (4 1 (:REWRITE NATP-POSP))
 (2 2 (:TYPE-PRESCRIPTION NATP))
 (1 1 (:REWRITE POSP-RW))
 (1 1 (:REWRITE NATP-RW))
 (1 1 (:REWRITE DEFAULT-CAR))
 )
(O-P-DEF-O-FINP-1
 (2 2 (:REWRITE NATP-RW))
 )
(O-P-DEF-O-FINP-2)
(O-INFP->NEQ-0)
(LIMITP-O-P)
(LIMITP-O-INFP)
(LIMITP-NATPART)
(NOT-LIMITP-NATP
 (19 4 (:REWRITE O-FIRST-EXPT-O-INFP))
 (6 2 (:REWRITE O-FIRST-EXPT-DEF-O-FINP))
 (4 1 (:REWRITE O-P-O-FIRST-EXPT-NEQ-0))
 (4 1 (:REWRITE O-INFP->NEQ-0))
 (4 1 (:LINEAR O-FIRST-EXPT-<=))
 (3 1 (:REWRITE O-FIRST-EXPT-0-NATP))
 (2 2 (:REWRITE O-P-DEF-O-FINP-1))
 (1 1 (:REWRITE O-FINP-O-RST))
 )
(LIMITP-O-RST
 (85 19 (:REWRITE O-FIRST-EXPT-O-INFP))
 (30 11 (:REWRITE O-FIRST-EXPT-DEF-O-FINP))
 (28 6 (:REWRITE O-INFP->NEQ-0))
 (16 4 (:REWRITE O-P-O-FIRST-EXPT-NEQ-0))
 (16 4 (:LINEAR O-FIRST-EXPT-<=))
 (12 4 (:REWRITE O-FIRST-EXPT-0-NATP))
 (7 7 (:REWRITE O-FINP-O-RST))
 (6 1 (:REWRITE NOT-LIMITP-NATP))
 (3 3 (:REWRITE O-P-DEF-O-FINP-1))
 (2 2 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (2 2 (:META CANCEL_PLUS-EQUAL-CORRECT))
 )
(LIMITP-O-INFP-O-RST
 (82 18 (:REWRITE O-FIRST-EXPT-O-INFP))
 (28 10 (:REWRITE O-FIRST-EXPT-DEF-O-FINP))
 (22 5 (:REWRITE O-INFP->NEQ-0))
 (16 4 (:REWRITE O-P-O-FIRST-EXPT-NEQ-0))
 (16 4 (:LINEAR O-FIRST-EXPT-<=))
 (12 4 (:REWRITE O-FIRST-EXPT-0-NATP))
 (6 6 (:REWRITE O-FINP-O-RST))
 (6 1 (:REWRITE NOT-LIMITP-NATP))
 (2 2 (:REWRITE O-P-DEF-O-FINP-1))
 (1 1 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (1 1 (:META CANCEL_PLUS-EQUAL-CORRECT))
 )
(LIMITP-DEF)
(LIMITP-DEF-2
 (678 4 (:DEFINITION O<))
 (454 16 (:REWRITE O-FIRST-EXPT-<))
 (446 85 (:REWRITE O-FIRST-EXPT-O-INFP))
 (358 358 (:TYPE-PRESCRIPTION O-FINP))
 (201 87 (:REWRITE O-FIRST-EXPT-DEF-O-FINP))
 (112 17 (:LINEAR O-FIRST-EXPT-<=))
 (96 16 (:REWRITE O-FIRST-COEFF-<))
 (84 19 (:REWRITE O-INFP->NEQ-0))
 (82 15 (:REWRITE O-FIRST-EXPT-0-NATP))
 (64 26 (:REWRITE O-P-DEF-O-FINP-1))
 (60 15 (:REWRITE O-P-O-FIRST-EXPT-NEQ-0))
 (48 16 (:REWRITE O-FINP-<))
 (48 16 (:REWRITE AC-<))
 (37 1 (:REWRITE LIMITP-DEF))
 (36 6 (:REWRITE O-INFP-O-FINP-O<=))
 (22 18 (:REWRITE O-FIRST-EXPT-O-P))
 (18 6 (:REWRITE O<=-O-FINP-DEF))
 (16 16 (:REWRITE |a < b & b < c  =>  a < c|))
 (16 16 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (16 16 (:REWRITE O-FIRST-COEFF-DEF-O-FINP))
 (16 16 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (16 16 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (16 8 (:REWRITE DEFAULT-<-2))
 (16 8 (:REWRITE DEFAULT-<-1))
 (15 13 (:REWRITE O-FINP-O-RST))
 (12 2 (:REWRITE NOT-LIMITP-NATP))
 (8 8 (:META CANCEL_PLUS-LESSP-CORRECT))
 (8 2 (:REWRITE NATP-POSP))
 (4 4 (:TYPE-PRESCRIPTION NATP))
 (2 2 (:REWRITE POSP-RW))
 (2 2 (:REWRITE NATP-RW))
 )
(NATPART-O-FINP
 (182 21 (:REWRITE O-FIRST-EXPT-O-INFP))
 (42 14 (:REWRITE O-P-DEF-O-FINP-1))
 (42 7 (:REWRITE O-FIRST-EXPT-0-NATP))
 (42 7 (:LINEAR O-FIRST-EXPT-<=))
 (28 7 (:REWRITE O-P-O-FIRST-EXPT-NEQ-0))
 (28 7 (:REWRITE O-INFP->NEQ-0))
 (21 7 (:REWRITE O-FIRST-EXPT-DEF-O-FINP))
 (7 7 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (7 7 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (2 2 (:REWRITE O-FINP-O-RST))
 )
(NATPART-NATP
 (76 16 (:REWRITE O-FIRST-EXPT-O-INFP))
 (24 8 (:REWRITE O-FIRST-EXPT-DEF-O-FINP))
 (16 4 (:REWRITE O-P-O-FIRST-EXPT-NEQ-0))
 (16 4 (:REWRITE O-INFP->NEQ-0))
 (16 4 (:LINEAR O-FIRST-EXPT-<=))
 (12 4 (:REWRITE O-FIRST-EXPT-0-NATP))
 (4 4 (:REWRITE NATP-RW))
 (2 2 (:REWRITE O-FINP-O-RST))
 )
(NATPART-DEF-O-FINP
 (50 25 (:TYPE-PRESCRIPTION NATPART-NATP))
 (26 3 (:REWRITE O-FIRST-EXPT-O-INFP))
 (6 2 (:REWRITE O-P-DEF-O-FINP-1))
 (6 1 (:REWRITE O-FIRST-EXPT-0-NATP))
 (6 1 (:LINEAR O-FIRST-EXPT-<=))
 (4 1 (:REWRITE O-P-O-FIRST-EXPT-NEQ-0))
 (4 1 (:REWRITE O-INFP->NEQ-0))
 (3 1 (:REWRITE O-FIRST-EXPT-DEF-O-FINP))
 (1 1 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (1 1 (:META CANCEL_PLUS-EQUAL-CORRECT))
 )
(NATPART-O-RST
 (88 44 (:TYPE-PRESCRIPTION NATPART-NATP))
 (78 9 (:REWRITE O-FIRST-EXPT-O-INFP))
 (18 6 (:REWRITE O-P-DEF-O-FINP-1))
 (18 3 (:REWRITE O-FIRST-EXPT-0-NATP))
 (18 3 (:LINEAR O-FIRST-EXPT-<=))
 (16 6 (:REWRITE NATPART-DEF-O-FINP))
 (12 3 (:REWRITE O-P-O-FIRST-EXPT-NEQ-0))
 (12 3 (:REWRITE O-INFP->NEQ-0))
 (9 3 (:REWRITE O-FIRST-EXPT-DEF-O-FINP))
 (5 5 (:REWRITE O-FINP-O-RST))
 (3 3 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (3 3 (:META CANCEL_PLUS-EQUAL-CORRECT))
 )
(NATPART-MAKE-ORD
 (52 6 (:REWRITE O-FIRST-EXPT-O-INFP))
 (30 30 (:TYPE-PRESCRIPTION O-FINP))
 (17 6 (:REWRITE NATPART-DEF-O-FINP))
 (12 4 (:REWRITE O-P-DEF-O-FINP-1))
 (12 2 (:REWRITE O-FIRST-EXPT-0-NATP))
 (12 2 (:LINEAR O-FIRST-EXPT-<=))
 (8 2 (:REWRITE O-P-O-FIRST-EXPT-NEQ-0))
 (8 2 (:REWRITE O-INFP->NEQ-0))
 (6 2 (:REWRITE O-FIRST-EXPT-DEF-O-FINP))
 (4 3 (:REWRITE O-FINP-O-RST))
 (2 2 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (2 2 (:META CANCEL_PLUS-EQUAL-CORRECT))
 )
(LIMITPART-O-FIRST-EXPT
 (78 9 (:REWRITE O-FIRST-EXPT-O-INFP))
 (19 8 (:REWRITE O-FIRST-EXPT-DEF-O-FINP))
 (18 6 (:REWRITE O-P-DEF-O-FINP-1))
 (18 3 (:REWRITE O-FIRST-EXPT-0-NATP))
 (18 3 (:LINEAR O-FIRST-EXPT-<=))
 (12 3 (:REWRITE O-P-O-FIRST-EXPT-NEQ-0))
 (12 3 (:REWRITE O-INFP->NEQ-0))
 (4 4 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (4 4 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (3 3 (:TYPE-PRESCRIPTION MAKE-ORD))
 (3 3 (:REWRITE O-FIRST-COEFF-DEF-O-FINP))
 (3 3 (:REWRITE O-FINP-O-RST))
 )
(LIMITPART-O-FIRST-COEFF
 (52 6 (:REWRITE O-FIRST-EXPT-O-INFP))
 (12 4 (:REWRITE O-P-DEF-O-FINP-1))
 (12 2 (:REWRITE O-FIRST-EXPT-0-NATP))
 (12 2 (:LINEAR O-FIRST-EXPT-<=))
 (9 5 (:REWRITE O-FIRST-EXPT-DEF-O-FINP))
 (8 2 (:REWRITE O-P-O-FIRST-EXPT-NEQ-0))
 (8 2 (:REWRITE O-INFP->NEQ-0))
 (6 5 (:REWRITE O-FIRST-COEFF-DEF-O-FINP))
 (3 3 (:REWRITE O-FINP-O-RST))
 (2 2 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (2 2 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (1 1 (:TYPE-PRESCRIPTION MAKE-ORD))
 )
(LIMITPART-O-RST
 (78 9 (:REWRITE O-FIRST-EXPT-O-INFP))
 (18 6 (:REWRITE O-P-DEF-O-FINP-1))
 (18 3 (:REWRITE O-FIRST-EXPT-0-NATP))
 (18 3 (:LINEAR O-FIRST-EXPT-<=))
 (13 7 (:REWRITE O-FIRST-EXPT-DEF-O-FINP))
 (12 3 (:REWRITE O-P-O-FIRST-EXPT-NEQ-0))
 (12 3 (:REWRITE O-INFP->NEQ-0))
 (7 6 (:REWRITE O-FINP-O-RST))
 (4 4 (:REWRITE O-FIRST-COEFF-DEF-O-FINP))
 (3 3 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (3 3 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (1 1 (:TYPE-PRESCRIPTION MAKE-ORD))
 )
(LIMITPART-DEF-O-FINP
 (26 3 (:REWRITE O-FIRST-EXPT-O-INFP))
 (6 2 (:REWRITE O-P-DEF-O-FINP-1))
 (6 1 (:REWRITE O-FIRST-EXPT-0-NATP))
 (6 1 (:LINEAR O-FIRST-EXPT-<=))
 (4 1 (:REWRITE O-P-O-FIRST-EXPT-NEQ-0))
 (4 1 (:REWRITE O-INFP->NEQ-0))
 (3 1 (:REWRITE O-FIRST-EXPT-DEF-O-FINP))
 (1 1 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (1 1 (:META CANCEL_PLUS-EQUAL-CORRECT))
 )
(LIMITPART-OLEN
 (300 30 (:REWRITE O-FIRST-EXPT-O-INFP))
 (90 12 (:REWRITE O-P-O-FIRST-EXPT-NEQ-0))
 (78 24 (:REWRITE O-P-DEF-O-FINP-1))
 (72 12 (:REWRITE O-FIRST-EXPT-0-NATP))
 (72 12 (:LINEAR O-FIRST-EXPT-<=))
 (39 18 (:REWRITE O-FIRST-EXPT-DEF-O-FINP))
 (39 12 (:REWRITE O-INFP->NEQ-0))
 (18 3 (:REWRITE LIMITPART-O-RST))
 (15 15 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (15 15 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (14 7 (:REWRITE DEFAULT-+-2))
 (12 3 (:REWRITE LIMITPART-O-FIRST-EXPT))
 (9 8 (:REWRITE O-FINP-O-RST))
 (7 7 (:REWRITE DEFAULT-+-1))
 (6 6 (:TYPE-PRESCRIPTION LIMITPART))
 (6 6 (:REWRITE NATP-RW))
 (3 3 (:REWRITE O-FIRST-COEFF-DEF-O-FINP))
 )
(LIMITPART-O-FINP
 (278 24 (:REWRITE O-FIRST-EXPT-O-INFP))
 (85 13 (:REWRITE O-P-O-FIRST-EXPT-NEQ-0))
 (78 13 (:LINEAR O-FIRST-EXPT-<=))
 (75 23 (:REWRITE O-P-DEF-O-FINP-1))
 (63 13 (:REWRITE O-FIRST-EXPT-0-NATP))
 (34 13 (:REWRITE O-INFP->NEQ-0))
 (30 16 (:REWRITE O-FIRST-EXPT-DEF-O-FINP))
 (16 16 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (16 16 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (12 3 (:REWRITE LIMITPART-O-FIRST-EXPT))
 (6 6 (:REWRITE NATP-RW))
 (3 3 (:REWRITE O-FIRST-COEFF-DEF-O-FINP))
 (3 3 (:REWRITE O-FINP-O-RST))
 )
(LIMITPART-O-P
 (228 47 (:REWRITE O-FIRST-EXPT-O-INFP))
 (223 9 (:REWRITE O-FIRST-EXPT-<))
 (111 48 (:REWRITE O-FIRST-EXPT-DEF-O-FINP))
 (52 10 (:LINEAR O-FIRST-EXPT-<=))
 (48 15 (:REWRITE O-P-DEF-O-FINP-1))
 (48 8 (:REWRITE O-FIRST-COEFF-<))
 (39 9 (:REWRITE O-FIRST-EXPT-0-NATP))
 (36 9 (:REWRITE O-P-O-FIRST-EXPT-NEQ-0))
 (36 9 (:REWRITE O-INFP->NEQ-0))
 (27 9 (:REWRITE O-FINP-<))
 (27 9 (:REWRITE AC-<))
 (19 9 (:REWRITE |a < b & b < c  =>  a < c|))
 (18 3 (:REWRITE O-INFP-O-FINP-O<=))
 (13 5 (:REWRITE LIMITPART-DEF-O-FINP))
 (11 11 (:REWRITE O-FIRST-COEFF-DEF-O-FINP))
 (9 3 (:REWRITE O<=-O-FINP-DEF))
 (8 8 (:TYPE-PRESCRIPTION LIMITPART))
 (8 8 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (8 4 (:REWRITE LIMITPART-O-FINP))
 (8 4 (:REWRITE DEFAULT-<-2))
 (8 4 (:REWRITE DEFAULT-<-1))
 (6 6 (:REWRITE O-FINP-O-RST))
 (4 4 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (4 4 (:META CANCEL_PLUS-LESSP-CORRECT))
 (4 4 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (1 1 (:TYPE-PRESCRIPTION MAKE-ORD))
 (1 1 (:REWRITE |~(a < a)|))
 )
(LIMITPART
 (72 11 (:REWRITE O-FIRST-EXPT-O-INFP))
 (66 2 (:DEFINITION LIMITPART))
 (16 8 (:REWRITE O-FIRST-EXPT-DEF-O-FINP))
 (16 3 (:LINEAR O-FIRST-EXPT-<=))
 (15 5 (:REWRITE O-P-DEF-O-FINP-1))
 (15 3 (:REWRITE O-FIRST-EXPT-0-NATP))
 (12 4 (:REWRITE LIMITPART-DEF-O-FINP))
 (12 3 (:REWRITE O-P-O-FIRST-EXPT-NEQ-0))
 (12 3 (:REWRITE O-INFP->NEQ-0))
 (4 4 (:REWRITE O-FIRST-COEFF-DEF-O-FINP))
 (4 4 (:REWRITE O-FINP-O-RST))
 (2 2 (:REWRITE DEFAULT-CAR))
 (2 2 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (2 2 (:META CANCEL_PLUS-EQUAL-CORRECT))
 )
(NATPART-LIMITPART
 (390 45 (:REWRITE O-FIRST-EXPT-O-INFP))
 (96 3 (:REWRITE NOT-LIMITP-NATP))
 (90 30 (:REWRITE O-P-DEF-O-FINP-1))
 (90 15 (:REWRITE O-FIRST-EXPT-0-NATP))
 (90 15 (:LINEAR O-FIRST-EXPT-<=))
 (87 18 (:REWRITE O-INFP->NEQ-0))
 (60 15 (:REWRITE O-P-O-FIRST-EXPT-NEQ-0))
 (52 22 (:REWRITE O-FIRST-EXPT-DEF-O-FINP))
 (48 8 (:REWRITE NATPART-DEF-O-FINP))
 (18 18 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (18 18 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (10 10 (:REWRITE O-FINP-O-RST))
 (7 7 (:REWRITE O-FIRST-COEFF-DEF-O-FINP))
 (3 3 (:REWRITE NATPART-O-FINP))
 )
(LIMITPART-LIMITP
 (58 13 (:REWRITE O-FIRST-EXPT-O-INFP))
 (33 2 (:DEFINITION LIMITPART))
 (20 8 (:REWRITE O-FIRST-EXPT-DEF-O-FINP))
 (12 3 (:REWRITE O-P-O-FIRST-EXPT-NEQ-0))
 (12 3 (:REWRITE O-INFP->NEQ-0))
 (12 3 (:LINEAR O-FIRST-EXPT-<=))
 (10 4 (:REWRITE LIMITPART-DEF-O-FINP))
 (9 3 (:REWRITE O-FIRST-EXPT-0-NATP))
 (4 2 (:REWRITE O-P-DEF-O-FINP-1))
 (2 2 (:REWRITE O-FIRST-COEFF-DEF-O-FINP))
 (2 2 (:REWRITE O-FINP-O-RST))
 (1 1 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (1 1 (:META CANCEL_PLUS-EQUAL-CORRECT))
 )
(LIMITPART-LIMITP-TP
 (19 4 (:REWRITE O-FIRST-EXPT-O-INFP))
 (7 3 (:REWRITE O-FIRST-EXPT-DEF-O-FINP))
 (7 1 (:DEFINITION LIMITPART))
 (4 2 (:REWRITE LIMITPART-DEF-O-FINP))
 (4 1 (:REWRITE O-P-O-FIRST-EXPT-NEQ-0))
 (4 1 (:REWRITE O-INFP->NEQ-0))
 (4 1 (:LINEAR O-FIRST-EXPT-<=))
 (3 1 (:REWRITE O-FIRST-EXPT-0-NATP))
 (1 1 (:REWRITE O-P-DEF-O-FINP-1))
 (1 1 (:REWRITE O-FIRST-COEFF-DEF-O-FINP))
 (1 1 (:REWRITE O-FINP-O-RST))
 )
(O-P-O-LAST-EXPT
 (185 34 (:REWRITE O-FIRST-EXPT-O-INFP))
 (51 19 (:REWRITE O-FIRST-EXPT-DEF-O-FINP))
 (40 9 (:LINEAR O-FIRST-EXPT-<=))
 (36 9 (:REWRITE O-P-O-FIRST-EXPT-NEQ-0))
 (36 9 (:REWRITE O-INFP->NEQ-0))
 (33 9 (:REWRITE O-FIRST-EXPT-0-NATP))
 (8 8 (:REWRITE O-FINP-O-RST))
 (2 2 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (2 2 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (1 1 (:REWRITE NATP-RW))
 )
(O-LAST-EXPT-O-FIRST-EXPT-2
 (2924 18 (:DEFINITION O<))
 (1888 355 (:REWRITE O-FIRST-EXPT-O-INFP))
 (1826 72 (:REWRITE O-FIRST-EXPT-<))
 (458 82 (:LINEAR O-FIRST-EXPT-<=))
 (420 70 (:REWRITE O-FIRST-COEFF-<))
 (359 72 (:REWRITE |a < b & b < c  =>  a < c|))
 (343 69 (:REWRITE O-FIRST-EXPT-0-NATP))
 (288 71 (:REWRITE O-INFP->NEQ-0))
 (276 69 (:REWRITE O-P-O-FIRST-EXPT-NEQ-0))
 (216 72 (:REWRITE O-FINP-<))
 (216 72 (:REWRITE AC-<))
 (150 25 (:REWRITE O-INFP-O-FINP-O<=))
 (75 25 (:REWRITE O<=-O-FINP-DEF))
 (72 72 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (72 72 (:REWRITE O-FIRST-COEFF-DEF-O-FINP))
 (72 36 (:REWRITE DEFAULT-<-2))
 (72 36 (:REWRITE DEFAULT-<-1))
 (68 44 (:REWRITE O-FIRST-EXPT-O-P))
 (56 56 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (56 56 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (54 52 (:REWRITE O-FINP-O-RST))
 (36 36 (:META CANCEL_PLUS-LESSP-CORRECT))
 (35 35 (:REWRITE O-P-O-LAST-EXPT))
 (8 2 (:REWRITE NATP-POSP))
 (4 4 (:REWRITE NATP-RW))
 (2 2 (:REWRITE POSP-RW))
 )
(O-LAST-EXPT-0
 (291 54 (:REWRITE O-FIRST-EXPT-O-INFP))
 (82 18 (:REWRITE O-INFP->NEQ-0))
 (81 32 (:REWRITE O-FIRST-EXPT-DEF-O-FINP))
 (60 13 (:LINEAR O-FIRST-EXPT-<=))
 (52 13 (:REWRITE O-P-O-FIRST-EXPT-NEQ-0))
 (51 13 (:REWRITE O-FIRST-EXPT-0-NATP))
 (12 12 (:REWRITE O-FINP-O-RST))
 (9 9 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (9 9 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (1 1 (:REWRITE NATP-RW))
 )
(O-LAST-EXPT-DEF-O-INFP-1
 (130 15 (:REWRITE O-FIRST-EXPT-O-INFP))
 (30 10 (:REWRITE O-P-DEF-O-FINP-1))
 (30 5 (:REWRITE O-FIRST-EXPT-0-NATP))
 (30 5 (:LINEAR O-FIRST-EXPT-<=))
 (20 5 (:REWRITE O-P-O-FIRST-EXPT-NEQ-0))
 (20 5 (:REWRITE O-INFP->NEQ-0))
 (17 7 (:REWRITE O-FIRST-EXPT-DEF-O-FINP))
 (13 9 (:REWRITE O-FINP-O-RST))
 (6 6 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (6 6 (:META CANCEL_PLUS-EQUAL-CORRECT))
 )
(O-LAST-EXPT-DEF-O-INFP-2
 (52 6 (:REWRITE O-FIRST-EXPT-O-INFP))
 (12 4 (:REWRITE O-P-DEF-O-FINP-1))
 (12 2 (:REWRITE O-FIRST-EXPT-0-NATP))
 (12 2 (:LINEAR O-FIRST-EXPT-<=))
 (8 4 (:REWRITE O-FIRST-EXPT-DEF-O-FINP))
 (8 2 (:REWRITE O-P-O-FIRST-EXPT-NEQ-0))
 (8 2 (:REWRITE O-INFP->NEQ-0))
 (2 2 (:REWRITE O-FINP-O-RST))
 (2 2 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (2 2 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (1 1 (:REWRITE O-LAST-EXPT-DEF-O-INFP-1))
 )
(O-P-DROPN
 (12 5 (:REWRITE ZP-OPEN))
 (6 5 (:REWRITE DEFAULT-+-2))
 (5 5 (:REWRITE DEFAULT-+-1))
 (4 4 (:REWRITE O-FINP-O-RST))
 (4 1 (:REWRITE <-0-+-NEGATIVE-1))
 (3 3 (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
 (3 1 (:REWRITE FOLD-CONSTS-IN-+))
 (2 2 (:META CANCEL_PLUS-LESSP-CORRECT))
 (1 1 (:REWRITE NATP-RW))
 (1 1 (:REWRITE DEFAULT-<-2))
 (1 1 (:REWRITE DEFAULT-<-1))
 )
(DROPN-NEW-DEF
 (26 3 (:REWRITE O-FIRST-EXPT-O-INFP))
 (19 5 (:REWRITE ZP-OPEN))
 (9 7 (:REWRITE DEFAULT-+-2))
 (8 2 (:REWRITE <-0-+-NEGATIVE-1))
 (7 7 (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
 (7 7 (:REWRITE DEFAULT-+-1))
 (6 2 (:REWRITE O-P-DEF-O-FINP-1))
 (6 2 (:REWRITE FOLD-CONSTS-IN-+))
 (6 1 (:REWRITE O-FIRST-EXPT-0-NATP))
 (6 1 (:LINEAR O-FIRST-EXPT-<=))
 (5 5 (:REWRITE O-FINP-O-RST))
 (4 4 (:TYPE-PRESCRIPTION O-P))
 (4 4 (:META CANCEL_PLUS-LESSP-CORRECT))
 (4 1 (:REWRITE O-P-O-FIRST-EXPT-NEQ-0))
 (4 1 (:REWRITE O-INFP->NEQ-0))
 (3 1 (:REWRITE O-FIRST-EXPT-DEF-O-FINP))
 (2 2 (:REWRITE DEFAULT-<-2))
 (2 2 (:REWRITE DEFAULT-<-1))
 (2 2 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (2 2 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (2 2 (:DEFINITION NOT))
 )
(COUNT2)
