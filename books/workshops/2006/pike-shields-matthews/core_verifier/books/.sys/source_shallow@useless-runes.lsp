(NBITS-HLP
 (136 1 (:REWRITE O<=-O-FINP-DEF))
 (126 7 (:DEFINITION EXPT))
 (120 25 (:META CANCEL_PLUS-LESSP-CORRECT))
 (47 10 (:REWRITE DEFAULT-*-2))
 (39 21 (:REWRITE DEFAULT-<-2))
 (33 1 (:REWRITE NORMALIZE-<-MINUS-/))
 (32 25 (:REWRITE EXPT-WITH-VIOLATED-GUARDS))
 (26 20 (:REWRITE DEFAULT-+-2))
 (21 21 (:REWRITE DEFAULT-<-1))
 (20 20 (:REWRITE DEFAULT-+-1))
 (16 4 (:REWRITE DEFAULT-UNARY-MINUS))
 (16 1 (:REWRITE <-Y-*-X-Y))
 (14 14 (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
 (12 3 (:LINEAR EXPT->-1))
 (10 10 (:REWRITE DEFAULT-*-1))
 (9 1 (:REWRITE AC-<))
 (7 7 (:REWRITE ZIP-OPEN))
 (6 6 (:LINEAR EXPT-IS-INCREASING-FOR-BASE>1))
 (5 1 (:REWRITE O-INFP-O-FINP-O<=))
 (2 2 (:REWRITE EXPONENTS-ADD))
 (1 1 (:REWRITE |a < b & b < c  =>  a < c|))
 (1 1 (:REWRITE ZP-OPEN))
 (1 1 (:REWRITE NATP-RW))
 )
(NBITS)
(C-WORD-+)
(C-WORD--
 (3 3 (:TYPE-PRESCRIPTION |x < y  =>  0 < y-x|))
 )
(C-WORD-*)
(C-WORD-/
 (5 5 (:TYPE-PRESCRIPTION FLOOR-TYPE-3 . 2))
 (5 5 (:TYPE-PRESCRIPTION FLOOR-TYPE-3 . 1))
 (5 5 (:TYPE-PRESCRIPTION FLOOR-TYPE-1 . 2))
 (5 5 (:TYPE-PRESCRIPTION FLOOR-TYPE-1 . 1))
 )
(C-WORD-%
 (5 5 (:TYPE-PRESCRIPTION RATIONALP-MOD))
 (5 5 (:TYPE-PRESCRIPTION MOD-TYPE . 4))
 (5 5 (:TYPE-PRESCRIPTION MOD-TYPE . 3))
 (5 5 (:TYPE-PRESCRIPTION MOD-TYPE . 2))
 (5 5 (:TYPE-PRESCRIPTION MOD-TYPE . 1))
 (5 5 (:TYPE-PRESCRIPTION INTEGERP-MOD))
 )
(C-WORD-GCD
 (5 5 (:TYPE-PRESCRIPTION NONNEG-INT-GCD->-0))
 )
(C-WORD-**-HLP
 (10 1 (:REWRITE O<=-O-FINP-DEF))
 (7 7 (:REWRITE DEFAULT-*-2))
 (7 7 (:REWRITE DEFAULT-*-1))
 (6 6 (:META CANCEL_PLUS-LESSP-CORRECT))
 (5 5 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-POSITIVE))
 (5 5 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONZERO))
 (4 1 (:REWRITE <-Y-*-X-Y))
 (3 3 (:REWRITE DEFAULT-<-2))
 (3 3 (:REWRITE DEFAULT-<-1))
 (1 1 (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
 (1 1 (:REWRITE |a < b & b < c  =>  a < c|))
 (1 1 (:REWRITE ZP-OPEN))
 (1 1 (:REWRITE O-INFP-O-FINP-O<=))
 (1 1 (:REWRITE INTEGERP-+-MINUS-*))
 (1 1 (:REWRITE AC-<))
 )
(C-WORD-**)
(C-LG2-HLP
 (308 2 (:REWRITE O<=-O-FINP-DEF))
 (234 13 (:DEFINITION EXPT))
 (120 35 (:META CANCEL_PLUS-LESSP-CORRECT))
 (100 55 (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
 (89 19 (:REWRITE DEFAULT-*-2))
 (80 31 (:REWRITE DEFAULT-<-1))
 (74 31 (:REWRITE DEFAULT-<-2))
 (56 43 (:REWRITE EXPT-WITH-VIOLATED-GUARDS))
 (51 36 (:REWRITE DEFAULT-+-2))
 (41 2 (:REWRITE AC-<))
 (36 36 (:REWRITE DEFAULT-+-1))
 (35 1 (:REWRITE O-FIRST-EXPT-<))
 (33 10 (:REWRITE DEFAULT-UNARY-MINUS))
 (33 2 (:REWRITE O-FIRST-EXPT-DEF-O-FINP))
 (27 1 (:REWRITE NORMALIZE-<-MINUS-/))
 (23 2 (:REWRITE O-INFP-O-FINP-O<=))
 (19 19 (:REWRITE DEFAULT-*-1))
 (16 1 (:REWRITE <-Y-*-X-Y))
 (15 1 (:REWRITE O-FIRST-COEFF-<))
 (13 13 (:REWRITE ZIP-OPEN))
 (4 1 (:LINEAR EXPT->-1))
 (2 2 (:REWRITE |a < b & b < c  =>  a < c|))
 (2 2 (:REWRITE ZP-OPEN))
 (2 2 (:REWRITE NATP-RW))
 (2 2 (:REWRITE EXPONENTS-ADD))
 (2 2 (:LINEAR EXPT-IS-INCREASING-FOR-BASE>1))
 )
(C-LG2)
(C-WORD-MIN)
(C-WORD-MAX)
(C-WORD-NEG)
(C-WORD-<<)
(C-WORD->>)
(C-WORD-<<<
 (1 1 (:TYPE-PRESCRIPTION |x < y  =>  0 < y-x|))
 )
(C-WORD->>>
 (3 3 (:TYPE-PRESCRIPTION |x < y  =>  0 < y-x|))
 )
(C-WORD-APPEND-HLP
 (213 99 (:REWRITE DEFAULT-+-2))
 (176 3 (:REWRITE O<=-O-FINP-DEF))
 (150 26 (:META CANCEL_PLUS-LESSP-CORRECT))
 (138 99 (:REWRITE DEFAULT-+-1))
 (100 20 (:DEFINITION INTEGER-ABS))
 (80 20 (:REWRITE COMMUTATIVITY-OF-+))
 (80 10 (:DEFINITION LENGTH))
 (50 10 (:DEFINITION LEN))
 (31 25 (:REWRITE DEFAULT-<-2))
 (29 25 (:REWRITE DEFAULT-<-1))
 (20 20 (:REWRITE DEFAULT-UNARY-MINUS))
 (14 14 (:REWRITE DEFAULT-CAR))
 (12 2 (:REWRITE O-FIRST-EXPT-<))
 (11 3 (:REWRITE AC-<))
 (10 10 (:TYPE-PRESCRIPTION LEN))
 (10 10 (:REWRITE NUMERATOR-WHEN-INTEGERP))
 (10 10 (:REWRITE INTEGERP==>DENOMINATOR=1))
 (10 10 (:REWRITE DEFAULT-REALPART))
 (10 10 (:REWRITE DEFAULT-NUMERATOR))
 (10 10 (:REWRITE DEFAULT-IMAGPART))
 (10 10 (:REWRITE DEFAULT-DENOMINATOR))
 (10 10 (:REWRITE DEFAULT-COERCE-2))
 (10 10 (:REWRITE DEFAULT-COERCE-1))
 (8 4 (:REWRITE O-FIRST-EXPT-DEF-O-FINP))
 (6 3 (:REWRITE O-INFP-O-FINP-O<=))
 (4 2 (:REWRITE O-FIRST-COEFF-<))
 (3 3 (:REWRITE |a < b & b < c  =>  a < c|))
 )
(C-WORD-APPEND)
(C-WORD-EXTRACT-HLP)
(C-WORD-EXTRACT)
(C-WORD-JOIN-HLP)
(C-WORD-JOIN)
(C-WORD-SPLIT-HLP
 (1 1 (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
 )
(C-WORD-SPLIT)
(C-WORD-SEGMENT)
(MAKE-TRANS-WD)
(C-WORD-TRANSPOSE-HLP
 (9 9 (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
 )
(C-WORD-TRANSPOSE)
(C-WORD-REVERSE)
(C-WORD-PARITY)
(C-WORD-PADD)
(C-WORD-PMULT-HLP
 (1856 34 (:REWRITE UNIQUE-RATIONALP))
 (1620 12 (:REWRITE NIQ-TYPE . 2))
 (1214 32 (:REWRITE COMMUTATIVITY-OF-NONNEG-INT-GCD))
 (1182 32 (:DEFINITION NONNEG-INT-GCD))
 (992 32 (:DEFINITION NONNEG-INT-MOD))
 (754 80 (:REWRITE NONNEG-INT-MOD-WHEN-DIVIDES))
 (702 10 (:LINEAR NUMERATOR-GOES-DOWN-BY-INTEGER-DIVISION . 1))
 (678 6 (:DEFINITION NONNEGATIVE-INTEGER-QUOTIENT))
 (548 10 (:LINEAR LEAST-NUMERATOR-DENOMINATOR-<= . 2))
 (548 10 (:LINEAR LEAST-NUMERATOR-DENOMINATOR-<= . 1))
 (548 3 (:REWRITE O<=-O-FINP-DEF))
 (356 28 (:REWRITE NONNEG-INT-MOD-MINUS-0))
 (258 16 (:REWRITE DISTRIBUTIVITY))
 (254 2 (:LINEAR NIQ-TYPE))
 (224 192 (:TYPE-PRESCRIPTION NONNEG-INT-GCD->-0))
 (222 120 (:REWRITE /R-WHEN-ABS-NUMERATOR=1))
 (210 12 (:REWRITE NIQ-TYPE . 3))
 (198 182 (:REWRITE DEFAULT-*-2))
 (198 182 (:REWRITE DEFAULT-*-1))
 (192 192 (:TYPE-PRESCRIPTION NONNEG-INT-GCD))
 (130 10 (:LINEAR NONNEG-INT-MOD-<-DIVISOR))
 (128 32 (:DEFINITION ABS))
 (112 16 (:REWRITE FUNCTIONAL-COMMUTATIVITY-OF-MINUS-*-RIGHT))
 (99 93 (:REWRITE DEFAULT-<-1))
 (98 98 (:TYPE-PRESCRIPTION NONNEG-INT-MOD))
 (95 95 (:META CANCEL_PLUS-LESSP-CORRECT))
 (93 93 (:REWRITE DEFAULT-<-2))
 (80 74 (:REWRITE DEFAULT-+-2))
 (77 77 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (77 77 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (74 74 (:REWRITE DEFAULT-+-1))
 (70 70 (:REWRITE INTEGERP-+-MINUS-*))
 (60 60 (:REWRITE DEFAULT-UNARY-/))
 (48 48 (:TYPE-PRESCRIPTION |x < y  =>  0 < y-x|))
 (48 16 (:REWRITE COMMUTATIVITY-OF-+))
 (42 42 (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
 (34 34 (:REWRITE DEFAULT-UNARY-MINUS))
 (32 32 (:TYPE-PRESCRIPTION ABS))
 (30 10 (:REWRITE REDUCE-INTEGERP-+-CONSTANT))
 (28 28 (:REWRITE NONNEG-INT-MOD-+-0))
 (24 6 (:DEFINITION NFIX))
 (22 22 (:REWRITE DEFAULT-NUMERATOR))
 (16 16 (:REWRITE INVERSE-OF-*))
 (13 12 (:REWRITE INTEGERP==>DENOMINATOR=1))
 (12 12 (:REWRITE DEFAULT-DENOMINATOR))
 (10 10 (:LINEAR NUMERATOR-GOES-DOWN-BY-INTEGER-DIVISION . 2))
 (10 10 (:LINEAR LEAST-NUMERATOR-DENOMINATOR-<= . 3))
 (10 10 (:DEFINITION FIX))
 (8 1 (:REWRITE <-*-/-LEFT-COMMUTED))
 (5 3 (:REWRITE O-INFP-O-FINP-O<=))
 (5 3 (:REWRITE AC-<))
 (5 1 (:REWRITE O-FIRST-EXPT-<))
 (4 1 (:REWRITE <-Y-*-X-Y))
 (3 3 (:REWRITE |a < b & b < c  =>  a < c|))
 (3 3 (:REWRITE ZP-OPEN))
 (3 2 (:REWRITE O-FIRST-EXPT-DEF-O-FINP))
 (1 1 (:REWRITE O-FIRST-COEFF-<))
 )
(C-WORD-PMULT)
(C-WORD-PDIV-PMOD
 (3 3 (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
 )
(C-WORD-PDIV)
(C-WORD-PMOD)
(C-WORD-PGCD-HLP
 (6 6 (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
 )
(C-WORD-PGCD)
(C-WORD-PIRRED-HLP
 (5 5 (:META CANCEL_PLUS-LESSP-CORRECT))
 (5 1 (:REWRITE O<=-O-FINP-DEF))
 (4 3 (:REWRITE DEFAULT-+-2))
 (4 3 (:REWRITE DEFAULT-+-1))
 (3 3 (:REWRITE NATP-RW))
 (3 3 (:REWRITE DEFAULT-<-2))
 (3 3 (:REWRITE DEFAULT-<-1))
 (2 2 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (2 1 (:REWRITE O-INFP-O-FINP-O<=))
 (2 1 (:REWRITE AC-<))
 (1 1 (:REWRITE |a < b & b < c  =>  a < c|))
 (1 1 (:REWRITE FOLD-CONSTS-IN-+))
 (1 1 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (1 1 (:META CANCEL_PLUS-EQUAL-CORRECT))
 )
(C-WORD-PIRRED
 (3 3 (:TYPE-PRESCRIPTION FLOOR-TYPE-3 . 2))
 (3 3 (:TYPE-PRESCRIPTION FLOOR-TYPE-1 . 2))
 (3 3 (:TYPE-PRESCRIPTION FLOOR-TYPE-1 . 1))
 )
(C-WORD-PINV-HLP)
(C-WORD-PINV)
(C-==)
(C-!=)
(C-^)
(C-WORD-&&)
(C-WORD-OR)
(C-WORD-^^)
(C-~)
(C-VEC-<<
 (16 8 (:TYPE-PRESCRIPTION TRUE-LISTP-NTHCDR-TYPE-PRESCRIPTION))
 )
(C-VEC->>)
(C-VEC-<<<
 (16 8 (:TYPE-PRESCRIPTION TRUE-LISTP-NTHCDR-TYPE-PRESCRIPTION))
 (8 8 (:TYPE-PRESCRIPTION TRUE-LISTP))
 )
(C-VEC->>>)
(C-VEC-APPEND
 (1 1 (:TYPE-PRESCRIPTION TRUE-LISTP))
 )
(C-VEC-EXTRACT
 (2 1 (:TYPE-PRESCRIPTION TRUE-LISTP-NTHCDR-TYPE-PRESCRIPTION))
 (1 1 (:TYPE-PRESCRIPTION TRUE-LISTP))
 )
(C-VEC-JOIN
 (687 46 (:REWRITE O-FIRST-EXPT-<))
 (621 17 (:REWRITE O-INFP-O-FINP-O<=))
 (367 12 (:REWRITE O+-O-FIRST-EXPT-SMASH))
 (304 5 (:REWRITE |a <= b & c <= d  =>  a+c <= b+d|))
 (263 54 (:REWRITE AC-<))
 (260 8 (:REWRITE O-INFP-O+-3))
 (215 8 (:REWRITE O+-O-FIRST-COEFF-3))
 (208 17 (:REWRITE O<=-O-FINP-DEF))
 (201 21 (:REWRITE O-FIRST-EXPT-O-INFP))
 (139 4 (:REWRITE |(a <= b) & (c < d)  =>  ac < bd|))
 (133 12 (:REWRITE O+-ATOM-DEF))
 (78 39 (:REWRITE DEFAULT-+-2))
 (74 74 (:REWRITE DEFAULT-CDR))
 (72 9 (:LINEAR O-FIRST-EXPT-<=))
 (72 6 (:REWRITE O+-O-FIRST-EXPT-1))
 (60 13 (:REWRITE O-P-O-INFP-CAR))
 (57 57 (:REWRITE |a < b & b < c  =>  a < c|))
 (39 39 (:REWRITE DEFAULT-+-1))
 (39 13 (:REWRITE O-INFP-O*-2))
 (39 13 (:REWRITE O*-O-FIRST-EXPT-SMASH-2))
 (39 6 (:REWRITE O-FIRST-EXPT-0-NATP))
 (36 3 (:REWRITE O+-O-FIRST-COEFF-1))
 (32 8 (:REWRITE O-INFP-O+-2))
 (28 28 (:REWRITE DEFAULT-CAR))
 (27 6 (:REWRITE |~(a<0)|))
 (26 13 (:REWRITE O*-O-FINP))
 (20 10 (:REWRITE O-INFP->NEQ-0))
 (18 9 (:REWRITE O-FIRST-EXPT-O-P))
 (18 3 (:REWRITE O-P-O-FIRST-EXPT-NEQ-0))
 (14 7 (:REWRITE DEFAULT-<-2))
 (14 7 (:REWRITE DEFAULT-<-1))
 (13 13 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (13 13 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (11 11 (:META CANCEL_PLUS-LESSP-CORRECT))
 (5 1 (:REWRITE O+-O-FIRST-EXPT-SMASH-2))
 (3 3 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 )
(C-VEC-SPLIT
 (957 496 (:REWRITE DEFAULT-+-2))
 (670 28 (:REWRITE O<=-O-FINP-DEF))
 (649 496 (:REWRITE DEFAULT-+-1))
 (460 92 (:DEFINITION INTEGER-ABS))
 (368 46 (:DEFINITION LENGTH))
 (292 217 (:REWRITE DEFAULT-<-2))
 (292 217 (:REWRITE DEFAULT-<-1))
 (160 152 (:REWRITE DEFAULT-CDR))
 (156 25 (:REWRITE O-FIRST-EXPT-<))
 (122 57 (:TYPE-PRESCRIPTION TRUE-LISTP-NTHCDR-TYPE-PRESCRIPTION))
 (118 112 (:REWRITE FOLD-CONSTS-IN-+))
 (106 50 (:REWRITE O-FIRST-EXPT-DEF-O-FINP))
 (97 31 (:REWRITE AC-<))
 (92 92 (:REWRITE DEFAULT-UNARY-MINUS))
 (72 18 (:REWRITE O-P-O-INFP-CAR))
 (64 64 (:REWRITE DEFAULT-CAR))
 (56 28 (:REWRITE O-INFP-O-FINP-O<=))
 (56 25 (:REWRITE O-FIRST-COEFF-<))
 (47 47 (:REWRITE DEFAULT-REALPART))
 (47 47 (:REWRITE DEFAULT-IMAGPART))
 (46 46 (:REWRITE NUMERATOR-WHEN-INTEGERP))
 (46 46 (:REWRITE INTEGERP==>DENOMINATOR=1))
 (46 46 (:REWRITE DEFAULT-NUMERATOR))
 (46 46 (:REWRITE DEFAULT-DENOMINATOR))
 (46 46 (:REWRITE DEFAULT-COERCE-2))
 (46 46 (:REWRITE DEFAULT-COERCE-1))
 (45 45 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (33 4 (:REWRITE ZP-OPEN))
 (24 24 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (24 24 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (18 18 (:REWRITE O-P-DEF-O-FINP-1))
 (16 16 (:REWRITE NATP-RW))
 (16 8 (:REWRITE O-INFP->NEQ-0))
 (12 3 (:REWRITE <-0-+-NEGATIVE-1))
 (11 11 (:REWRITE EQUAL-CONSTANT-+))
 )
(C-VEC-SEGMENT
 (10 5 (:TYPE-PRESCRIPTION TRUE-LISTP-NTHCDR-TYPE-PRESCRIPTION))
 (5 5 (:TYPE-PRESCRIPTION TRUE-LISTP))
 )
(MAKE-ROWS
 (28 2 (:REWRITE O<=-O-FINP-DEF))
 (18 13 (:REWRITE DEFAULT-+-2))
 (14 14 (:TYPE-PRESCRIPTION |x < y  =>  0 < y-x|))
 (13 13 (:REWRITE DEFAULT-+-1))
 (12 7 (:REWRITE DEFAULT-<-1))
 (9 9 (:META CANCEL_PLUS-LESSP-CORRECT))
 (9 7 (:REWRITE DEFAULT-<-2))
 (7 6 (:REWRITE DEFAULT-UNARY-MINUS))
 (7 2 (:REWRITE AC-<))
 (7 1 (:REWRITE O-FIRST-EXPT-<))
 (5 2 (:REWRITE O-INFP-O-FINP-O<=))
 (5 2 (:REWRITE O-FIRST-EXPT-DEF-O-FINP))
 (4 4 (:REWRITE NATP-RW))
 (4 4 (:REWRITE FOLD-CONSTS-IN-+))
 (2 2 (:REWRITE |a < b & b < c  =>  a < c|))
 (2 1 (:REWRITE O-FIRST-COEFF-<))
 )
(C-VEC-TRANSPOSE-HLP
 (28 2 (:REWRITE O<=-O-FINP-DEF))
 (18 13 (:REWRITE DEFAULT-+-2))
 (14 14 (:TYPE-PRESCRIPTION |x < y  =>  0 < y-x|))
 (13 13 (:REWRITE DEFAULT-+-1))
 (12 7 (:REWRITE DEFAULT-<-1))
 (9 9 (:META CANCEL_PLUS-LESSP-CORRECT))
 (9 7 (:REWRITE DEFAULT-<-2))
 (7 6 (:REWRITE DEFAULT-UNARY-MINUS))
 (7 2 (:REWRITE AC-<))
 (7 1 (:REWRITE O-FIRST-EXPT-<))
 (5 2 (:REWRITE O-INFP-O-FINP-O<=))
 (5 2 (:REWRITE O-FIRST-EXPT-DEF-O-FINP))
 (4 4 (:REWRITE NATP-RW))
 (4 4 (:REWRITE FOLD-CONSTS-IN-+))
 (2 2 (:REWRITE |a < b & b < c  =>  a < c|))
 (2 1 (:REWRITE O-FIRST-COEFF-<))
 )
(C-VEC-TRANSPOSE)
(C-VEC-REVERSE-HLP
 (28 2 (:REWRITE O<=-O-FINP-DEF))
 (18 13 (:REWRITE DEFAULT-+-2))
 (13 13 (:REWRITE DEFAULT-+-1))
 (12 7 (:REWRITE DEFAULT-<-1))
 (9 9 (:META CANCEL_PLUS-LESSP-CORRECT))
 (9 7 (:REWRITE DEFAULT-<-2))
 (7 6 (:REWRITE DEFAULT-UNARY-MINUS))
 (7 2 (:REWRITE AC-<))
 (7 1 (:REWRITE O-FIRST-EXPT-<))
 (5 2 (:REWRITE O-INFP-O-FINP-O<=))
 (5 2 (:REWRITE O-FIRST-EXPT-DEF-O-FINP))
 (4 4 (:REWRITE NATP-RW))
 (4 4 (:REWRITE FOLD-CONSTS-IN-+))
 (2 2 (:REWRITE |a < b & b < c  =>  a < c|))
 (2 1 (:REWRITE O-FIRST-COEFF-<))
 )
(C-VEC-REVERSE)
