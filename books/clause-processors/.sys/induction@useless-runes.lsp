(APPLY-FOR-DEFEVALUATOR)
(INDEV)
(EVAL-LIST-KWOTE-LST)
(TRUE-LIST-FIX-EV-LST)
(EV-COMMUTES-CAR)
(EV-LST-COMMUTES-CDR)
(INDEV-OF-FNCALL-ARGS)
(INDEV-OF-VARIABLE)
(INDEV-OF-QUOTE)
(INDEV-OF-LAMBDA)
(INDEV-LST-OF-ATOM)
(INDEV-LST-OF-CONS)
(INDEV-OF-NONSYMBOL-ATOM)
(INDEV-OF-BAD-FNCALL)
(INDEV-OF-IF-CALL)
(INDEV-OF-O-P-CALL)
(INDEV-OF-O<-CALL
 (44 2 (:DEFINITION O<))
 (22 22 (:DEFINITION O-FINP))
 (16 8 (:DEFINITION O-FIRST-EXPT))
 (16 8 (:DEFINITION O-FIRST-COEFF))
 (4 4 (:DEFINITION O-RST))
 )
(INDEV-OF-NOT-CALL)
(INDEV-OF-BINARY-+-CALL)
(INDEV-OF-CONS-CALL)
(INDEV-DISJOIN-CONS)
(INDEV-DISJOIN-WHEN-CONSP)
(INDEV-DISJOIN-ATOM
 (1 1 (:REWRITE INDEV-OF-IF-CALL))
 )
(INDEV-DISJOIN-APPEND
 (23 23 (:REWRITE INDEV-OF-QUOTE))
 (23 23 (:REWRITE INDEV-OF-IF-CALL))
 )
(INDEV-CONJOIN-CONS)
(INDEV-CONJOIN-WHEN-CONSP)
(INDEV-CONJOIN-ATOM
 (1 1 (:REWRITE INDEV-OF-IF-CALL))
 )
(INDEV-CONJOIN-APPEND
 (23 23 (:REWRITE INDEV-OF-QUOTE))
 (23 23 (:REWRITE INDEV-OF-IF-CALL))
 )
(INDEV-CONJOIN-CLAUSES-CONS
 (100 50 (:DEFINITION DISJOIN))
 (50 50 (:DEFINITION DISJOIN2))
 (7 7 (:REWRITE INDEV-DISJOIN-ATOM))
 (5 5 (:REWRITE INDEV-CONJOIN-ATOM))
 )
(INDEV-CONJOIN-CLAUSES-WHEN-CONSP
 (24 24 (:REWRITE INDEV-OF-QUOTE))
 (24 24 (:REWRITE INDEV-OF-IF-CALL))
 (18 9 (:DEFINITION DISJOIN))
 (9 9 (:REWRITE INDEV-DISJOIN-ATOM))
 (9 9 (:DEFINITION DISJOIN2))
 )
(INDEV-CONJOIN-CLAUSES-ATOM
 (1 1 (:REWRITE INDEV-OF-IF-CALL))
 )
(INDEV-CONJOIN-CLAUSES-APPEND
 (65 65 (:REWRITE INDEV-OF-QUOTE))
 (65 65 (:REWRITE INDEV-OF-IF-CALL))
 (24 12 (:DEFINITION DISJOIN))
 (12 12 (:REWRITE INDEV-DISJOIN-ATOM))
 (12 12 (:DEFINITION DISJOIN2))
 )
(INDEV-THEOREMP-CONJOIN-CONS
 (53 53 (:REWRITE INDEV-CONJOIN-ATOM))
 )
(INDEV-THEOREMP-CONJOIN-APPEND)
(INDEV-THEOREMP-CONJOIN-CLAUSES-CONS
 (3 3 (:REWRITE INDEV-DISJOIN-ATOM))
 (3 3 (:REWRITE INDEV-CONJOIN-ATOM))
 )
(INDEV-THEOREMP-CONJOIN-CLAUSES-APPEND
 (15 15 (:REWRITE INDEV-DISJOIN-ATOM))
 )
(INDEV-THEOREMP-DISJOIN-CONS-UNLESS-THEOREMP
 (4 4 (:REWRITE INDEV-DISJOIN-ATOM))
 )
(INDEV-THEOREMP-DISJOIN-WHEN-CONSP-UNLESS-THEOREMP
 (4 4 (:REWRITE INDEV-DISJOIN-ATOM))
 )
(PSEUDO-TERM-ALIST-LISTP)
(INDUCTION-STEP-LISTP)
(PSEUDO-TERM-VAL-ALISTP-IMPLIES-ALISTP
 (432 16 (:REWRITE PSEUDO-TERMP-CADR-FROM-PSEUDO-TERM-LISTP))
 (408 32 (:REWRITE PSEUDO-TERMP-CAR))
 (368 56 (:REWRITE PSEUDO-TERMP-LIST-CDR))
 (160 32 (:DEFINITION LEN))
 (148 148 (:REWRITE DEFAULT-CDR))
 (146 146 (:REWRITE DEFAULT-CAR))
 (138 53 (:REWRITE PSEUDO-TERMP-OPENER))
 (104 104 (:REWRITE PSEUDO-TERM-LISTP-OF-ATOM))
 (102 102 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (64 32 (:REWRITE DEFAULT-+-2))
 (45 45 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (32 32 (:REWRITE DEFAULT-+-1))
 (32 32 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (32 32 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (32 16 (:DEFINITION TRUE-LISTP))
 (24 8 (:DEFINITION SYMBOL-LISTP))
 (8 8 (:REWRITE DEFAULT-COERCE-2))
 (8 8 (:REWRITE DEFAULT-COERCE-1))
 )
(SUBSTITUTE-LIST-INTO-CLAUSE
 (108 4 (:DEFINITION PSEUDO-TERM-LISTP))
 (28 4 (:REWRITE PSEUDO-TERM-LISTP-CDR))
 (24 4 (:REWRITE PSEUDO-TERMP-LIST-CDR))
 (24 4 (:REWRITE PSEUDO-TERMP-CAR))
 (18 18 (:REWRITE DEFAULT-CAR))
 (16 16 (:TYPE-PRESCRIPTION PSEUDO-TERMP))
 (16 16 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (16 16 (:REWRITE PSEUDO-TERM-LISTP-OF-ATOM))
 (12 12 (:REWRITE DEFAULT-CDR))
 (12 8 (:REWRITE PSEUDO-TERMP-OPENER))
 (9 3 (:DEFINITION ALISTP))
 (8 8 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (6 6 (:REWRITE PSEUDO-TERM-VAL-ALISTP-OF-ATOM))
 )
(SUBSTITUTE-LIST-INTO-CLAUSE-OF-CONS
 (5 5 (:REWRITE SUBSTITUTE-INTO-LIST-OF-ATOM))
 (3 3 (:REWRITE DEFAULT-CDR))
 (3 3 (:REWRITE DEFAULT-CAR))
 )
(SUBSTITUTE-LIST-INTO-CLAUSE-OF-ATOM)
(INDUCTION-STEPS
 (1674 12 (:DEFINITION PSEUDO-TERMP))
 (629 57 (:REWRITE PSEUDO-TERMP-CAR))
 (540 72 (:REWRITE PSEUDO-TERM-LISTP-CDR))
 (348 12 (:REWRITE PSEUDO-TERMP-CADR-FROM-PSEUDO-TERM-LISTP))
 (345 12 (:DEFINITION PSEUDO-TERM-LISTP))
 (300 36 (:DEFINITION LENGTH))
 (296 72 (:REWRITE PSEUDO-TERMP-LIST-CDR))
 (259 258 (:REWRITE DEFAULT-CDR))
 (252 251 (:REWRITE DEFAULT-CAR))
 (240 48 (:DEFINITION LEN))
 (204 84 (:REWRITE PSEUDO-TERMP-OPENER))
 (144 144 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (144 144 (:REWRITE PSEUDO-TERM-LISTP-OF-ATOM))
 (108 108 (:TYPE-PRESCRIPTION LEN))
 (96 48 (:REWRITE DEFAULT-+-2))
 (72 72 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (58 29 (:DEFINITION TRUE-LISTP))
 (48 48 (:REWRITE DEFAULT-+-1))
 (48 48 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (48 48 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (36 12 (:DEFINITION SYMBOL-LISTP))
 (12 12 (:TYPE-PRESCRIPTION SYMBOL-LISTP))
 (12 12 (:REWRITE PSEUDO-TERM-VAL-ALISTP-OF-ATOM))
 (12 12 (:REWRITE DEFAULT-COERCE-2))
 (12 12 (:REWRITE DEFAULT-COERCE-1))
 (9 9 (:REWRITE SUBSTITUTE-LIST-INTO-CLAUSE-OF-ATOM))
 (5 5 (:REWRITE SUBSTITUTE-INTO-LIST-OF-ATOM))
 )
(MEASURE-DECRS-SUBS
 (816 6 (:DEFINITION PSEUDO-TERMP))
 (214 34 (:REWRITE PSEUDO-TERM-LISTP-CDR))
 (180 16 (:REWRITE PSEUDO-TERMP-CAR))
 (174 6 (:REWRITE PSEUDO-TERMP-CADR-FROM-PSEUDO-TERM-LISTP))
 (150 34 (:REWRITE PSEUDO-TERMP-LIST-CDR))
 (150 18 (:DEFINITION LENGTH))
 (120 24 (:DEFINITION LEN))
 (114 114 (:REWRITE DEFAULT-CDR))
 (108 4 (:DEFINITION PSEUDO-TERM-LISTP))
 (102 102 (:REWRITE DEFAULT-CAR))
 (96 38 (:REWRITE PSEUDO-TERMP-OPENER))
 (64 64 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (64 64 (:REWRITE PSEUDO-TERM-LISTP-OF-ATOM))
 (54 54 (:TYPE-PRESCRIPTION LEN))
 (48 24 (:REWRITE DEFAULT-+-2))
 (32 32 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (24 24 (:REWRITE DEFAULT-+-1))
 (24 24 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (24 24 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (24 12 (:DEFINITION TRUE-LISTP))
 (18 6 (:DEFINITION SYMBOL-LISTP))
 (9 3 (:DEFINITION ALISTP))
 (6 6 (:TYPE-PRESCRIPTION SYMBOL-LISTP))
 (6 6 (:REWRITE PSEUDO-TERM-VAL-ALISTP-OF-ATOM))
 (6 6 (:REWRITE DEFAULT-COERCE-2))
 (6 6 (:REWRITE DEFAULT-COERCE-1))
 )
(MEASURE-DECRS
 (195 20 (:REWRITE PSEUDO-TERMP-CAR))
 (175 7 (:DEFINITION PSEUDO-TERM-LISTP))
 (153 21 (:REWRITE PSEUDO-TERM-LISTP-CDR))
 (91 21 (:REWRITE PSEUDO-TERMP-LIST-CDR))
 (87 3 (:REWRITE PSEUDO-TERMP-CADR-FROM-PSEUDO-TERM-LISTP))
 (68 68 (:REWRITE DEFAULT-CAR))
 (62 62 (:REWRITE DEFAULT-CDR))
 (60 12 (:DEFINITION LEN))
 (59 27 (:REWRITE PSEUDO-TERMP-OPENER))
 (49 49 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (49 49 (:REWRITE PSEUDO-TERM-LISTP-OF-ATOM))
 (24 24 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (24 12 (:REWRITE DEFAULT-+-2))
 (12 12 (:REWRITE DEFAULT-+-1))
 (12 12 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (12 12 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (12 6 (:DEFINITION TRUE-LISTP))
 (9 3 (:DEFINITION SYMBOL-LISTP))
 (3 3 (:REWRITE DEFAULT-COERCE-2))
 (3 3 (:REWRITE DEFAULT-COERCE-1))
 (2 2 (:REWRITE PSEUDO-TERM-VAL-ALISTP-OF-ATOM))
 )
(O-FIRST-EXPT-OF-MAKE-ORD
 (2 2 (:REWRITE DEFAULT-CAR))
 )
(O-FIRST-COEFF-OF-MAKE-ORD
 (1 1 (:REWRITE DEFAULT-CDR))
 (1 1 (:REWRITE DEFAULT-CAR))
 )
(O-RST-OF-MAKE-ORD)
(O-FINP-OF-MAKE-ORD)
(O-P-OF-MAKE-ORD
 (150 150 (:REWRITE DEFAULT-CAR))
 (54 54 (:REWRITE DEFAULT-CDR))
 (53 37 (:REWRITE DEFAULT-<-1))
 (48 37 (:REWRITE DEFAULT-<-2))
 (44 11 (:REWRITE ZP-WHEN-GT-0))
 (37 37 (:META CANCEL_PLUS-LESSP-CORRECT))
 (31 11 (:REWRITE ZP-OPEN))
 (27 27 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (16 4 (:REWRITE NATP-WHEN-GTE-0))
 (15 15 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (15 15 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (11 11 (:REWRITE ZP-WHEN-INTEGERP))
 (4 4 (:REWRITE NATP-WHEN-INTEGERP))
 (4 4 (:REWRITE NATP-RW))
 )
(O<-SELF
 (30 30 (:REWRITE DEFAULT-CAR))
 (18 18 (:REWRITE DEFAULT-CDR))
 (8 8 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (8 4 (:REWRITE DEFAULT-<-2))
 (8 4 (:REWRITE DEFAULT-<-1))
 (4 4 (:META CANCEL_PLUS-LESSP-CORRECT))
 )
(O<-OF-MAKE-ORD
 (28 28 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (28 14 (:REWRITE DEFAULT-<-2))
 (28 14 (:REWRITE DEFAULT-<-1))
 (18 18 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (18 18 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (14 14 (:META CANCEL_PLUS-LESSP-CORRECT))
 )
(ACL2-COUNT-OF-O-RST
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
(O-FIN-PART
 (67 2 (:DEFINITION ACL2-COUNT))
 (21 10 (:REWRITE DEFAULT-+-2))
 (14 10 (:REWRITE DEFAULT-+-1))
 (10 2 (:DEFINITION INTEGER-ABS))
 (8 2 (:REWRITE COMMUTATIVITY-OF-+))
 (8 1 (:DEFINITION LENGTH))
 (5 1 (:DEFINITION LEN))
 (4 4 (:REWRITE DEFAULT-<-2))
 (4 4 (:REWRITE DEFAULT-<-1))
 (4 4 (:META CANCEL_PLUS-LESSP-CORRECT))
 (4 1 (:REWRITE ZP-WHEN-GT-0))
 (3 3 (:REWRITE FOLD-CONSTS-IN-+))
 (3 3 (:REWRITE DEFAULT-CDR))
 (3 3 (:REWRITE DEFAULT-CAR))
 (2 2 (:REWRITE DEFAULT-UNARY-MINUS))
 (1 1 (:TYPE-PRESCRIPTION LEN))
 (1 1 (:REWRITE ZP-WHEN-INTEGERP))
 (1 1 (:REWRITE NUMERATOR-WHEN-INTEGERP))
 (1 1 (:REWRITE INTEGERP==>DENOMINATOR=1))
 (1 1 (:REWRITE DEFAULT-REALPART))
 (1 1 (:REWRITE DEFAULT-NUMERATOR))
 (1 1 (:REWRITE DEFAULT-IMAGPART))
 (1 1 (:REWRITE DEFAULT-DENOMINATOR))
 (1 1 (:REWRITE DEFAULT-COERCE-2))
 (1 1 (:REWRITE DEFAULT-COERCE-1))
 (1 1 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (1 1 (:META CANCEL_PLUS-EQUAL-CORRECT))
 )
(REPLACE-O-FIN-PART
 (67 2 (:DEFINITION ACL2-COUNT))
 (21 10 (:REWRITE DEFAULT-+-2))
 (14 10 (:REWRITE DEFAULT-+-1))
 (10 2 (:DEFINITION INTEGER-ABS))
 (8 2 (:REWRITE COMMUTATIVITY-OF-+))
 (8 1 (:DEFINITION LENGTH))
 (5 1 (:DEFINITION LEN))
 (3 3 (:REWRITE FOLD-CONSTS-IN-+))
 (3 3 (:REWRITE DEFAULT-CDR))
 (2 2 (:REWRITE DEFAULT-UNARY-MINUS))
 (2 2 (:REWRITE DEFAULT-CAR))
 (2 2 (:REWRITE DEFAULT-<-2))
 (2 2 (:REWRITE DEFAULT-<-1))
 (2 2 (:META CANCEL_PLUS-LESSP-CORRECT))
 (1 1 (:TYPE-PRESCRIPTION LEN))
 (1 1 (:REWRITE NUMERATOR-WHEN-INTEGERP))
 (1 1 (:REWRITE INTEGERP==>DENOMINATOR=1))
 (1 1 (:REWRITE DEFAULT-REALPART))
 (1 1 (:REWRITE DEFAULT-NUMERATOR))
 (1 1 (:REWRITE DEFAULT-IMAGPART))
 (1 1 (:REWRITE DEFAULT-DENOMINATOR))
 (1 1 (:REWRITE DEFAULT-COERCE-2))
 (1 1 (:REWRITE DEFAULT-COERCE-1))
 )
(O-FIRST-EXPT-OF-REPLACE-O-FIN-PART
 (36 4 (:REWRITE NFIX-WHEN-NATP))
 (24 4 (:REWRITE NFIX-WHEN-NOT-NATP))
 (20 8 (:REWRITE NATP-WHEN-GTE-0))
 (16 16 (:TYPE-PRESCRIPTION NATP))
 (8 8 (:REWRITE NATP-WHEN-INTEGERP))
 (8 8 (:REWRITE NATP-RW))
 (4 4 (:REWRITE DEFAULT-<-2))
 (4 4 (:REWRITE DEFAULT-<-1))
 (4 4 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (4 4 (:META CANCEL_PLUS-LESSP-CORRECT))
 (4 4 (:META CANCEL_PLUS-EQUAL-CORRECT))
 )
(O-FINP-OF-REPLACE-O-FIN-PART
 (18 2 (:REWRITE NFIX-WHEN-NATP))
 (12 2 (:REWRITE NFIX-WHEN-NOT-NATP))
 (10 4 (:REWRITE NATP-WHEN-GTE-0))
 (8 8 (:TYPE-PRESCRIPTION NATP))
 (4 4 (:REWRITE NATP-WHEN-INTEGERP))
 (4 4 (:REWRITE NATP-RW))
 (2 2 (:REWRITE DEFAULT-<-2))
 (2 2 (:REWRITE DEFAULT-<-1))
 (2 2 (:META CANCEL_PLUS-LESSP-CORRECT))
 (1 1 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (1 1 (:META CANCEL_PLUS-EQUAL-CORRECT))
 )
(O-FIRST-COEFF-OF-REPLACE-O-FIN-PART
 (66 10 (:REWRITE NFIX-WHEN-NATP))
 (45 10 (:REWRITE NFIX-WHEN-NOT-NATP))
 (35 14 (:REWRITE NATP-WHEN-GTE-0))
 (30 2 (:REWRITE NFIX-EQUAL-TO-NONZERO))
 (28 28 (:TYPE-PRESCRIPTION NATP))
 (16 2 (:REWRITE ZP-OPEN))
 (14 14 (:REWRITE NATP-WHEN-INTEGERP))
 (14 14 (:REWRITE NATP-RW))
 (13 13 (:REWRITE DEFAULT-<-2))
 (13 13 (:REWRITE DEFAULT-<-1))
 (13 13 (:META CANCEL_PLUS-LESSP-CORRECT))
 (8 2 (:REWRITE ZP-WHEN-GT-0))
 (3 3 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (3 3 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (2 2 (:TYPE-PRESCRIPTION ZP))
 (2 2 (:REWRITE ZP-WHEN-INTEGERP))
 (2 2 (:REWRITE NFIX-EQUAL-TO-NONZERO-CONST))
 )
(O-P-OF-FIRST-EXPT-WHEN-O-P
 (54 3 (:DEFINITION O<))
 (36 3 (:REWRITE POSP-REDEFINITION))
 (28 7 (:REWRITE NATP-WHEN-GTE-0))
 (25 19 (:REWRITE DEFAULT-<-2))
 (25 19 (:REWRITE DEFAULT-<-1))
 (19 19 (:META CANCEL_PLUS-LESSP-CORRECT))
 (15 3 (:REWRITE ZP-OPEN))
 (12 12 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (12 3 (:REWRITE ZP-WHEN-GT-0))
 (9 9 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (9 9 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (7 7 (:REWRITE NATP-WHEN-INTEGERP))
 (7 7 (:REWRITE NATP-RW))
 (4 4 (:REWRITE DEFAULT-CAR))
 (3 3 (:REWRITE ZP-WHEN-INTEGERP))
 )
(POSP-OF-FIRST-COEFF-WHEN-O-P
 (4 1 (:REWRITE O-P-OF-FIRST-EXPT-WHEN-O-P))
 (1 1 (:REWRITE DEFAULT-CAR))
 (1 1 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (1 1 (:META CANCEL_PLUS-EQUAL-CORRECT))
 )
(O-P-NFIX
 (9 1 (:REWRITE NFIX-WHEN-NATP))
 (6 1 (:REWRITE NFIX-WHEN-NOT-NATP))
 (5 2 (:REWRITE NATP-WHEN-GTE-0))
 (4 4 (:TYPE-PRESCRIPTION NATP))
 (2 2 (:REWRITE NATP-WHEN-INTEGERP))
 (2 2 (:REWRITE NATP-RW))
 (1 1 (:REWRITE DEFAULT-<-2))
 (1 1 (:REWRITE DEFAULT-<-1))
 (1 1 (:META CANCEL_PLUS-LESSP-CORRECT))
 )
(FIRST-<-RST-WHEN-O-P
 (18 4 (:REWRITE DEFAULT-<-1))
 (14 1 (:REWRITE ZP-WHEN-GT-0))
 (9 3 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (8 4 (:REWRITE DEFAULT-<-2))
 (7 1 (:REWRITE ZP-WHEN-INTEGERP))
 (4 4 (:META CANCEL_PLUS-LESSP-CORRECT))
 (4 1 (:REWRITE O-P-OF-FIRST-EXPT-WHEN-O-P))
 (3 3 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (3 3 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (1 1 (:REWRITE DEFAULT-CAR))
 )
(O-P-OF-O-RST
 (28 14 (:TYPE-PRESCRIPTION POSP-OF-FIRST-COEFF-WHEN-O-P))
 (14 1 (:REWRITE ZP-WHEN-GT-0))
 (7 1 (:REWRITE ZP-WHEN-INTEGERP))
 (4 2 (:REWRITE DEFAULT-<-2))
 (4 1 (:REWRITE O-P-OF-FIRST-EXPT-WHEN-O-P))
 (2 2 (:REWRITE DEFAULT-<-1))
 (2 2 (:META CANCEL_PLUS-LESSP-CORRECT))
 (1 1 (:REWRITE DEFAULT-CAR))
 (1 1 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (1 1 (:META CANCEL_PLUS-EQUAL-CORRECT))
 )
(O-P-REPLACE-O-FIN-PART
 (27 3 (:REWRITE NFIX-WHEN-NATP))
 (18 3 (:REWRITE NFIX-WHEN-NOT-NATP))
 (15 6 (:REWRITE NATP-WHEN-GTE-0))
 (12 12 (:TYPE-PRESCRIPTION NATP))
 (6 6 (:REWRITE NATP-WHEN-INTEGERP))
 (6 6 (:REWRITE NATP-RW))
 (3 3 (:REWRITE DEFAULT-<-2))
 (3 3 (:REWRITE DEFAULT-<-1))
 (3 3 (:META CANCEL_PLUS-LESSP-CORRECT))
 )
(REPLACE-O-FIN-PART
 (4 1 (:REWRITE NATP-WHEN-GTE-0))
 (1 1 (:REWRITE NATP-WHEN-INTEGERP))
 (1 1 (:REWRITE NATP-RW))
 (1 1 (:REWRITE DEFAULT-CAR))
 (1 1 (:REWRITE DEFAULT-<-2))
 (1 1 (:REWRITE DEFAULT-<-1))
 (1 1 (:META CANCEL_PLUS-LESSP-CORRECT))
 )
(O-FINP-OF-PLUS)
(O-FINP-OF-NFIX)
(O<-WHEN-O-FINP
 (4 4 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (4 2 (:REWRITE DEFAULT-<-2))
 (4 2 (:REWRITE DEFAULT-<-1))
 (2 2 (:META CANCEL_PLUS-LESSP-CORRECT))
 )
(REPLACE-O-FIN-PART-REL
 (1179 251 (:REWRITE DEFAULT-<-1))
 (1095 52 (:REWRITE FIRST-<-RST-WHEN-O-P))
 (1060 48 (:REWRITE O-P-OF-O-RST))
 (623 200 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (511 251 (:REWRITE DEFAULT-<-2))
 (420 30 (:REWRITE ZP-WHEN-GT-0))
 (210 30 (:REWRITE ZP-WHEN-INTEGERP))
 (187 187 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (187 187 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (172 52 (:REWRITE NATP-WHEN-GTE-0))
 (106 34 (:REWRITE NFIX-WHEN-NOT-NATP))
 (67 67 (:REWRITE DEFAULT-CAR))
 (54 54 (:TYPE-PRESCRIPTION NATP))
 (52 52 (:REWRITE NATP-WHEN-INTEGERP))
 (52 52 (:REWRITE NATP-RW))
 (41 41 (:TYPE-PRESCRIPTION O-FIN-PART))
 (39 22 (:REWRITE DEFAULT-+-2))
 (22 22 (:REWRITE DEFAULT-+-1))
 )
(REPLACE-O-FIN-PART-NONZERO
 (12 5 (:REWRITE DEFAULT-<-2))
 (8 2 (:REWRITE ZP-WHEN-GT-0))
 (5 5 (:REWRITE DEFAULT-<-1))
 (5 5 (:META CANCEL_PLUS-LESSP-CORRECT))
 (4 1 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (3 3 (:REWRITE NFIX-WHEN-NOT-NATP))
 (2 2 (:REWRITE ZP-WHEN-INTEGERP))
 (2 2 (:REWRITE ZP-OPEN))
 )
(O-FIRST-EXPT-OF-NFIX
 (9 1 (:REWRITE NFIX-WHEN-NATP))
 (6 1 (:REWRITE NFIX-WHEN-NOT-NATP))
 (5 2 (:REWRITE NATP-WHEN-GTE-0))
 (4 4 (:TYPE-PRESCRIPTION NATP))
 (2 2 (:REWRITE NATP-WHEN-INTEGERP))
 (2 2 (:REWRITE NATP-RW))
 (1 1 (:REWRITE DEFAULT-<-2))
 (1 1 (:REWRITE DEFAULT-<-1))
 (1 1 (:META CANCEL_PLUS-LESSP-CORRECT))
 )
(INDEV-ALIST)
(INDEV-SUBSTITUTE-INTO-TERM
 (110 94 (:REWRITE DEFAULT-CAR))
 (52 52 (:REWRITE DEFAULT-CDR))
 (47 27 (:REWRITE INDEV-OF-O<-CALL))
 (47 27 (:REWRITE INDEV-OF-O-P-CALL))
 (47 27 (:REWRITE INDEV-OF-NOT-CALL))
 (47 27 (:REWRITE INDEV-OF-IF-CALL))
 (34 34 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (34 34 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (16 16 (:REWRITE CAR-CONS))
 (14 2 (:DEFINITION ASSOC-EQUAL))
 (10 2 (:DEFINITION PAIRLIS$))
 (8 2 (:DEFINITION KWOTE-LST))
 (6 6 (:REWRITE INDEV-LST-OF-ATOM))
 (3 2 (:REWRITE DEFAULT-+-2))
 (3 2 (:REWRITE DEFAULT-+-1))
 (2 2 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (2 2 (:DEFINITION KWOTE))
 )
(LEN-EQUAL-0
 (9 5 (:REWRITE DEFAULT-+-2))
 (5 5 (:REWRITE DEFAULT-+-1))
 (4 4 (:REWRITE DEFAULT-CDR))
 (4 4 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (4 4 (:META CANCEL_PLUS-EQUAL-CORRECT))
 )
(NTHCDR-NIL
 (16 4 (:REWRITE ZP-WHEN-GT-0))
 (13 13 (:TYPE-PRESCRIPTION |x < y  =>  0 < y-x|))
 (6 2 (:REWRITE COMMUTATIVITY-OF-+))
 (4 4 (:REWRITE ZP-WHEN-INTEGERP))
 (4 4 (:REWRITE ZP-OPEN))
 (4 4 (:REWRITE DEFAULT-<-2))
 (4 4 (:REWRITE DEFAULT-<-1))
 (4 4 (:REWRITE DEFAULT-+-2))
 (4 4 (:REWRITE DEFAULT-+-1))
 (4 4 (:META CANCEL_PLUS-LESSP-CORRECT))
 )
(NTHCDR-OPEN
 (128 27 (:REWRITE ZP-WHEN-GT-0))
 (127 99 (:REWRITE DEFAULT-+-2))
 (102 99 (:REWRITE DEFAULT-+-1))
 (73 69 (:REWRITE DEFAULT-CDR))
 (63 51 (:REWRITE DEFAULT-<-2))
 (62 27 (:REWRITE ZP-WHEN-INTEGERP))
 (61 61 (:META CANCEL_PLUS-LESSP-CORRECT))
 (58 51 (:REWRITE DEFAULT-<-1))
 (55 55 (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
 (51 14 (:REWRITE NFIX-WHEN-NOT-NATP))
 (40 10 (:REWRITE <-0-+-NEGATIVE-1))
 (35 14 (:REWRITE NATP-WHEN-GTE-0))
 (32 32 (:TYPE-PRESCRIPTION |x < y  =>  0 < y-x|))
 (28 28 (:TYPE-PRESCRIPTION NATP))
 (22 22 (:REWRITE ZP-OPEN))
 (19 15 (:REWRITE DEFAULT-CAR))
 (14 14 (:REWRITE NATP-WHEN-INTEGERP))
 (14 14 (:REWRITE NATP-RW))
 (11 11 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (11 11 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (6 6 (:REWRITE INEQUALITY-WITH-NFIX-HYP-2))
 (2 2 (:REWRITE-QUOTED-CONSTANT NFIX-UNDER-NAT-EQUIV))
 (2 2 (:REWRITE-QUOTED-CONSTANT IFIX-UNDER-INT-EQUIV))
 )
(NTHCDR-END
 (55 10 (:REWRITE NTHCDR-OPEN))
 (37 27 (:REWRITE DEFAULT-<-2))
 (36 36 (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
 (36 9 (:REWRITE ZP-WHEN-GT-0))
 (32 32 (:TYPE-PRESCRIPTION |x < y  =>  0 < y-x|))
 (31 27 (:REWRITE DEFAULT-<-1))
 (29 22 (:REWRITE DEFAULT-+-2))
 (28 28 (:META CANCEL_PLUS-LESSP-CORRECT))
 (27 3 (:REWRITE INEQUALITY-WITH-NFIX-HYP-2))
 (26 10 (:REWRITE NFIX-WHEN-NOT-NATP))
 (22 22 (:REWRITE DEFAULT-+-1))
 (15 6 (:REWRITE NATP-WHEN-GTE-0))
 (12 12 (:TYPE-PRESCRIPTION NATP))
 (9 9 (:REWRITE ZP-WHEN-INTEGERP))
 (9 9 (:REWRITE ZP-OPEN))
 (6 6 (:REWRITE NATP-WHEN-INTEGERP))
 (6 6 (:REWRITE NATP-RW))
 )
(INDUCTION-CP-IND
 (670 80 (:REWRITE NATP-WHEN-INTEGERP))
 (659 64 (:REWRITE NFIX-WHEN-NOT-NATP))
 (410 80 (:REWRITE NATP-WHEN-GTE-0))
 (209 19 (:DEFINITION NTH))
 (204 12 (:DEFINITION O-FIN-PART))
 (168 93 (:REWRITE DEFAULT-+-2))
 (165 107 (:REWRITE DEFAULT-<-2))
 (165 107 (:REWRITE DEFAULT-<-1))
 (164 23 (:REWRITE ZP-WHEN-GT-0))
 (140 140 (:TYPE-PRESCRIPTION NATP))
 (135 15 (:REWRITE <-+-NEGATIVE-0-1))
 (130 15 (:REWRITE <-+-NEGATIVE-0-2))
 (117 93 (:REWRITE DEFAULT-+-1))
 (110 22 (:DEFINITION LEN))
 (72 12 (:DEFINITION REPLACE-O-FIN-PART))
 (61 61 (:REWRITE DEFAULT-CDR))
 (60 60 (:REWRITE NATP-RW))
 (50 50 (:REWRITE INEQUALITY-WITH-NFIX-HYP-1))
 (45 3 (:DEFINITION INDEV-ALIST))
 (44 22 (:REWRITE DEFAULT-UNARY-MINUS))
 (30 30 (:REWRITE INDEV-OF-VARIABLE))
 (30 30 (:REWRITE INDEV-OF-QUOTE))
 (30 30 (:REWRITE INDEV-OF-O<-CALL))
 (30 30 (:REWRITE INDEV-OF-O-P-CALL))
 (30 30 (:REWRITE INDEV-OF-NOT-CALL))
 (30 30 (:REWRITE INDEV-OF-LAMBDA))
 (30 30 (:REWRITE INDEV-OF-IF-CALL))
 (30 30 (:REWRITE INDEV-OF-CONS-CALL))
 (30 30 (:REWRITE INDEV-OF-BINARY-+-CALL))
 (30 30 (:REWRITE DEFAULT-CAR))
 (19 19 (:REWRITE ZP-OPEN))
 (8 8 (:REWRITE INEQUALITY-WITH-NFIX-HYP-2))
 (7 7 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (7 7 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (4 4 (:REWRITE FOLD-CONSTS-IN-+))
 )
(O-P-WHEN-THEOREMP
 (8 8 (:REWRITE DEFAULT-CAR))
 (6 4 (:REWRITE INDEV-OF-O<-CALL))
 (6 4 (:REWRITE INDEV-OF-NOT-CALL))
 (6 4 (:REWRITE INDEV-OF-CONS-CALL))
 (6 4 (:REWRITE INDEV-OF-BINARY-+-CALL))
 (2 2 (:REWRITE INDEV-OF-VARIABLE))
 (2 2 (:REWRITE INDEV-OF-QUOTE))
 (2 2 (:REWRITE INDEV-OF-LAMBDA))
 (2 2 (:REWRITE INDEV-OF-IF-CALL))
 (2 2 (:REWRITE DEFAULT-CDR))
 )
(MEASURE-DECR-WHEN-MEASURE-DECRS-SUBS
 (323 323 (:REWRITE DEFAULT-CAR))
 (322 322 (:REWRITE DEFAULT-CDR))
 (290 10 (:REWRITE PSEUDO-TERMP-CADR-FROM-PSEUDO-TERM-LISTP))
 (260 20 (:REWRITE PSEUDO-TERMP-CAR))
 (240 16 (:DEFINITION INDEV-ALIST))
 (210 50 (:REWRITE PSEUDO-TERMP-LIST-CDR))
 (209 209 (:TYPE-PRESCRIPTION PSEUDO-TERM-LISTP))
 (138 49 (:REWRITE PSEUDO-TERMP-OPENER))
 (134 114 (:REWRITE INDEV-OF-CONS-CALL))
 (134 114 (:REWRITE INDEV-OF-BINARY-+-CALL))
 (125 63 (:REWRITE DEFAULT-+-2))
 (105 35 (:DEFINITION BINARY-APPEND))
 (98 98 (:REWRITE INDEV-OF-O-P-CALL))
 (98 98 (:REWRITE INDEV-OF-LAMBDA))
 (98 98 (:REWRITE INDEV-OF-IF-CALL))
 (91 91 (:REWRITE INDEV-OF-VARIABLE))
 (87 87 (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
 (80 80 (:REWRITE PSEUDO-TERM-LISTP-OF-ATOM))
 (79 79 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (63 63 (:REWRITE DEFAULT-+-1))
 (52 20 (:REWRITE O<-WHEN-O-FINP))
 (40 40 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (40 40 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (40 20 (:DEFINITION TRUE-LISTP))
 (39 39 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (32 32 (:TYPE-PRESCRIPTION O-FINP))
 (30 10 (:DEFINITION SYMBOL-LISTP))
 (29 18 (:REWRITE DEFAULT-<-2))
 (21 18 (:REWRITE DEFAULT-<-1))
 (20 5 (:REWRITE ZP-WHEN-GT-0))
 (18 18 (:META CANCEL_PLUS-LESSP-CORRECT))
 (16 16 (:REWRITE INDEV-DISJOIN-ATOM))
 (14 8 (:REWRITE NFIX-WHEN-NOT-NATP))
 (14 7 (:REWRITE INDEV-CONJOIN-CLAUSES-ATOM))
 (10 10 (:REWRITE DEFAULT-COERCE-2))
 (10 10 (:REWRITE DEFAULT-COERCE-1))
 (7 7 (:TYPE-PRESCRIPTION MEASURE-DECRS-SUBS))
 (5 5 (:REWRITE ZP-WHEN-INTEGERP))
 (5 5 (:REWRITE ZP-OPEN))
 (5 2 (:REWRITE NATP-WHEN-GTE-0))
 (4 4 (:TYPE-PRESCRIPTION NATP))
 (2 2 (:REWRITE NATP-WHEN-INTEGERP))
 (2 2 (:REWRITE NATP-RW))
 (1 1 (:REWRITE INEQUALITY-WITH-NFIX-HYP-2))
 )
(MEASURE-DECR-WHEN-MEASURE-DECRS
 (410 410 (:REWRITE DEFAULT-CAR))
 (403 403 (:REWRITE DEFAULT-CDR))
 (352 88 (:DEFINITION BINARY-APPEND))
 (264 44 (:DEFINITION MEASURE-DECRS-SUBS))
 (203 7 (:REWRITE PSEUDO-TERMP-CADR-FROM-PSEUDO-TERM-LISTP))
 (182 14 (:REWRITE PSEUDO-TERMP-CAR))
 (147 35 (:REWRITE PSEUDO-TERMP-LIST-CDR))
 (146 146 (:TYPE-PRESCRIPTION PSEUDO-TERM-LISTP))
 (114 61 (:REWRITE DEFAULT-+-2))
 (105 7 (:DEFINITION INDEV-ALIST))
 (96 34 (:REWRITE PSEUDO-TERMP-OPENER))
 (94 94 (:TYPE-PRESCRIPTION MEASURE-DECRS-SUBS))
 (61 61 (:REWRITE DEFAULT-+-1))
 (60 14 (:REWRITE NFIX-WHEN-NOT-NATP))
 (58 40 (:REWRITE DEFAULT-<-2))
 (56 56 (:REWRITE PSEUDO-TERM-LISTP-OF-ATOM))
 (55 55 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (54 54 (:REWRITE INDEV-OF-O<-CALL))
 (54 54 (:REWRITE INDEV-OF-O-P-CALL))
 (54 54 (:REWRITE INDEV-OF-NOT-CALL))
 (54 54 (:REWRITE INDEV-OF-LAMBDA))
 (54 54 (:REWRITE INDEV-OF-IF-CALL))
 (54 54 (:REWRITE INDEV-OF-CONS-CALL))
 (54 54 (:REWRITE INDEV-OF-BINARY-+-CALL))
 (53 53 (:REWRITE INDEV-OF-VARIABLE))
 (51 40 (:REWRITE DEFAULT-<-1))
 (48 12 (:REWRITE ZP-WHEN-GT-0))
 (45 18 (:REWRITE NATP-WHEN-GTE-0))
 (40 40 (:META CANCEL_PLUS-LESSP-CORRECT))
 (39 39 (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
 (36 36 (:TYPE-PRESCRIPTION NATP))
 (32 16 (:REWRITE INDEV-CONJOIN-CLAUSES-ATOM))
 (28 28 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (28 28 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (28 14 (:DEFINITION TRUE-LISTP))
 (27 27 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (21 7 (:DEFINITION SYMBOL-LISTP))
 (18 18 (:REWRITE NATP-WHEN-INTEGERP))
 (18 18 (:REWRITE NATP-RW))
 (18 6 (:REWRITE O<-WHEN-O-FINP))
 (12 12 (:TYPE-PRESCRIPTION O-FINP))
 (12 12 (:REWRITE ZP-WHEN-INTEGERP))
 (12 12 (:REWRITE ZP-OPEN))
 (10 10 (:TYPE-PRESCRIPTION MEASURE-DECRS))
 (10 10 (:REWRITE INEQUALITY-WITH-NFIX-HYP-2))
 (7 7 (:REWRITE INDEV-DISJOIN-ATOM))
 (7 7 (:REWRITE DEFAULT-COERCE-2))
 (7 7 (:REWRITE DEFAULT-COERCE-1))
 )
(O-P-WITH-CLAUSE-WHEN-THEOREMP
 (29 5 (:REWRITE O-P-WHEN-THEOREMP))
 (12 10 (:REWRITE INDEV-OF-O<-CALL))
 (12 10 (:REWRITE INDEV-OF-NOT-CALL))
 (12 10 (:REWRITE INDEV-OF-CONS-CALL))
 (12 10 (:REWRITE INDEV-OF-BINARY-+-CALL))
 (11 11 (:REWRITE DEFAULT-CAR))
 (9 3 (:DEFINITION BINARY-APPEND))
 (8 8 (:REWRITE INDEV-OF-LAMBDA))
 (8 8 (:REWRITE INDEV-OF-IF-CALL))
 (6 6 (:REWRITE INDEV-OF-VARIABLE))
 (5 5 (:REWRITE DEFAULT-CDR))
 (2 2 (:REWRITE INDEV-DISJOIN-ATOM))
 )
(INDUCTION-STEP-RIGHT
 (235 47 (:DEFINITION SUBSTITUTE-LIST-INTO-CLAUSE))
 (195 195 (:REWRITE DEFAULT-CAR))
 (149 149 (:REWRITE DEFAULT-CDR))
 (94 94 (:REWRITE SUBSTITUTE-LIST-INTO-CLAUSE-OF-ATOM))
 (47 47 (:REWRITE SUBSTITUTE-INTO-LIST-OF-ATOM))
 (44 40 (:REWRITE INDEV-OF-CONS-CALL))
 (44 40 (:REWRITE INDEV-OF-BINARY-+-CALL))
 (41 39 (:REWRITE INDEV-OF-O<-CALL))
 (41 39 (:REWRITE INDEV-OF-O-P-CALL))
 (38 38 (:REWRITE INDEV-OF-LAMBDA))
 (30 15 (:REWRITE INDEV-CONJOIN-CLAUSES-ATOM))
 (28 28 (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
 (21 11 (:REWRITE DEFAULT-+-2))
 (20 5 (:REWRITE ZP-WHEN-GT-0))
 (17 11 (:REWRITE DEFAULT-<-2))
 (13 13 (:REWRITE INDEV-DISJOIN-ATOM))
 (12 11 (:REWRITE DEFAULT-<-1))
 (11 11 (:REWRITE DEFAULT-+-1))
 (11 11 (:META CANCEL_PLUS-LESSP-CORRECT))
 (8 8 (:TYPE-PRESCRIPTION INDUCTION-STEPS))
 (7 7 (:TYPE-PRESCRIPTION SUBSTITUTE-LIST-INTO-CLAUSE))
 (5 5 (:REWRITE ZP-WHEN-INTEGERP))
 (5 5 (:REWRITE ZP-OPEN))
 (4 3 (:REWRITE NFIX-WHEN-NOT-NATP))
 )
(INDEV-DISJOIN-SUBSTITUTE
 (544 4 (:DEFINITION PSEUDO-TERMP))
 (510 34 (:DEFINITION INDEV-ALIST))
 (378 14 (:DEFINITION PSEUDO-TERM-LISTP))
 (222 34 (:REWRITE PSEUDO-TERM-LISTP-CDR))
 (188 22 (:REWRITE PSEUDO-TERMP-CAR))
 (186 186 (:REWRITE DEFAULT-CAR))
 (170 170 (:REWRITE DEFAULT-CDR))
 (116 4 (:REWRITE PSEUDO-TERMP-CADR-FROM-PSEUDO-TERM-LISTP))
 (100 12 (:DEFINITION LENGTH))
 (98 98 (:REWRITE INDEV-OF-O<-CALL))
 (98 98 (:REWRITE INDEV-OF-O-P-CALL))
 (98 98 (:REWRITE INDEV-OF-NOT-CALL))
 (98 98 (:REWRITE INDEV-OF-LAMBDA))
 (98 98 (:REWRITE INDEV-OF-IF-CALL))
 (98 98 (:REWRITE INDEV-OF-CONS-CALL))
 (98 98 (:REWRITE INDEV-OF-BINARY-+-CALL))
 (98 48 (:REWRITE PSEUDO-TERMP-OPENER))
 (96 96 (:REWRITE INDEV-OF-VARIABLE))
 (88 88 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (82 55 (:REWRITE INDEV-DISJOIN-ATOM))
 (80 16 (:DEFINITION LEN))
 (44 44 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (32 16 (:REWRITE DEFAULT-+-2))
 (27 27 (:TYPE-PRESCRIPTION SUBSTITUTE-INTO-LIST))
 (16 16 (:REWRITE DEFAULT-+-1))
 (16 16 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (16 16 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (16 8 (:DEFINITION TRUE-LISTP))
 (12 4 (:DEFINITION SYMBOL-LISTP))
 (4 4 (:TYPE-PRESCRIPTION SYMBOL-LISTP))
 (4 4 (:REWRITE DEFAULT-COERCE-2))
 (4 4 (:REWRITE DEFAULT-COERCE-1))
 )
(INDEV-DISJOIN-ATOM-NO-BC)
(NTHCDR-0
 (22 11 (:TYPE-PRESCRIPTION TRUE-LISTP-NTHCDR-TYPE-PRESCRIPTION))
 (15 1 (:REWRITE NTHCDR-OPEN))
 (11 11 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (6 6 (:TYPE-PRESCRIPTION LEN))
 (5 1 (:DEFINITION LEN))
 (2 1 (:REWRITE DEFAULT-<-2))
 (2 1 (:REWRITE DEFAULT-+-2))
 (1 1 (:TYPE-PRESCRIPTION NFIX))
 (1 1 (:REWRITE-QUOTED-CONSTANT NFIX-UNDER-NAT-EQUIV))
 (1 1 (:REWRITE-QUOTED-CONSTANT IFIX-UNDER-INT-EQUIV))
 (1 1 (:REWRITE DEFAULT-CDR))
 (1 1 (:REWRITE DEFAULT-<-1))
 (1 1 (:REWRITE DEFAULT-+-1))
 (1 1 (:META CANCEL_PLUS-LESSP-CORRECT))
 )
(INDUCTION-CP-CORRECT-REC-WITH-ORIG-CLAUSE
 (597 105 (:REWRITE O-P-WHEN-THEOREMP))
 (500 76 (:REWRITE NFIX-WHEN-NATP))
 (426 420 (:REWRITE DEFAULT-CAR))
 (388 350 (:REWRITE INDEV-OF-O<-CALL))
 (388 350 (:REWRITE INDEV-OF-NOT-CALL))
 (388 350 (:REWRITE INDEV-OF-CONS-CALL))
 (388 350 (:REWRITE INDEV-OF-BINARY-+-CALL))
 (350 76 (:REWRITE NFIX-WHEN-NOT-NATP))
 (331 331 (:REWRITE INDEV-OF-LAMBDA))
 (331 331 (:REWRITE INDEV-OF-IF-CALL))
 (330 188 (:REWRITE INDEV-DISJOIN-ATOM-NO-BC))
 (314 314 (:REWRITE INDEV-OF-VARIABLE))
 (307 301 (:REWRITE DEFAULT-CDR))
 (280 56 (:DEFINITION LEN))
 (250 100 (:REWRITE NATP-WHEN-GTE-0))
 (200 200 (:TYPE-PRESCRIPTION NATP))
 (178 114 (:REWRITE DEFAULT-<-1))
 (178 89 (:REWRITE DEFAULT-+-2))
 (178 8 (:REWRITE ZP-WHEN-GT-0))
 (168 56 (:DEFINITION BINARY-APPEND))
 (148 114 (:REWRITE DEFAULT-<-2))
 (142 118 (:REWRITE INDEV-DISJOIN-ATOM))
 (138 69 (:REWRITE INDEV-CONJOIN-CLAUSES-ATOM))
 (130 130 (:META CANCEL_PLUS-LESSP-CORRECT))
 (102 89 (:REWRITE DEFAULT-+-1))
 (100 100 (:REWRITE NATP-WHEN-INTEGERP))
 (100 100 (:REWRITE NATP-RW))
 (98 98 (:TYPE-PRESCRIPTION STRIP-CARS))
 (96 16 (:REWRITE PSEUDO-TERM-LISTP-CDR))
 (72 72 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (72 72 (:REWRITE PSEUDO-TERM-LISTP-OF-ATOM))
 (72 56 (:REWRITE PSEUDO-TERMP-OPENER))
 (56 56 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (40 40 (:REWRITE INEQUALITY-WITH-NFIX-HYP-2))
 (25 25 (:TYPE-PRESCRIPTION TRUE-LISTP-APPEND))
 (25 25 (:TYPE-PRESCRIPTION BINARY-APPEND))
 (24 24 (:TYPE-PRESCRIPTION MEASURE-DECRS))
 (24 24 (:TYPE-PRESCRIPTION INDUCTION-STEPS))
 (21 21 (:TYPE-PRESCRIPTION SUBSTITUTE-LIST-INTO-CLAUSE))
 (18 18 (:TYPE-PRESCRIPTION SUBSTITUTE-INTO-LIST))
 (16 8 (:REWRITE DEFAULT-UNARY-MINUS))
 (11 11 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (11 11 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (6 6 (:REWRITE SUBSTITUTE-INTO-LIST-OF-ATOM))
 )
(INDUCTION-CP-CORRECT-REC-WITHOUT-ORIG-CLAUSE
 (800 116 (:REWRITE NFIX-WHEN-NATP))
 (554 116 (:REWRITE NFIX-WHEN-NOT-NATP))
 (529 526 (:REWRITE DEFAULT-CAR))
 (458 382 (:REWRITE INDEV-OF-O<-CALL))
 (458 382 (:REWRITE INDEV-OF-NOT-CALL))
 (458 382 (:REWRITE INDEV-OF-CONS-CALL))
 (458 382 (:REWRITE INDEV-OF-BINARY-+-CALL))
 (455 91 (:DEFINITION LEN))
 (410 164 (:REWRITE NATP-WHEN-GTE-0))
 (350 347 (:REWRITE DEFAULT-CDR))
 (344 344 (:REWRITE INDEV-OF-LAMBDA))
 (344 344 (:REWRITE INDEV-OF-IF-CALL))
 (337 337 (:REWRITE INDEV-OF-VARIABLE))
 (328 328 (:TYPE-PRESCRIPTION NATP))
 (293 13 (:REWRITE ZP-WHEN-GT-0))
 (290 186 (:REWRITE DEFAULT-<-1))
 (278 139 (:REWRITE DEFAULT-+-2))
 (253 186 (:REWRITE DEFAULT-<-2))
 (241 126 (:REWRITE INDEV-DISJOIN-ATOM-NO-BC))
 (212 212 (:META CANCEL_PLUS-LESSP-CORRECT))
 (180 90 (:REWRITE INDEV-CONJOIN-CLAUSES-ATOM))
 (164 164 (:REWRITE NATP-WHEN-INTEGERP))
 (164 164 (:REWRITE NATP-RW))
 (162 139 (:REWRITE DEFAULT-+-1))
 (137 107 (:REWRITE INDEV-DISJOIN-ATOM))
 (121 121 (:TYPE-PRESCRIPTION STRIP-CARS))
 (108 18 (:REWRITE PSEUDO-TERM-LISTP-CDR))
 (84 84 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (84 84 (:REWRITE PSEUDO-TERM-LISTP-OF-ATOM))
 (84 66 (:REWRITE PSEUDO-TERMP-OPENER))
 (76 76 (:REWRITE INEQUALITY-WITH-NFIX-HYP-2))
 (66 66 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (30 30 (:TYPE-PRESCRIPTION SUBSTITUTE-LIST-INTO-CLAUSE))
 (30 30 (:TYPE-PRESCRIPTION MEASURE-DECRS))
 (30 30 (:TYPE-PRESCRIPTION INDUCTION-STEPS))
 (26 13 (:REWRITE DEFAULT-UNARY-MINUS))
 (24 24 (:TYPE-PRESCRIPTION SUBSTITUTE-INTO-LIST))
 (18 18 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (18 18 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (8 8 (:REWRITE SUBSTITUTE-INTO-LIST-OF-ATOM))
 )
(INDUCTION-CP
 (1380 268 (:DEFINITION LEN))
 (1307 1307 (:REWRITE DEFAULT-CDR))
 (1176 1176 (:REWRITE DEFAULT-CAR))
 (996 93 (:REWRITE PSEUDO-TERMP-CADR-FROM-PSEUDO-TERM-LISTP))
 (699 346 (:REWRITE PSEUDO-TERMP-OPENER))
 (662 160 (:DEFINITION TRUE-LISTP))
 (552 276 (:REWRITE DEFAULT-+-2))
 (463 463 (:REWRITE PSEUDO-TERM-LISTP-OF-ATOM))
 (458 458 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (332 332 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (316 316 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (300 65 (:DEFINITION SYMBOL-LISTP))
 (276 276 (:REWRITE DEFAULT-+-1))
 (262 262 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (262 262 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (65 65 (:REWRITE DEFAULT-COERCE-2))
 (65 65 (:REWRITE DEFAULT-COERCE-1))
 (40 8 (:REWRITE EQUAL-CONSTANT-+))
 (24 2 (:DEFINITION INDUCTION-STEPS))
 (14 14 (:REWRITE PSEUDO-TERM-VAL-ALISTP-OF-ATOM))
 (10 2 (:DEFINITION SUBSTITUTE-LIST-INTO-CLAUSE))
 (8 2 (:DEFINITION STRIP-CARS))
 (4 4 (:REWRITE SUBSTITUTE-LIST-INTO-CLAUSE-OF-ATOM))
 (2 2 (:REWRITE SUBSTITUTE-INTO-LIST-OF-ATOM))
 )
(DISJOIN-SINGLETON
 (1 1 (:REWRITE DEFAULT-CDR))
 (1 1 (:REWRITE DEFAULT-CAR))
 )
(INDEV-THEOREM-DISJOIN-CLAUSE
 (2 2 (:REWRITE INDEV-OF-VARIABLE))
 (2 2 (:REWRITE INDEV-OF-QUOTE))
 (2 2 (:REWRITE INDEV-OF-O<-CALL))
 (2 2 (:REWRITE INDEV-OF-O-P-CALL))
 (2 2 (:REWRITE INDEV-OF-NOT-CALL))
 (2 2 (:REWRITE INDEV-OF-LAMBDA))
 (2 2 (:REWRITE INDEV-OF-IF-CALL))
 (2 2 (:REWRITE INDEV-OF-CONS-CALL))
 (2 2 (:REWRITE INDEV-OF-BINARY-+-CALL))
 (2 2 (:REWRITE INDEV-DISJOIN-ATOM-NO-BC))
 (2 2 (:REWRITE INDEV-DISJOIN-ATOM))
 )
(INDEV-THEOREM-DISJOIN-CONS
 (3 3 (:REWRITE INDEV-OF-VARIABLE))
 (3 3 (:REWRITE INDEV-OF-QUOTE))
 (3 3 (:REWRITE INDEV-OF-O<-CALL))
 (3 3 (:REWRITE INDEV-OF-O-P-CALL))
 (3 3 (:REWRITE INDEV-OF-NOT-CALL))
 (3 3 (:REWRITE INDEV-OF-LAMBDA))
 (3 3 (:REWRITE INDEV-OF-IF-CALL))
 (3 3 (:REWRITE INDEV-OF-CONS-CALL))
 (3 3 (:REWRITE INDEV-OF-BINARY-+-CALL))
 (3 3 (:REWRITE INDEV-DISJOIN-ATOM-NO-BC))
 (2 2 (:REWRITE INDEV-DISJOIN-ATOM))
 )
(INDUCTION-CP-CORRECT
 (2016 96 (:DEFINITION INDUCTION-STEP-LISTP))
 (1740 1670 (:REWRITE INDEV-OF-O<-CALL))
 (1740 1670 (:REWRITE INDEV-OF-NOT-CALL))
 (1740 1670 (:REWRITE INDEV-OF-LAMBDA))
 (1740 1670 (:REWRITE INDEV-OF-IF-CALL))
 (1740 1670 (:REWRITE INDEV-OF-CONS-CALL))
 (1740 1670 (:REWRITE INDEV-OF-BINARY-+-CALL))
 (1684 421 (:DEFINITION STRIP-CARS))
 (1030 209 (:REWRITE INDEV-CONJOIN-CLAUSES-ATOM))
 (1003 231 (:REWRITE PSEUDO-TERMP-CAR))
 (980 703 (:REWRITE INDEV-DISJOIN-ATOM-NO-BC))
 (874 703 (:REWRITE INDEV-DISJOIN-ATOM))
 (630 210 (:DEFINITION ALISTP))
 (526 254 (:TYPE-PRESCRIPTION TRUE-LISTP-APPEND))
 (480 96 (:DEFINITION PSEUDO-TERM-ALIST-LISTP))
 (427 427 (:TYPE-PRESCRIPTION INDUCTION-STEPS))
 (409 409 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (409 409 (:REWRITE PSEUDO-TERM-LISTP-OF-ATOM))
 (254 254 (:TYPE-PRESCRIPTION BINARY-APPEND))
 (231 231 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (231 231 (:REWRITE PSEUDO-TERMP-OPENER))
 (226 226 (:TYPE-PRESCRIPTION MEASURE-DECRS))
 (212 212 (:TYPE-PRESCRIPTION STRIP-CARS))
 (210 210 (:REWRITE CAR-CONS))
 (96 96 (:TYPE-PRESCRIPTION PSEUDO-TERM-VAL-ALISTP))
 (96 96 (:TYPE-PRESCRIPTION PSEUDO-TERM-ALIST-LISTP))
 (96 96 (:REWRITE PSEUDO-TERM-VAL-ALISTP-OF-ATOM))
 (82 82 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (82 82 (:META CANCEL_PLUS-EQUAL-CORRECT))
 )
(FIB
 (8 2 (:REWRITE ZP-WHEN-GT-0))
 (6 6 (:REWRITE DEFAULT-<-2))
 (6 6 (:REWRITE DEFAULT-<-1))
 (2 2 (:REWRITE ZP-WHEN-INTEGERP))
 (2 2 (:REWRITE ZP-OPEN))
 (2 2 (:REWRITE DEFAULT-+-2))
 (2 2 (:REWRITE DEFAULT-+-1))
 (2 2 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (2 2 (:META CANCEL_PLUS-EQUAL-CORRECT))
 )
(FIB-OF-X+2
 (37 28 (:REWRITE DEFAULT-+-2))
 (37 28 (:REWRITE DEFAULT-+-1))
 (10 6 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (10 2 (:REWRITE ZP-WHEN-INTEGERP))
 (8 2 (:REWRITE ZP-WHEN-GT-0))
 (6 6 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (5 5 (:REWRITE DEFAULT-<-2))
 (5 5 (:REWRITE DEFAULT-<-1))
 (5 5 (:META CANCEL_PLUS-LESSP-CORRECT))
 (4 1 (:REWRITE NATP-WHEN-GTE-0))
 (1 1 (:REWRITE NATP-WHEN-INTEGERP))
 (1 1 (:REWRITE NATP-RW))
 )
(FIB-OF-0-AND-1)
(FIB-POSITIVE
 (45 31 (:REWRITE DEFAULT-<-2))
 (35 8 (:REWRITE NFIX-WHEN-NOT-NATP))
 (31 31 (:REWRITE DEFAULT-<-1))
 (20 10 (:REWRITE NATP-WHEN-INTEGERP))
 (18 17 (:REWRITE DEFAULT-+-2))
 (17 17 (:REWRITE DEFAULT-+-1))
 (14 14 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (9 9 (:REWRITE NATP-RW))
 (4 1 (:REWRITE <-+-NEGATIVE-0-1))
 (1 1 (:REWRITE EQUAL-CONSTANT-+))
 (1 1 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (1 1 (:META CANCEL_PLUS-EQUAL-CORRECT))
 )
