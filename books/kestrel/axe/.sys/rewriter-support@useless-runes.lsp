(LEN-OF-CADAR-WHEN-PSEUDO-TERMP
 (361 32 (:REWRITE CONSP-FROM-LEN-CHEAP))
 (139 3 (:DEFINITION SYMBOL-LISTP))
 (107 55 (:REWRITE DEFAULT-CAR))
 (101 5 (:REWRITE USE-ALL-CONSP-FOR-CAR))
 (89 52 (:REWRITE DEFAULT-CDR))
 (78 78 (:REWRITE LEN-WHEN-DARGP-LESS-THAN))
 (62 6 (:REWRITE <-OF-+-ARG2-WHEN-NEGATIVE-CONSTANT))
 (61 10 (:REWRITE ALL-CONSP-WHEN-NOT-CONSP))
 (58 21 (:LINEAR LEN-POSITIVE-WHEN-CONSP-LINEAR-CHEAP))
 (43 1 (:DEFINITION PSEUDO-TERM-LISTP))
 (35 5 (:REWRITE ALL-CONSP-OF-CDR))
 (31 16 (:REWRITE DEFAULT-+-2))
 (26 14 (:REWRITE DEFAULT-<-2))
 (20 20 (:TYPE-PRESCRIPTION ALL-CONSP))
 (16 16 (:REWRITE DEFAULT-+-1))
 (15 15 (:REWRITE USE-ALL-CONSP-2))
 (15 15 (:REWRITE USE-ALL-CONSP))
 (15 15 (:REWRITE CONSP-WHEN-LEN-GREATER))
 (14 14 (:REWRITE DEFAULT-<-1))
 (14 14 (:REWRITE <-WHEN-BOUNDED-AXE-TREEP))
 (10 10 (:REWRITE ALL-CONSP-WHEN-NOT-CONSP-CHEAP))
 (10 5 (:REWRITE SYMBOLP-OF-CAR-WHEN-AXE-TREEP-CHEAP))
 (10 5 (:REWRITE CONSP-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (8 1 (:LINEAR LEN-OF-CDR-LINEAR-STRONG))
 (7 7 (:REWRITE SYMBOLP-WHEN-BOUNDED-DAG-EXPRP))
 (6 6 (:REWRITE EQUAL-OF-+-COMBINE-CONSTANTS))
 (6 6 (:REWRITE CONSP-OF-CDR-WHEN-LEN-KNOWN))
 (5 5 (:TYPE-PRESCRIPTION SYMBOL-TERM-ALISTP))
 (5 5 (:TYPE-PRESCRIPTION AXE-TREEP))
 (5 5 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (5 5 (:REWRITE SYMBOLP-OF-CAR-WHEN-BOUNDED-DAG-EXPRP))
 (4 4 (:REWRITE TRUE-LISTP-OF-CAR-WHEN-BOUNDED-DARG-LISTP))
 (4 4 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (4 4 (:REWRITE LEN-OF-CDDR-WHEN-EQUAL-OF-LEN))
 (3 3 (:REWRITE DEFAULT-COERCE-2))
 (3 3 (:REWRITE DEFAULT-COERCE-1))
 )
(LEN-OF-CADAR-WHEN-AXE-TREEP
 (10830 6 (:DEFINITION AXE-TREE-LISTP))
 (10021 35 (:DEFINITION PSEUDO-TERMP))
 (9243 21 (:REWRITE AXE-TREE-LISTP-OF-CDR-2))
 (8508 21 (:REWRITE AXE-TREE-LISTP-OF-CDR))
 (5254 19 (:REWRITE AXE-TREEP-WHEN-PSEUDO-TERMP))
 (4383 403 (:REWRITE CONSP-FROM-LEN-CHEAP))
 (2217 45 (:DEFINITION SYMBOL-LISTP))
 (2141 27 (:REWRITE AXE-TREE-LISTP-WHEN-PSEUDO-TERM-LISTP))
 (2057 27 (:DEFINITION PSEUDO-TERM-LISTP))
 (1561 98 (:REWRITE USE-ALL-CONSP-FOR-CAR))
 (1478 9 (:REWRITE AXE-TREEP-OF-CAR))
 (1282 734 (:REWRITE DEFAULT-CAR))
 (1113 725 (:REWRITE DEFAULT-CDR))
 (1028 345 (:LINEAR LEN-POSITIVE-WHEN-CONSP-LINEAR-CHEAP))
 (1004 1004 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
 (1003 1003 (:REWRITE LEN-WHEN-DARGP-LESS-THAN))
 (941 19 (:REWRITE AXE-TREEP-WHEN-DARGP))
 (866 173 (:REWRITE ALL-CONSP-WHEN-NOT-CONSP))
 (764 105 (:DEFINITION LENGTH))
 (764 27 (:REWRITE AXE-TREE-LISTP-WHEN-ALL-DARGP))
 (595 17 (:DEFINITION MYQUOTEP))
 (578 66 (:REWRITE <-OF-+-ARG2-WHEN-NEGATIVE-CONSTANT))
 (495 51 (:REWRITE ALL-DARGP-WHEN-NOT-CONSP))
 (492 78 (:REWRITE ALL-CONSP-OF-CDR))
 (444 6 (:DEFINITION DARGP))
 (360 194 (:REWRITE DEFAULT-+-2))
 (346 346 (:TYPE-PRESCRIPTION ALL-CONSP))
 (340 340 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (332 185 (:REWRITE DEFAULT-<-2))
 (271 17 (:REWRITE DARGP-WHEN-CONSP-CHEAP))
 (218 218 (:TYPE-PRESCRIPTION PSEUDO-TERM-LISTP))
 (197 197 (:REWRITE USE-ALL-CONSP-2))
 (197 197 (:REWRITE USE-ALL-CONSP))
 (197 197 (:REWRITE CONSP-WHEN-LEN-GREATER))
 (196 98 (:REWRITE CONSP-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (194 194 (:REWRITE DEFAULT-+-1))
 (190 17 (:DEFINITION QUOTEP))
 (185 185 (:REWRITE DEFAULT-<-1))
 (185 185 (:REWRITE <-WHEN-BOUNDED-AXE-TREEP))
 (180 90 (:REWRITE SYMBOLP-OF-CAR-WHEN-AXE-TREEP-CHEAP))
 (173 173 (:REWRITE ALL-CONSP-WHEN-NOT-CONSP-CHEAP))
 (172 25 (:REWRITE ALL-DARGP-OF-CDR))
 (102 102 (:TYPE-PRESCRIPTION ALL-DARGP))
 (102 51 (:REWRITE ALL-DARGP-WHEN-ALL-MYQUOTEP-CHEAP))
 (100 100 (:TYPE-PRESCRIPTION SYMBOL-TERM-ALISTP))
 (98 9 (:REWRITE USE-ALL-DARGP-FOR-CAR))
 (97 97 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (93 93 (:REWRITE SYMBOLP-WHEN-BOUNDED-DAG-EXPRP))
 (93 93 (:REWRITE CONSP-OF-CDR-WHEN-LEN-KNOWN))
 (90 90 (:REWRITE SYMBOLP-OF-CAR-WHEN-BOUNDED-DAG-EXPRP))
 (89 89 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (82 82 (:REWRITE EQUAL-OF-+-COMBINE-CONSTANTS))
 (69 69 (:REWRITE LEN-OF-CDDR-WHEN-EQUAL-OF-LEN))
 (67 67 (:REWRITE TRUE-LISTP-OF-CAR-WHEN-BOUNDED-DARG-LISTP))
 (52 14 (:REWRITE +-COMBINE-CONSTANTS))
 (51 51 (:TYPE-PRESCRIPTION ALL-MYQUOTEP))
 (51 51 (:REWRITE ALL-DARGP-WHEN-NOT-CONSP-CHEAP))
 (51 51 (:REWRITE ALL-DARGP-WHEN-BOUNDED-DARG-LISTP))
 (35 35 (:REWRITE DEFAULT-COERCE-2))
 (35 35 (:REWRITE DEFAULT-COERCE-1))
 (19 19 (:REWRITE AXE-TREEP-WHEN-SYMBOLP-CHEAP))
 (19 19 (:REWRITE AXE-TREEP-WHEN-NOT-CONSP-AND-NOT-SYMBOLP-CHEAP))
 (19 19 (:REWRITE AXE-TREEP-WHEN-EQUAL-OF-CAR-AND-QUOTE-CHEAP))
 (19 19 (:REWRITE AXE-TREEP-WHEN-BOUNDED-AXE-TREEP))
 (17 17 (:TYPE-PRESCRIPTION DARGP))
 (17 17 (:REWRITE USE-ALL-DARGP-2))
 (17 17 (:REWRITE USE-ALL-DARGP))
 (17 17 (:REWRITE MYQUOTEP-WHEN-DARGP-LESS-THAN))
 (17 17 (:REWRITE MYQUOTEP-WHEN-BOUNDED-DAG-EXPRP))
 (17 17 (:REWRITE MYQUOTEP-WHEN-AXE-TREEP))
 (17 17 (:REWRITE DARGP-WHEN-EQUAL-OF-QUOTE-AND-CAR-CHEAP))
 (17 17 (:REWRITE DARGP-WHEN-DARGP-LESS-THAN))
 (12 6 (:REWRITE DARGP-WHEN-NATP-CHEAP))
 (12 6 (:REWRITE DARGP-WHEN-MYQUOTEP-CHEAP))
 (9 9 (:REWRITE AXE-TREEP-OF-CAR-WHEN-BOUNDED-AXE-TREE-LISTP))
 (8 8 (:REWRITE NONNEG-WHEN-DARGP-LESS-THAN))
 (8 8 (:REWRITE INTEGERP-WHEN-DARGP-LESS-THAN))
 (8 1 (:LINEAR LEN-OF-CDR-LINEAR-STRONG))
 (6 6 (:TYPE-PRESCRIPTION NATP))
 (6 6 (:TYPE-PRESCRIPTION MYQUOTEP))
 (5 5 (:REWRITE NOT-<-OF-CAR-WHEN-BOUNDED-DARG-LISTP-2))
 (5 5 (:REWRITE INTEGERP-OF-CAR-WHEN-BOUNDED-DARG-LISTP))
 (3 1 (:REWRITE PSEUDO-TERMP-OF-CDR-OF-CAR-WHEN-SYMBOL-TERM-ALISTP))
 )
(PSEUDO-TERMP-OF-CADDDR-WHEN-AXE-TREEP
 (842 2 (:REWRITE AXE-TREE-LISTP-OF-CDR))
 (633 57 (:REWRITE CONSP-FROM-LEN-CHEAP))
 (439 2 (:REWRITE AXE-TREEP-WHEN-PSEUDO-TERMP))
 (290 6 (:DEFINITION SYMBOL-LISTP))
 (202 10 (:REWRITE USE-ALL-CONSP-FOR-CAR))
 (164 92 (:REWRITE DEFAULT-CAR))
 (141 93 (:REWRITE DEFAULT-CDR))
 (125 125 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
 (125 125 (:REWRITE LEN-WHEN-DARGP-LESS-THAN))
 (122 20 (:REWRITE ALL-CONSP-WHEN-NOT-CONSP))
 (79 11 (:REWRITE <-OF-+-ARG2-WHEN-NEGATIVE-CONSTANT))
 (70 10 (:REWRITE ALL-CONSP-OF-CDR))
 (67 25 (:LINEAR LEN-POSITIVE-WHEN-CONSP-LINEAR-CHEAP))
 (63 3 (:REWRITE AXE-TREE-LISTP-WHEN-ALL-DARGP))
 (57 57 (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT))
 (53 2 (:REWRITE AXE-TREEP-WHEN-DARGP))
 (50 34 (:REWRITE DEFAULT-<-2))
 (46 46 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (41 3 (:REWRITE ALL-DARGP-WHEN-NOT-CONSP))
 (40 40 (:TYPE-PRESCRIPTION ALL-CONSP))
 (37 3 (:REWRITE AXE-TREE-LISTP-WHEN-PSEUDO-TERM-LISTP))
 (36 27 (:REWRITE DEFAULT-+-2))
 (34 34 (:REWRITE DEFAULT-<-1))
 (34 34 (:REWRITE <-WHEN-BOUNDED-AXE-TREEP))
 (29 29 (:REWRITE USE-ALL-CONSP-2))
 (29 29 (:REWRITE USE-ALL-CONSP))
 (29 29 (:REWRITE CONSP-WHEN-LEN-GREATER))
 (29 1 (:DEFINITION DARGP))
 (28 2 (:REWRITE AXE-TREE-LISTP-OF-CDR-2))
 (28 2 (:DEFINITION PSEUDO-TERM-LISTP))
 (27 27 (:REWRITE DEFAULT-+-1))
 (22 2 (:DEFINITION MYQUOTEP))
 (20 20 (:REWRITE ALL-CONSP-WHEN-NOT-CONSP-CHEAP))
 (20 10 (:REWRITE SYMBOLP-OF-CAR-WHEN-AXE-TREEP-CHEAP))
 (20 10 (:REWRITE CONSP-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (20 2 (:DEFINITION QUOTEP))
 (16 16 (:REWRITE CONSP-OF-CDR-WHEN-LEN-KNOWN))
 (15 15 (:REWRITE TRUE-LISTP-OF-CAR-WHEN-BOUNDED-DARG-LISTP))
 (12 12 (:REWRITE SYMBOLP-WHEN-BOUNDED-DAG-EXPRP))
 (12 12 (:REWRITE LEN-OF-CDDR-WHEN-EQUAL-OF-LEN))
 (12 4 (:REWRITE +-COMBINE-CONSTANTS))
 (10 10 (:TYPE-PRESCRIPTION SYMBOL-TERM-ALISTP))
 (10 10 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (10 10 (:REWRITE SYMBOLP-OF-CAR-WHEN-BOUNDED-DAG-EXPRP))
 (8 8 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (8 2 (:REWRITE DARGP-WHEN-CONSP-CHEAP))
 (8 1 (:REWRITE ALL-DARGP-OF-CDR))
 (6 6 (:TYPE-PRESCRIPTION ALL-DARGP))
 (6 3 (:REWRITE ALL-DARGP-WHEN-ALL-MYQUOTEP-CHEAP))
 (4 4 (:REWRITE EQUAL-OF-+-COMBINE-CONSTANTS))
 (3 3 (:TYPE-PRESCRIPTION ALL-MYQUOTEP))
 (3 3 (:REWRITE ALL-DARGP-WHEN-NOT-CONSP-CHEAP))
 (3 3 (:REWRITE ALL-DARGP-WHEN-BOUNDED-DARG-LISTP))
 (2 2 (:TYPE-PRESCRIPTION DARGP))
 (2 2 (:REWRITE USE-ALL-DARGP-2))
 (2 2 (:REWRITE USE-ALL-DARGP))
 (2 2 (:REWRITE NONNEG-WHEN-DARGP-LESS-THAN))
 (2 2 (:REWRITE MYQUOTEP-WHEN-DARGP-LESS-THAN))
 (2 2 (:REWRITE MYQUOTEP-WHEN-BOUNDED-DAG-EXPRP))
 (2 2 (:REWRITE MYQUOTEP-WHEN-AXE-TREEP))
 (2 2 (:REWRITE INTEGERP-WHEN-DARGP-LESS-THAN))
 (2 2 (:REWRITE DEFAULT-COERCE-2))
 (2 2 (:REWRITE DEFAULT-COERCE-1))
 (2 2 (:REWRITE DARGP-WHEN-EQUAL-OF-QUOTE-AND-CAR-CHEAP))
 (2 2 (:REWRITE DARGP-WHEN-DARGP-LESS-THAN))
 (2 2 (:REWRITE AXE-TREEP-WHEN-SYMBOLP-CHEAP))
 (2 2 (:REWRITE AXE-TREEP-WHEN-NOT-CONSP-AND-NOT-SYMBOLP-CHEAP))
 (2 2 (:REWRITE AXE-TREEP-WHEN-EQUAL-OF-CAR-AND-QUOTE-CHEAP))
 (2 2 (:REWRITE AXE-TREEP-WHEN-BOUNDED-AXE-TREEP))
 (2 1 (:REWRITE DARGP-WHEN-NATP-CHEAP))
 (2 1 (:REWRITE DARGP-WHEN-MYQUOTEP-CHEAP))
 (1 1 (:TYPE-PRESCRIPTION NATP))
 (1 1 (:TYPE-PRESCRIPTION MYQUOTEP))
 )
(ALL-DARGP-OF-IF)
(BOUNDED-DARG-LISTP-OF-IF)
(AXE-TREE-LISTP-WHEN-BOUNDED-DARG-LISTP
 (166 1 (:DEFINITION BOUNDED-DARG-LISTP))
 (98 5 (:REWRITE CONSP-FROM-LEN-CHEAP))
 (83 1 (:DEFINITION DARGP-LESS-THAN))
 (66 1 (:DEFINITION MYQUOTEP))
 (52 4 (:REWRITE BOUNDED-DARG-LISTP-WHEN-NOT-CONSP))
 (40 40 (:TYPE-PRESCRIPTION LEN))
 (26 7 (:LINEAR LEN-POSITIVE-WHEN-CONSP-LINEAR-CHEAP))
 (26 2 (:REWRITE <-OF-+-ARG2-WHEN-NEGATIVE-CONSTANT))
 (25 1 (:DEFINITION QUOTEP))
 (20 2 (:REWRITE LEN-OF-CDR))
 (12 12 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
 (12 12 (:REWRITE LEN-WHEN-DARGP-LESS-THAN))
 (11 6 (:REWRITE DEFAULT-<-2))
 (8 4 (:REWRITE BOUNDED-DARG-LISTP-WHEN-ALL-MYQUOTEP-CHEAP))
 (8 1 (:REWRITE DARGP-LESS-THAN-OF-CAR-WHEN-BOUNDED-DARG-LISTP))
 (8 1 (:REWRITE BOUNDED-DARG-LISTP-OF-CDR))
 (8 1 (:DEFINITION NATP))
 (6 6 (:REWRITE DEFAULT-<-1))
 (6 6 (:REWRITE <-WHEN-BOUNDED-AXE-TREEP))
 (5 5 (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT))
 (5 1 (:REWRITE USE-ALL-CONSP-FOR-CAR))
 (4 4 (:TYPE-PRESCRIPTION ALL-MYQUOTEP))
 (4 4 (:REWRITE USE-ALL-CONSP-2))
 (4 4 (:REWRITE USE-ALL-CONSP))
 (4 4 (:REWRITE DEFAULT-CDR))
 (4 4 (:REWRITE CONSP-WHEN-LEN-GREATER))
 (4 4 (:REWRITE BOUNDED-DARG-LISTP-MONOTONE))
 (4 2 (:REWRITE DEFAULT-+-2))
 (2 2 (:TYPE-PRESCRIPTION ALL-CONSP))
 (2 2 (:REWRITE NOT-<-OF-CAR-WHEN-BOUNDED-DARG-LISTP-2))
 (2 2 (:REWRITE EQUAL-OF-LEN-AND-0))
 (2 2 (:REWRITE DEFAULT-CAR))
 (2 2 (:REWRITE DEFAULT-+-1))
 (2 2 (:REWRITE CONSP-OF-CDR-WHEN-LEN-KNOWN))
 (2 1 (:REWRITE DARGP-LESS-THAN-WHEN-NATP-CHEAP))
 (2 1 (:REWRITE CONSP-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (1 1 (:TYPE-PRESCRIPTION SYMBOL-TERM-ALISTP))
 (1 1 (:TYPE-PRESCRIPTION NATP))
 (1 1 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (1 1 (:REWRITE NONNEG-WHEN-DARGP-LESS-THAN))
 (1 1 (:REWRITE MYQUOTEP-WHEN-DARGP-LESS-THAN))
 (1 1 (:REWRITE MYQUOTEP-WHEN-BOUNDED-DAG-EXPRP))
 (1 1 (:REWRITE MYQUOTEP-WHEN-AXE-TREEP))
 (1 1 (:REWRITE INTEGERP-WHEN-DARGP-LESS-THAN))
 (1 1 (:REWRITE INTEGERP-OF-CAR-WHEN-BOUNDED-DARG-LISTP))
 (1 1 (:REWRITE DARGP-LESS-THAN-WHEN-QUOTEP-CHEAP))
 (1 1 (:REWRITE DARGP-LESS-THAN-WHEN-NOT-CONSP-CHEAP))
 (1 1 (:REWRITE DARGP-LESS-THAN-WHEN-EQUAL-OF-CAR-AND-QUOTE))
 (1 1 (:REWRITE DARGP-LESS-THAN-WHEN-CONSP-CHEAP))
 (1 1 (:REWRITE DARGP-LESS-THAN-MONO))
 (1 1 (:REWRITE ALL-CONSP-WHEN-NOT-CONSP-CHEAP))
 (1 1 (:REWRITE ALL-CONSP-WHEN-NOT-CONSP))
 )
(DARGP-LESS-THAN-WHEN-NOT-QUOTEP-CHEAP
 (24 2 (:REWRITE CONSP-FROM-LEN-CHEAP))
 (16 10 (:REWRITE DEFAULT-<-2))
 (10 10 (:TYPE-PRESCRIPTION LEN))
 (10 10 (:REWRITE DEFAULT-<-1))
 (10 10 (:REWRITE <-WHEN-BOUNDED-AXE-TREEP))
 (4 4 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (4 4 (:REWRITE NONNEG-WHEN-DARGP-LESS-THAN))
 (4 4 (:REWRITE INTEGERP-WHEN-DARGP-LESS-THAN))
 (4 2 (:REWRITE DARGP-LESS-THAN-WHEN-NATP-CHEAP))
 (2 2 (:TYPE-PRESCRIPTION NATP))
 (2 2 (:REWRITE USE-ALL-CONSP-2))
 (2 2 (:REWRITE USE-ALL-CONSP))
 (2 2 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
 (2 2 (:REWRITE LEN-WHEN-DARGP-LESS-THAN))
 (2 2 (:REWRITE DEFAULT-CAR))
 (2 2 (:REWRITE DARGP-LESS-THAN-WHEN-QUOTEP-CHEAP))
 (2 2 (:REWRITE DARGP-LESS-THAN-WHEN-EQUAL-OF-CAR-AND-QUOTE))
 (2 2 (:REWRITE DARGP-LESS-THAN-MONO))
 (2 2 (:REWRITE CONSP-WHEN-LEN-GREATER))
 (2 2 (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT))
 (2 2 (:LINEAR LEN-POSITIVE-WHEN-CONSP-LINEAR-CHEAP))
 (1 1 (:REWRITE MYQUOTEP-WHEN-DARGP-LESS-THAN))
 (1 1 (:REWRITE MYQUOTEP-WHEN-BOUNDED-DAG-EXPRP))
 (1 1 (:REWRITE MYQUOTEP-WHEN-AXE-TREEP))
 (1 1 (:REWRITE DARGP-LESS-THAN-WHEN-CONSP-CHEAP))
 )
(SYMBOL-ALISTP-WHEN-ALISTP
 (240 20 (:REWRITE CONSP-FROM-LEN-CHEAP))
 (46 23 (:REWRITE DEFAULT-CAR))
 (36 18 (:REWRITE DEFAULT-<-2))
 (33 20 (:LINEAR LEN-POSITIVE-WHEN-CONSP-LINEAR-CHEAP))
 (30 6 (:REWRITE USE-ALL-CONSP-FOR-CAR))
 (27 24 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
 (24 24 (:REWRITE LEN-WHEN-DARGP-LESS-THAN))
 (20 20 (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT))
 (18 18 (:REWRITE USE-ALL-CONSP-2))
 (18 18 (:REWRITE USE-ALL-CONSP))
 (18 18 (:REWRITE DEFAULT-<-1))
 (18 18 (:REWRITE CONSP-WHEN-LEN-GREATER))
 (18 18 (:REWRITE <-WHEN-BOUNDED-AXE-TREEP))
 (17 7 (:REWRITE SYMBOLP-OF-CAR-WHEN-AXE-TREEP-CHEAP))
 (12 12 (:TYPE-PRESCRIPTION ALL-CONSP))
 (12 6 (:REWRITE CONSP-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (11 11 (:TYPE-PRESCRIPTION SYMBOL-TERM-ALISTP))
 (11 10 (:REWRITE DEFAULT-CDR))
 (10 5 (:REWRITE SYMBOL-ALISTP-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (7 7 (:TYPE-PRESCRIPTION AXE-TREEP))
 (7 7 (:REWRITE SYMBOLP-WHEN-BOUNDED-DAG-EXPRP))
 (7 7 (:REWRITE SYMBOLP-OF-CAR-WHEN-BOUNDED-DAG-EXPRP))
 (6 6 (:REWRITE ALL-CONSP-WHEN-NOT-CONSP-CHEAP))
 (6 6 (:REWRITE ALL-CONSP-WHEN-NOT-CONSP))
 )
(LEN-WHEN-AXE-TREEP-AND-CONSP-OF-CAR
 (75 2 (:REWRITE AXE-TREEP-WHEN-PSEUDO-TERMP))
 (69 5 (:REWRITE CONSP-FROM-LEN-CHEAP))
 (69 2 (:DEFINITION PSEUDO-TERMP))
 (62 2 (:REWRITE AXE-TREE-LISTP-WHEN-ALL-DARGP))
 (53 2 (:REWRITE AXE-TREEP-WHEN-DARGP))
 (50 1 (:REWRITE AXE-TREE-LISTP-OF-CDR))
 (41 3 (:REWRITE ALL-DARGP-WHEN-NOT-CONSP))
 (36 2 (:REWRITE AXE-TREE-LISTP-WHEN-PSEUDO-TERM-LISTP))
 (29 1 (:DEFINITION DARGP))
 (28 2 (:DEFINITION PSEUDO-TERM-LISTP))
 (28 1 (:REWRITE AXE-TREE-LISTP-OF-CDR-2))
 (22 5 (:DEFINITION TRUE-LISTP))
 (22 2 (:DEFINITION MYQUOTEP))
 (20 2 (:DEFINITION QUOTEP))
 (16 16 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (16 16 (:TYPE-PRESCRIPTION PSEUDO-TERM-LISTP))
 (16 6 (:LINEAR LEN-POSITIVE-WHEN-CONSP-LINEAR-CHEAP))
 (13 13 (:REWRITE DEFAULT-CAR))
 (13 1 (:REWRITE <-OF-+-ARG2-WHEN-NEGATIVE-CONSTANT))
 (11 11 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
 (11 11 (:REWRITE LEN-WHEN-DARGP-LESS-THAN))
 (11 11 (:REWRITE DEFAULT-CDR))
 (10 6 (:REWRITE DEFAULT-<-2))
 (10 1 (:REWRITE LEN-OF-CDR))
 (8 8 (:TYPE-PRESCRIPTION PSEUDO-TERMP))
 (8 2 (:REWRITE DARGP-WHEN-CONSP-CHEAP))
 (8 1 (:REWRITE ALL-DARGP-OF-CDR))
 (6 6 (:TYPE-PRESCRIPTION ALL-DARGP))
 (6 6 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (6 6 (:REWRITE DEFAULT-<-1))
 (6 6 (:REWRITE <-WHEN-BOUNDED-AXE-TREEP))
 (6 3 (:REWRITE ALL-DARGP-WHEN-ALL-MYQUOTEP-CHEAP))
 (6 2 (:DEFINITION LENGTH))
 (5 5 (:REWRITE USE-ALL-CONSP-2))
 (5 5 (:REWRITE USE-ALL-CONSP))
 (5 5 (:REWRITE CONSP-WHEN-LEN-GREATER))
 (5 5 (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT))
 (4 4 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (3 3 (:TYPE-PRESCRIPTION ALL-MYQUOTEP))
 (3 3 (:REWRITE TRUE-LISTP-OF-CAR-WHEN-BOUNDED-DARG-LISTP))
 (3 3 (:REWRITE ALL-DARGP-WHEN-NOT-CONSP-CHEAP))
 (3 3 (:REWRITE ALL-DARGP-WHEN-BOUNDED-DARG-LISTP))
 (2 2 (:TYPE-PRESCRIPTION DARGP))
 (2 2 (:REWRITE USE-ALL-DARGP-2))
 (2 2 (:REWRITE USE-ALL-DARGP))
 (2 2 (:REWRITE SYMBOLP-WHEN-BOUNDED-DAG-EXPRP))
 (2 2 (:REWRITE NONNEG-WHEN-DARGP-LESS-THAN))
 (2 2 (:REWRITE MYQUOTEP-WHEN-DARGP-LESS-THAN))
 (2 2 (:REWRITE MYQUOTEP-WHEN-BOUNDED-DAG-EXPRP))
 (2 2 (:REWRITE MYQUOTEP-WHEN-AXE-TREEP))
 (2 2 (:REWRITE INTEGERP-WHEN-DARGP-LESS-THAN))
 (2 2 (:REWRITE DARGP-WHEN-EQUAL-OF-QUOTE-AND-CAR-CHEAP))
 (2 2 (:REWRITE DARGP-WHEN-DARGP-LESS-THAN))
 (2 2 (:REWRITE CONSP-OF-CDR-WHEN-LEN-KNOWN))
 (2 2 (:REWRITE AXE-TREEP-WHEN-SYMBOLP-CHEAP))
 (2 2 (:REWRITE AXE-TREEP-WHEN-NOT-CONSP-AND-NOT-SYMBOLP-CHEAP))
 (2 2 (:REWRITE AXE-TREEP-WHEN-EQUAL-OF-CAR-AND-QUOTE-CHEAP))
 (2 2 (:REWRITE AXE-TREEP-WHEN-BOUNDED-AXE-TREEP))
 (2 2 (:REWRITE AXE-TREE-LISTP-WHEN-BOUNDED-DARG-LISTP))
 (2 1 (:REWRITE DEFAULT-+-2))
 (2 1 (:REWRITE DARGP-WHEN-NATP-CHEAP))
 (2 1 (:REWRITE DARGP-WHEN-MYQUOTEP-CHEAP))
 (1 1 (:TYPE-PRESCRIPTION NATP))
 (1 1 (:TYPE-PRESCRIPTION MYQUOTEP))
 (1 1 (:REWRITE EQUAL-OF-LEN-AND-0))
 (1 1 (:REWRITE DEFAULT-+-1))
 )
(NATP-WHEN-DARGP
 (44 2 (:REWRITE CONSP-FROM-LEN-CHEAP))
 (18 18 (:TYPE-PRESCRIPTION LEN))
 (13 1 (:REWRITE <-OF-+-ARG2-WHEN-NEGATIVE-CONSTANT))
 (11 3 (:LINEAR LEN-POSITIVE-WHEN-CONSP-LINEAR-CHEAP))
 (10 1 (:REWRITE LEN-OF-CDR))
 (5 5 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
 (5 5 (:REWRITE LEN-WHEN-DARGP-LESS-THAN))
 (5 3 (:REWRITE DEFAULT-<-2))
 (3 3 (:REWRITE DEFAULT-CDR))
 (3 3 (:REWRITE DEFAULT-<-1))
 (3 3 (:REWRITE <-WHEN-BOUNDED-AXE-TREEP))
 (2 2 (:REWRITE USE-ALL-CONSP-2))
 (2 2 (:REWRITE USE-ALL-CONSP))
 (2 2 (:REWRITE CONSP-WHEN-LEN-GREATER))
 (2 2 (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT))
 (2 1 (:REWRITE DEFAULT-+-2))
 (2 1 (:REWRITE DARGP-WHEN-NATP-CHEAP))
 (2 1 (:REWRITE DARGP-WHEN-MYQUOTEP-CHEAP))
 (1 1 (:TYPE-PRESCRIPTION MYQUOTEP))
 (1 1 (:REWRITE USE-ALL-DARGP-2))
 (1 1 (:REWRITE USE-ALL-DARGP))
 (1 1 (:REWRITE NONNEG-WHEN-DARGP-LESS-THAN))
 (1 1 (:REWRITE MYQUOTEP-WHEN-DARGP-LESS-THAN))
 (1 1 (:REWRITE MYQUOTEP-WHEN-BOUNDED-DAG-EXPRP))
 (1 1 (:REWRITE MYQUOTEP-WHEN-AXE-TREEP))
 (1 1 (:REWRITE INTEGERP-WHEN-DARGP-LESS-THAN))
 (1 1 (:REWRITE EQUAL-OF-LEN-AND-0))
 (1 1 (:REWRITE DEFAULT-CAR))
 (1 1 (:REWRITE DEFAULT-+-1))
 (1 1 (:REWRITE DARGP-WHEN-EQUAL-OF-QUOTE-AND-CAR-CHEAP))
 (1 1 (:REWRITE DARGP-WHEN-DARGP-LESS-THAN))
 (1 1 (:REWRITE DARGP-WHEN-CONSP-CHEAP))
 (1 1 (:REWRITE CONSP-OF-CDR-WHEN-LEN-KNOWN))
 )
(QUOTEP-WHEN-DARGP
 (44 2 (:REWRITE CONSP-FROM-LEN-CHEAP))
 (18 18 (:TYPE-PRESCRIPTION LEN))
 (13 1 (:REWRITE <-OF-+-ARG2-WHEN-NEGATIVE-CONSTANT))
 (11 3 (:LINEAR LEN-POSITIVE-WHEN-CONSP-LINEAR-CHEAP))
 (10 1 (:REWRITE LEN-OF-CDR))
 (5 5 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
 (5 5 (:REWRITE LEN-WHEN-DARGP-LESS-THAN))
 (5 3 (:REWRITE DEFAULT-<-2))
 (3 3 (:REWRITE DEFAULT-CDR))
 (3 3 (:REWRITE DEFAULT-<-1))
 (3 3 (:REWRITE <-WHEN-BOUNDED-AXE-TREEP))
 (2 2 (:REWRITE USE-ALL-CONSP-2))
 (2 2 (:REWRITE USE-ALL-CONSP))
 (2 2 (:REWRITE DEFAULT-CAR))
 (2 2 (:REWRITE CONSP-WHEN-LEN-GREATER))
 (2 2 (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT))
 (2 1 (:REWRITE DEFAULT-+-2))
 (2 1 (:REWRITE DARGP-WHEN-NATP-CHEAP))
 (2 1 (:REWRITE DARGP-WHEN-MYQUOTEP-CHEAP))
 (1 1 (:TYPE-PRESCRIPTION NATP))
 (1 1 (:TYPE-PRESCRIPTION MYQUOTEP))
 (1 1 (:REWRITE USE-ALL-DARGP-2))
 (1 1 (:REWRITE USE-ALL-DARGP))
 (1 1 (:REWRITE NONNEG-WHEN-DARGP-LESS-THAN))
 (1 1 (:REWRITE MYQUOTEP-WHEN-DARGP-LESS-THAN))
 (1 1 (:REWRITE MYQUOTEP-WHEN-BOUNDED-DAG-EXPRP))
 (1 1 (:REWRITE MYQUOTEP-WHEN-AXE-TREEP))
 (1 1 (:REWRITE INTEGERP-WHEN-DARGP-LESS-THAN))
 (1 1 (:REWRITE EQUAL-OF-LEN-AND-0))
 (1 1 (:REWRITE DEFAULT-+-1))
 (1 1 (:REWRITE DARGP-WHEN-EQUAL-OF-QUOTE-AND-CAR-CHEAP))
 (1 1 (:REWRITE DARGP-WHEN-DARGP-LESS-THAN))
 (1 1 (:REWRITE DARGP-WHEN-CONSP-CHEAP))
 (1 1 (:REWRITE CONSP-OF-CDR-WHEN-LEN-KNOWN))
 )
(LEN-WHEN-DARGP
 (44 2 (:REWRITE CONSP-FROM-LEN-CHEAP))
 (26 26 (:REWRITE LEN-WHEN-DARGP-LESS-THAN))
 (26 2 (:LINEAR LEN-OF-CDR-LINEAR-STRONG))
 (22 2 (:LINEAR LEN-OF-CDR-LINEAR))
 (13 1 (:REWRITE <-OF-+-ARG2-WHEN-NEGATIVE-CONSTANT))
 (11 10 (:REWRITE DEFAULT-+-2))
 (10 10 (:REWRITE DEFAULT-+-1))
 (8 8 (:REWRITE DEFAULT-CDR))
 (5 3 (:REWRITE DEFAULT-<-2))
 (3 3 (:REWRITE DEFAULT-<-1))
 (3 3 (:REWRITE <-WHEN-BOUNDED-AXE-TREEP))
 (2 2 (:REWRITE USE-ALL-CONSP-2))
 (2 2 (:REWRITE USE-ALL-CONSP))
 (2 2 (:REWRITE CONSP-WHEN-LEN-GREATER))
 (2 2 (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT))
 (2 1 (:REWRITE DARGP-WHEN-NATP-CHEAP))
 (2 1 (:REWRITE DARGP-WHEN-MYQUOTEP-CHEAP))
 (1 1 (:TYPE-PRESCRIPTION NATP))
 (1 1 (:TYPE-PRESCRIPTION MYQUOTEP))
 (1 1 (:REWRITE USE-ALL-DARGP-2))
 (1 1 (:REWRITE USE-ALL-DARGP))
 (1 1 (:REWRITE NONNEG-WHEN-DARGP-LESS-THAN))
 (1 1 (:REWRITE MYQUOTEP-WHEN-DARGP-LESS-THAN))
 (1 1 (:REWRITE MYQUOTEP-WHEN-BOUNDED-DAG-EXPRP))
 (1 1 (:REWRITE MYQUOTEP-WHEN-AXE-TREEP))
 (1 1 (:REWRITE INTEGERP-WHEN-DARGP-LESS-THAN))
 (1 1 (:REWRITE EQUAL-OF-LEN-AND-0))
 (1 1 (:REWRITE DEFAULT-CAR))
 (1 1 (:REWRITE DARGP-WHEN-EQUAL-OF-QUOTE-AND-CAR-CHEAP))
 (1 1 (:REWRITE DARGP-WHEN-DARGP-LESS-THAN))
 (1 1 (:REWRITE DARGP-WHEN-CONSP-CHEAP))
 (1 1 (:REWRITE CONSP-OF-CDR-WHEN-LEN-KNOWN))
 )
(<-OF--1-WHEN-DARGP)
(<-OF--0-WHEN-DARGP)
(INTEGERP-OF-IF)
(SYMBOL-LISTP-OF-CONS
 (24 2 (:REWRITE CONSP-FROM-LEN-CHEAP))
 (10 10 (:TYPE-PRESCRIPTION LEN))
 (5 5 (:REWRITE SYMBOLP-WHEN-BOUNDED-DAG-EXPRP))
 (4 2 (:REWRITE SYMBOLP-OF-CAR-WHEN-AXE-TREEP-CHEAP))
 (4 2 (:REWRITE DEFAULT-<-2))
 (3 3 (:REWRITE DEFAULT-CDR))
 (3 3 (:REWRITE DEFAULT-CAR))
 (2 2 (:TYPE-PRESCRIPTION AXE-TREEP))
 (2 2 (:REWRITE USE-ALL-CONSP-2))
 (2 2 (:REWRITE USE-ALL-CONSP))
 (2 2 (:REWRITE SYMBOLP-OF-CAR-WHEN-BOUNDED-DAG-EXPRP))
 (2 2 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
 (2 2 (:REWRITE LEN-WHEN-DARGP-LESS-THAN))
 (2 2 (:REWRITE DEFAULT-<-1))
 (2 2 (:REWRITE CONSP-WHEN-LEN-GREATER))
 (2 2 (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT))
 (2 2 (:REWRITE <-WHEN-BOUNDED-AXE-TREEP))
 (2 2 (:LINEAR LEN-POSITIVE-WHEN-CONSP-LINEAR-CHEAP))
 )
(SYMBOL-ALISTP-WHEN-ALISTP-AND-EQUAL-OF-STRIP-CARS
 (376 32 (:REWRITE CONSP-FROM-LEN-CHEAP))
 (67 34 (:REWRITE DEFAULT-CAR))
 (56 28 (:REWRITE DEFAULT-<-2))
 (52 31 (:LINEAR LEN-POSITIVE-WHEN-CONSP-LINEAR-CHEAP))
 (46 10 (:REWRITE USE-ALL-CONSP-FOR-CAR))
 (43 37 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
 (37 37 (:REWRITE LEN-WHEN-DARGP-LESS-THAN))
 (32 32 (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT))
 (29 29 (:REWRITE USE-ALL-CONSP-2))
 (29 29 (:REWRITE USE-ALL-CONSP))
 (29 29 (:REWRITE CONSP-WHEN-LEN-GREATER))
 (28 28 (:REWRITE DEFAULT-<-1))
 (28 28 (:REWRITE <-WHEN-BOUNDED-AXE-TREEP))
 (28 11 (:REWRITE SYMBOLP-OF-CAR-WHEN-AXE-TREEP-CHEAP))
 (20 10 (:REWRITE CONSP-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (18 18 (:TYPE-PRESCRIPTION ALL-CONSP))
 (17 17 (:TYPE-PRESCRIPTION SYMBOL-TERM-ALISTP))
 (15 15 (:REWRITE DEFAULT-CDR))
 (14 7 (:REWRITE SYMBOL-ALISTP-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (11 11 (:TYPE-PRESCRIPTION AXE-TREEP))
 (11 11 (:REWRITE SYMBOLP-WHEN-BOUNDED-DAG-EXPRP))
 (11 11 (:REWRITE SYMBOLP-OF-CAR-WHEN-BOUNDED-DAG-EXPRP))
 (9 9 (:REWRITE ALL-CONSP-WHEN-NOT-CONSP-CHEAP))
 (9 9 (:REWRITE ALL-CONSP-WHEN-NOT-CONSP))
 )
(<-TRANS)
(EQUAL-OF-QUOTE-AND-NTH-1-OF-ASSOC-EQUAL-WHEN-ALL-DARGP-OF-STRIP-CDRS
 (1668 63 (:REWRITE ALL-DARGP-WHEN-NOT-CONSP))
 (950 225 (:REWRITE DEFAULT-CDR))
 (845 249 (:REWRITE DEFAULT-CAR))
 (665 650 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
 (636 636 (:REWRITE LEN-WHEN-DARGP-LESS-THAN))
 (501 43 (:REWRITE <-OF-+-ARG2-WHEN-NEGATIVE-CONSTANT))
 (404 214 (:REWRITE <-TRANS))
 (340 340 (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT))
 (310 171 (:REWRITE DEFAULT-<-2))
 (249 135 (:REWRITE DEFAULT-+-2))
 (200 200 (:REWRITE USE-ALL-CONSP-2))
 (200 200 (:REWRITE USE-ALL-CONSP))
 (200 200 (:REWRITE CONSP-WHEN-LEN-GREATER))
 (171 171 (:REWRITE DEFAULT-<-1))
 (171 171 (:REWRITE <-WHEN-BOUNDED-AXE-TREEP))
 (140 41 (:REWRITE USE-ALL-CONSP-FOR-CAR))
 (135 135 (:REWRITE DEFAULT-+-1))
 (127 15 (:REWRITE USE-ALL-DARGP-FOR-CAR))
 (127 15 (:REWRITE ALL-DARGP-OF-CDR))
 (126 63 (:REWRITE ALL-DARGP-WHEN-ALL-MYQUOTEP-CHEAP))
 (94 5 (:DEFINITION TRUE-LISTP))
 (83 63 (:REWRITE ALL-DARGP-WHEN-NOT-CONSP-CHEAP))
 (82 41 (:REWRITE CONSP-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (63 63 (:TYPE-PRESCRIPTION ALL-MYQUOTEP))
 (63 63 (:REWRITE ALL-DARGP-WHEN-BOUNDED-DARG-LISTP))
 (57 57 (:TYPE-PRESCRIPTION ALL-CONSP))
 (57 57 (:REWRITE CONSP-OF-CDR-WHEN-LEN-KNOWN))
 (53 53 (:TYPE-PRESCRIPTION SYMBOL-TERM-ALISTP))
 (40 20 (:REWRITE DARGP-WHEN-NATP-CHEAP))
 (40 20 (:REWRITE DARGP-WHEN-MYQUOTEP-CHEAP))
 (24 12 (:REWRITE IFF-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (22 20 (:REWRITE USE-ALL-DARGP))
 (21 21 (:REWRITE NTH-WHEN-ZP-CHEAP))
 (21 21 (:REWRITE NTH-WHEN-NOT-CONSP-CHEAP))
 (21 21 (:REWRITE LEN-OF-CDDR-WHEN-EQUAL-OF-LEN))
 (21 21 (:REWRITE ALL-CONSP-WHEN-NOT-CONSP-CHEAP))
 (21 21 (:REWRITE ALL-CONSP-WHEN-NOT-CONSP))
 (20 20 (:TYPE-PRESCRIPTION NATP))
 (20 20 (:TYPE-PRESCRIPTION MYQUOTEP))
 (20 20 (:REWRITE USE-ALL-DARGP-2))
 (20 20 (:REWRITE NONNEG-WHEN-DARGP-LESS-THAN))
 (20 20 (:REWRITE MYQUOTEP-WHEN-DARGP-LESS-THAN))
 (20 20 (:REWRITE MYQUOTEP-WHEN-BOUNDED-DAG-EXPRP))
 (20 20 (:REWRITE MYQUOTEP-WHEN-AXE-TREEP))
 (20 20 (:REWRITE INTEGERP-WHEN-DARGP-LESS-THAN))
 (20 20 (:REWRITE DARGP-WHEN-EQUAL-OF-QUOTE-AND-CAR-CHEAP))
 (20 20 (:REWRITE DARGP-WHEN-DARGP-LESS-THAN))
 (20 20 (:REWRITE DARGP-WHEN-CONSP-CHEAP))
 (15 15 (:REWRITE NOT-<-OF-CAR-WHEN-BOUNDED-DARG-LISTP-2))
 (15 15 (:REWRITE INTEGERP-OF-CAR-WHEN-BOUNDED-DARG-LISTP))
 (2 2 (:TYPE-PRESCRIPTION MEMBERP))
 )
