(RP::PSEUDO-TERMP-RP-EX-COUNTERPART
 (404 404 (:REWRITE DEFAULT-CAR))
 (100 100 (:META RP::BINARY-OR**/AND**-GUARD-META-CORRECT))
 (96 24 (:REWRITE RP::RP-TERMP-CADR))
 (76 19 (:REWRITE RP::RP-TERMP-IMPLIES-CDR-LISTP))
 (72 12 (:DEFINITION ASSOC-EQUAL))
 (56 14 (:REWRITE RP::RP-TERMP-CADDR))
 (49 14 (:REWRITE RP::RP-TERMP-SINGLE-STEP-3))
 (29 29 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
 (24 12 (:DEFINITION NTH))
 (22 16 (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
 (20 4 (:REWRITE APPLY$-BADGEP-PROPERTIES . 1))
 (18 6 (:DEFINITION APPLY$-BADGEP))
 (16 16 (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
 (13 13 (:REWRITE RP::RP-EVL-META-EXTRACT-FNCALL))
 (13 13 (:REWRITE MX-EV-META-EXTRACT-FNCALL))
 (13 13 (:REWRITE MEXTRACT-FNCALL))
 (12 12 (:REWRITE NTH-WHEN-PREFIXP))
 (12 12 (:REWRITE ARITIES-OKP-IMPLIES-LOGICP))
 (12 6 (:DEFINITION WEAK-APPLY$-BADGE-P))
 (10 2 (:LINEAR APPLY$-BADGEP-PROPERTIES . 1))
 (6 6 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
 (4 4 (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
 (2 2 (:REWRITE DEFAULT-<-2))
 (2 2 (:REWRITE DEFAULT-<-1))
 )
(RP::RP-EX-COUNTERPART-RETURN-RP-STATEP
 (44978 1046 (:REWRITE RP::RP-TERM-LISTP-IS-TRUE-LISTP))
 (37656 523 (:DEFINITION TRUE-LISTP))
 (35771 30651 (:REWRITE DEFAULT-CDR))
 (33454 2872 (:REWRITE RP::RP-TERMP-IMPLIES-CDR-LISTP))
 (24581 523 (:DEFINITION RP::RP-TERMP))
 (17752 17752 (:REWRITE NTH-WHEN-PREFIXP))
 (17436 16768 (:REWRITE DEFAULT-CAR))
 (4632 4632 (:META RP::BINARY-OR**/AND**-GUARD-META-CORRECT))
 (4184 1569 (:REWRITE RP::RP-TERMP-CADR))
 (3389 3236 (:REWRITE DEFAULT-<-1))
 (3236 3236 (:REWRITE DEFAULT-<-2))
 (3139 609 (:DEFINITION UPDATE-NTH))
 (2615 1046 (:REWRITE RP::RP-TERMP-SINGLE-STEP-3))
 (2092 2092 (:TYPE-PRESCRIPTION RP::IS-RP$INLINE))
 (2092 1046 (:REWRITE RP::RP-TERMP-CADDR))
 (1854 1854 (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
 (1843 1063 (:REWRITE DEFAULT-+-2))
 (1350 225 (:DEFINITION ASSOC-EQUAL))
 (1328 1328 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
 (1327 1327 (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
 (1327 1327 (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
 (1063 1063 (:REWRITE DEFAULT-+-1))
 (1053 1053 (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
 (1046 1046 (:TYPE-PRESCRIPTION RP::FALIST-CONSISTENT))
 (788 788 (:LINEAR LEN-WHEN-PREFIXP))
 (385 385 (:REWRITE RP::RP-STATE-PRESERVEDP-IMPLIES-RP-STATEP))
 (385 385 (:REWRITE RP::RP-STATE-PRESERVEDP-IMPLIES-ALISTP))
 (368 368 (:TYPE-PRESCRIPTION INTEGER-RANGE-P))
 (225 225 (:REWRITE ARITIES-OKP-IMPLIES-LOGICP))
 (134 134 (:REWRITE RP::RP-EVL-META-EXTRACT-FNCALL))
 (134 134 (:REWRITE MX-EV-META-EXTRACT-FNCALL))
 (134 134 (:REWRITE MEXTRACT-FNCALL))
 (102 51 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (51 51 (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
 (51 51 (:REWRITE ACL2-NUMBER-LISTP-IMPLIES-ACL2-NUMBERP))
 (15 3 (:REWRITE APPLY$-BADGEP-PROPERTIES . 1))
 (9 3 (:DEFINITION APPLY$-BADGEP))
 (6 3 (:DEFINITION WEAK-APPLY$-BADGE-P))
 (3 3 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
 )
(RP::RP-EX-COUNTERPART-RETURN-VALID-RP-STATE-SYNTAXP
 (760 760 (:META RP::BINARY-OR**/AND**-GUARD-META-CORRECT))
 (571 571 (:REWRITE ARITIES-OKP-IMPLIES-LOGICP))
 (414 69 (:REWRITE RP::RP-STATEP-OF-INCREMENT-RW-STACK-SIZE))
 (391 391 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
 (311 311 (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
 (311 311 (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
 (276 151 (:REWRITE RP::RP-STATE-PRESERVEDP-IMPLIES-VALID-RP-STATE-SYNTAXP))
 (242 242 (:REWRITE RP::RP-STATE-PRESERVEDP-IMPLIES-RP-STATEP))
 (242 242 (:REWRITE RP::RP-STATE-PRESERVEDP-IMPLIES-ALISTP))
 (207 69 (:REWRITE RP::RP-STATEP-RP-STAT-ADD-TO-RULES-USED))
 (192 48 (:REWRITE APPLY$-BADGEP-PROPERTIES . 1))
 (96 48 (:DEFINITION APPLY$-BADGEP))
 (68 68 (:TYPE-PRESCRIPTION RP::RP-STATE-PRESERVEDP))
 (57 19 (:REWRITE RP::RP-STATE-PRESERVEDP-OF-THE-SAME))
 (48 48 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
 (48 48 (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
 (48 48 (:DEFINITION WEAK-APPLY$-BADGE-P))
 (32 32 (:REWRITE DEFAULT-<-2))
 (32 32 (:REWRITE DEFAULT-<-1))
 )
(RP::RP-EX-COUNTERPART-RETURN-VALID-RP-STATEP
 (1499 1499 (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
 (1499 1499 (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
 (1438 1438 (:META RP::BINARY-OR**/AND**-GUARD-META-CORRECT))
 (839 839 (:REWRITE ARITIES-OKP-IMPLIES-LOGICP))
 (656 656 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
 (637 637 (:REWRITE RP::VALID-RP-STATEP-NECC))
 (370 23 (:REWRITE APPLY$-BADGEP-PROPERTIES . 1))
 (326 24 (:DEFINITION APPLY$-BADGEP))
 (125 2 (:REWRITE RP::RP-TERM-LISTP-IS-TRUE-LISTP))
 (111 1 (:DEFINITION SUBSETP-EQUAL))
 (100 14 (:DEFINITION MEMBER-EQUAL))
 (95 1 (:DEFINITION TRUE-LISTP))
 (65 65 (:TYPE-PRESCRIPTION RP::RP-TERMP))
 (64 2 (:DEFINITION RP::RP-TERM-LISTP))
 (63 5 (:REWRITE RP::RP-TERMP-IMPLIES-CDR-LISTP))
 (57 7 (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-1))
 (50 2 (:DEFINITION RP::RP-TERMP))
 (31 31 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 (29 29 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
 (25 24 (:DEFINITION WEAK-APPLY$-BADGE-P))
 (23 23 (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
 (21 21 (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-3))
 (20 6 (:REWRITE RP::RP-TERMP-CADR))
 (20 4 (:REWRITE RP::RP-TERMP-CADDDR))
 (16 3 (:REWRITE RP::RP-TERMP-CADDDDR))
 (15 12 (:REWRITE DEFAULT-<-2))
 (14 14 (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-2))
 (12 12 (:TYPE-PRESCRIPTION RP::RP-TERM-LISTP))
 (12 12 (:REWRITE DEFAULT-<-1))
 (12 4 (:REWRITE RP::RP-TERMP-CADDR))
 (11 4 (:REWRITE RP::RP-TERMP-SINGLE-STEP-3))
 (8 8 (:TYPE-PRESCRIPTION RP::IS-RP$INLINE))
 (8 4 (:REWRITE APPLY$-BADGEP-PROPERTIES . 3))
 (7 7 (:TYPE-PRESCRIPTION LEN))
 (6 2 (:LINEAR APPLY$-BADGEP-PROPERTIES . 1))
 (6 1 (:DEFINITION LEN))
 (5 5 (:TYPE-PRESCRIPTION ALL-NILS))
 (4 4 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (4 4 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
 (4 4 (:LINEAR LEN-WHEN-PREFIXP))
 (4 1 (:DEFINITION ALL-NILS))
 (2 2 (:TYPE-PRESCRIPTION NATP))
 (2 2 (:TYPE-PRESCRIPTION RP::FALIST-CONSISTENT))
 (2 1 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (2 1 (:REWRITE DEFAULT-+-2))
 (1 1 (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
 (1 1 (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
 (1 1 (:REWRITE DEFAULT-+-1))
 (1 1 (:REWRITE ACL2-NUMBER-LISTP-IMPLIES-ACL2-NUMBERP))
 )
(RP::VALID-SC-RP-EX-COUNTERPART
 (3564 36 (:DEFINITION RP::EVAL-AND-ALL))
 (741 42 (:DEFINITION RP::TRANS-LIST))
 (373 42 (:DEFINITION RP::IS-FALIST))
 (370 370 (:TYPE-PRESCRIPTION RP::RP-TRANS-LST))
 (279 279 (:META RP::BINARY-OR**/AND**-GUARD-META-CORRECT))
 (165 165 (:REWRITE RP::CONSP-RP-TRANS-LST))
 (107 60 (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
 (97 97 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
 (96 16 (:DEFINITION ASSOC-EQUAL))
 (72 72 (:TYPE-PRESCRIPTION RP::CONTEXT-FROM-RP))
 (60 60 (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
 (60 60 (:REWRITE RP::RP-EVL-OF-ZP-CALL))
 (60 60 (:REWRITE RP::RP-EVL-OF-UNARY-/-CALL))
 (60 60 (:REWRITE RP::RP-EVL-OF-UNARY---CALL))
 (60 60 (:REWRITE RP::RP-EVL-OF-TYPESPEC-CHECK-CALL))
 (60 60 (:REWRITE RP::RP-EVL-OF-SYNP-CALL))
 (60 60 (:REWRITE RP::RP-EVL-OF-SYMBOLP-CALL))
 (60 60 (:REWRITE RP::RP-EVL-OF-SYMBOL-PACKAGE-NAME-CALL))
 (60 60 (:REWRITE RP::RP-EVL-OF-SYMBOL-NAME-CALL))
 (60 60 (:REWRITE RP::RP-EVL-OF-STRINGP-CALL))
 (60 60 (:REWRITE RP::RP-EVL-OF-RP-EQUAL-SUBTERMS-CALL))
 (60 60 (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-SUBTERMS-CALL))
 (60 60 (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-CALL))
 (60 60 (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CALL))
 (60 60 (:REWRITE RP::RP-EVL-OF-RP-CALL))
 (60 60 (:REWRITE RP::RP-EVL-OF-RETURN-LAST-CALL))
 (60 60 (:REWRITE RP::RP-EVL-OF-REALPART-CALL))
 (60 60 (:REWRITE RP::RP-EVL-OF-RATIONALP-CALL))
 (60 60 (:REWRITE RP::RP-EVL-OF-NUMERATOR-CALL))
 (60 60 (:REWRITE RP::RP-EVL-OF-NOT-CALL))
 (60 60 (:REWRITE RP::RP-EVL-OF-NATP-CALL))
 (60 60 (:REWRITE RP::RP-EVL-OF-LAMBDA))
 (60 60 (:REWRITE RP::RP-EVL-OF-INTERN-IN-PACKAGE-OF-SYMBOL-CALL))
 (60 60 (:REWRITE RP::RP-EVL-OF-INTEGERP-CALL))
 (60 60 (:REWRITE RP::RP-EVL-OF-IMPLIES-CALL))
 (60 60 (:REWRITE RP::RP-EVL-OF-IMAGPART-CALL))
 (60 60 (:REWRITE RP::RP-EVL-OF-IFF-CALL))
 (60 60 (:REWRITE RP::RP-EVL-OF-IF-CALL))
 (60 60 (:REWRITE RP::RP-EVL-OF-HIDE-CALL))
 (60 60 (:REWRITE RP::RP-EVL-OF-FORCE-CALL))
 (60 60 (:REWRITE RP::RP-EVL-OF-FORCE$-CALL))
 (60 60 (:REWRITE RP::RP-EVL-OF-FALIST-CALL))
 (60 60 (:REWRITE RP::RP-EVL-OF-EQUAL-CALL))
 (60 60 (:REWRITE RP::RP-EVL-OF-DONT-RW-CONTEXT-CALL))
 (60 60 (:REWRITE RP::RP-EVL-OF-DENOMINATOR-CALL))
 (60 60 (:REWRITE RP::RP-EVL-OF-CONSP-CALL))
 (60 60 (:REWRITE RP::RP-EVL-OF-CONS-CALL))
 (60 60 (:REWRITE RP::RP-EVL-OF-COMPLEX-RATIONALP-CALL))
 (60 60 (:REWRITE RP::RP-EVL-OF-COERCE-CALL))
 (60 60 (:REWRITE RP::RP-EVL-OF-CODE-CHAR-CALL))
 (60 60 (:REWRITE RP::RP-EVL-OF-CHARACTERP-CALL))
 (60 60 (:REWRITE RP::RP-EVL-OF-CHAR-CODE-CALL))
 (60 60 (:REWRITE RP::RP-EVL-OF-CDR-CALL))
 (60 60 (:REWRITE RP::RP-EVL-OF-CASESPLIT-FROM-CONTEXT-TRIG-CALL))
 (60 60 (:REWRITE RP::RP-EVL-OF-CAR-CALL))
 (60 60 (:REWRITE RP::RP-EVL-OF-BITP-CALL))
 (60 60 (:REWRITE RP::RP-EVL-OF-BINARY-+-CALL))
 (60 60 (:REWRITE RP::RP-EVL-OF-BINARY-*-CALL))
 (60 60 (:REWRITE RP::RP-EVL-OF-BAD-ATOM<=-CALL))
 (60 60 (:REWRITE RP::RP-EVL-OF-ACL2-NUMBERP-CALL))
 (60 60 (:REWRITE RP::RP-EVL-OF-<-CALL))
 (51 17 (:DEFINITION APPLY$-BADGEP))
 (50 10 (:REWRITE APPLY$-BADGEP-PROPERTIES . 1))
 (44 2 (:DEFINITION RP::RP-TERMP))
 (43 3 (:REWRITE RP::RP-TERMP-CADR))
 (35 7 (:LINEAR APPLY$-BADGEP-PROPERTIES . 1))
 (34 17 (:DEFINITION WEAK-APPLY$-BADGE-P))
 (32 16 (:DEFINITION NTH))
 (17 17 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
 (17 17 (:REWRITE RP::RP-EVL-META-EXTRACT-FNCALL))
 (17 17 (:REWRITE MX-EV-META-EXTRACT-FNCALL))
 (17 17 (:REWRITE MEXTRACT-FNCALL))
 (16 16 (:REWRITE NTH-WHEN-PREFIXP))
 (16 16 (:REWRITE ARITIES-OKP-IMPLIES-LOGICP))
 (10 10 (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
 (9 6 (:REWRITE DEFAULT-<-2))
 (9 6 (:REWRITE DEFAULT-<-1))
 (5 2 (:REWRITE RP::RP-TERMP-SINGLE-STEP-3))
 (4 2 (:REWRITE RP::RP-TERMP-CADDR))
 (4 2 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (2 2 (:TYPE-PRESCRIPTION RP::RP-TERM-LISTP))
 (2 2 (:TYPE-PRESCRIPTION RP::FALIST-CONSISTENT))
 (2 2 (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
 (2 2 (:REWRITE ACL2-NUMBER-LISTP-IMPLIES-ACL2-NUMBERP))
 (2 1 (:REWRITE RP::RP-TERMP-IMPLIES-CDR-LISTP))
 (1 1 (:DEFINITION RP::RP-TRANS-LST))
 )
(RP::LEMMA1
 (84 83 (:REWRITE DEFAULT-CAR))
 (61 13 (:REWRITE RP::RP-TERMP-IMPLIES-CDR-LISTP))
 (43 42 (:REWRITE DEFAULT-CDR))
 (12 3 (:REWRITE RP::RP-TERMP-CADR))
 (11 11 (:META RP::BINARY-OR**/AND**-GUARD-META-CORRECT))
 (8 8 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
 (8 8 (:REWRITE RP::CONSP-RP-TRANS-LST))
 (1 1 (:REWRITE RP::RP-EVL-OF-ZP-CALL))
 (1 1 (:REWRITE RP::RP-EVL-OF-UNARY-/-CALL))
 (1 1 (:REWRITE RP::RP-EVL-OF-UNARY---CALL))
 (1 1 (:REWRITE RP::RP-EVL-OF-TYPESPEC-CHECK-CALL))
 (1 1 (:REWRITE RP::RP-EVL-OF-SYNP-CALL))
 (1 1 (:REWRITE RP::RP-EVL-OF-SYMBOLP-CALL))
 (1 1 (:REWRITE RP::RP-EVL-OF-SYMBOL-PACKAGE-NAME-CALL))
 (1 1 (:REWRITE RP::RP-EVL-OF-SYMBOL-NAME-CALL))
 (1 1 (:REWRITE RP::RP-EVL-OF-STRINGP-CALL))
 (1 1 (:REWRITE RP::RP-EVL-OF-RP-EQUAL-SUBTERMS-CALL))
 (1 1 (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-SUBTERMS-CALL))
 (1 1 (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-CALL))
 (1 1 (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CALL))
 (1 1 (:REWRITE RP::RP-EVL-OF-RP-CALL))
 (1 1 (:REWRITE RP::RP-EVL-OF-RETURN-LAST-CALL))
 (1 1 (:REWRITE RP::RP-EVL-OF-REALPART-CALL))
 (1 1 (:REWRITE RP::RP-EVL-OF-RATIONALP-CALL))
 (1 1 (:REWRITE RP::RP-EVL-OF-NUMERATOR-CALL))
 (1 1 (:REWRITE RP::RP-EVL-OF-NOT-CALL))
 (1 1 (:REWRITE RP::RP-EVL-OF-NATP-CALL))
 (1 1 (:REWRITE RP::RP-EVL-OF-LAMBDA))
 (1 1 (:REWRITE RP::RP-EVL-OF-INTERN-IN-PACKAGE-OF-SYMBOL-CALL))
 (1 1 (:REWRITE RP::RP-EVL-OF-INTEGERP-CALL))
 (1 1 (:REWRITE RP::RP-EVL-OF-IMPLIES-CALL))
 (1 1 (:REWRITE RP::RP-EVL-OF-IMAGPART-CALL))
 (1 1 (:REWRITE RP::RP-EVL-OF-IFF-CALL))
 (1 1 (:REWRITE RP::RP-EVL-OF-IF-CALL))
 (1 1 (:REWRITE RP::RP-EVL-OF-HIDE-CALL))
 (1 1 (:REWRITE RP::RP-EVL-OF-FORCE-CALL))
 (1 1 (:REWRITE RP::RP-EVL-OF-FORCE$-CALL))
 (1 1 (:REWRITE RP::RP-EVL-OF-FALIST-CALL))
 (1 1 (:REWRITE RP::RP-EVL-OF-EQUAL-CALL))
 (1 1 (:REWRITE RP::RP-EVL-OF-DONT-RW-CONTEXT-CALL))
 (1 1 (:REWRITE RP::RP-EVL-OF-DENOMINATOR-CALL))
 (1 1 (:REWRITE RP::RP-EVL-OF-CONSP-CALL))
 (1 1 (:REWRITE RP::RP-EVL-OF-CONS-CALL))
 (1 1 (:REWRITE RP::RP-EVL-OF-COMPLEX-RATIONALP-CALL))
 (1 1 (:REWRITE RP::RP-EVL-OF-COERCE-CALL))
 (1 1 (:REWRITE RP::RP-EVL-OF-CODE-CHAR-CALL))
 (1 1 (:REWRITE RP::RP-EVL-OF-CHARACTERP-CALL))
 (1 1 (:REWRITE RP::RP-EVL-OF-CHAR-CODE-CALL))
 (1 1 (:REWRITE RP::RP-EVL-OF-CDR-CALL))
 (1 1 (:REWRITE RP::RP-EVL-OF-CASESPLIT-FROM-CONTEXT-TRIG-CALL))
 (1 1 (:REWRITE RP::RP-EVL-OF-CAR-CALL))
 (1 1 (:REWRITE RP::RP-EVL-OF-BITP-CALL))
 (1 1 (:REWRITE RP::RP-EVL-OF-BINARY-+-CALL))
 (1 1 (:REWRITE RP::RP-EVL-OF-BINARY-*-CALL))
 (1 1 (:REWRITE RP::RP-EVL-OF-BAD-ATOM<=-CALL))
 (1 1 (:REWRITE RP::RP-EVL-OF-ACL2-NUMBERP-CALL))
 (1 1 (:REWRITE RP::RP-EVL-OF-<-CALL))
 )
(RP::LEMMA3
 (70 7 (:REWRITE RP::RP-TERMP-IMPLIES-CDR-LISTP))
 (45 45 (:REWRITE DEFAULT-CAR))
 (35 35 (:REWRITE DEFAULT-CDR))
 (12 12 (:META RP::BINARY-OR**/AND**-GUARD-META-CORRECT))
 (8 3 (:REWRITE RP::RP-TERMP-CADR))
 (7 7 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
 (5 2 (:REWRITE RP::RP-TERMP-SINGLE-STEP-3))
 (4 4 (:TYPE-PRESCRIPTION RP::IS-RP$INLINE))
 (4 2 (:REWRITE RP::RP-TERMP-CADDR))
 (2 2 (:TYPE-PRESCRIPTION RP::FALIST-CONSISTENT))
 (1 1 (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
 (1 1 (:REWRITE RP::RP-EVL-OF-ZP-CALL))
 (1 1 (:REWRITE RP::RP-EVL-OF-UNARY-/-CALL))
 (1 1 (:REWRITE RP::RP-EVL-OF-UNARY---CALL))
 (1 1 (:REWRITE RP::RP-EVL-OF-TYPESPEC-CHECK-CALL))
 (1 1 (:REWRITE RP::RP-EVL-OF-SYNP-CALL))
 (1 1 (:REWRITE RP::RP-EVL-OF-SYMBOLP-CALL))
 (1 1 (:REWRITE RP::RP-EVL-OF-SYMBOL-PACKAGE-NAME-CALL))
 (1 1 (:REWRITE RP::RP-EVL-OF-SYMBOL-NAME-CALL))
 (1 1 (:REWRITE RP::RP-EVL-OF-STRINGP-CALL))
 (1 1 (:REWRITE RP::RP-EVL-OF-RP-EQUAL-SUBTERMS-CALL))
 (1 1 (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-SUBTERMS-CALL))
 (1 1 (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-CALL))
 (1 1 (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CALL))
 (1 1 (:REWRITE RP::RP-EVL-OF-RP-CALL))
 (1 1 (:REWRITE RP::RP-EVL-OF-RETURN-LAST-CALL))
 (1 1 (:REWRITE RP::RP-EVL-OF-REALPART-CALL))
 (1 1 (:REWRITE RP::RP-EVL-OF-RATIONALP-CALL))
 (1 1 (:REWRITE RP::RP-EVL-OF-NUMERATOR-CALL))
 (1 1 (:REWRITE RP::RP-EVL-OF-NOT-CALL))
 (1 1 (:REWRITE RP::RP-EVL-OF-NATP-CALL))
 (1 1 (:REWRITE RP::RP-EVL-OF-LAMBDA))
 (1 1 (:REWRITE RP::RP-EVL-OF-INTERN-IN-PACKAGE-OF-SYMBOL-CALL))
 (1 1 (:REWRITE RP::RP-EVL-OF-INTEGERP-CALL))
 (1 1 (:REWRITE RP::RP-EVL-OF-IMPLIES-CALL))
 (1 1 (:REWRITE RP::RP-EVL-OF-IMAGPART-CALL))
 (1 1 (:REWRITE RP::RP-EVL-OF-IFF-CALL))
 (1 1 (:REWRITE RP::RP-EVL-OF-IF-CALL))
 (1 1 (:REWRITE RP::RP-EVL-OF-HIDE-CALL))
 (1 1 (:REWRITE RP::RP-EVL-OF-FORCE-CALL))
 (1 1 (:REWRITE RP::RP-EVL-OF-FORCE$-CALL))
 (1 1 (:REWRITE RP::RP-EVL-OF-FALIST-CALL))
 (1 1 (:REWRITE RP::RP-EVL-OF-EQUAL-CALL))
 (1 1 (:REWRITE RP::RP-EVL-OF-DONT-RW-CONTEXT-CALL))
 (1 1 (:REWRITE RP::RP-EVL-OF-DENOMINATOR-CALL))
 (1 1 (:REWRITE RP::RP-EVL-OF-CONSP-CALL))
 (1 1 (:REWRITE RP::RP-EVL-OF-CONS-CALL))
 (1 1 (:REWRITE RP::RP-EVL-OF-COMPLEX-RATIONALP-CALL))
 (1 1 (:REWRITE RP::RP-EVL-OF-COERCE-CALL))
 (1 1 (:REWRITE RP::RP-EVL-OF-CODE-CHAR-CALL))
 (1 1 (:REWRITE RP::RP-EVL-OF-CHARACTERP-CALL))
 (1 1 (:REWRITE RP::RP-EVL-OF-CHAR-CODE-CALL))
 (1 1 (:REWRITE RP::RP-EVL-OF-CDR-CALL))
 (1 1 (:REWRITE RP::RP-EVL-OF-CASESPLIT-FROM-CONTEXT-TRIG-CALL))
 (1 1 (:REWRITE RP::RP-EVL-OF-CAR-CALL))
 (1 1 (:REWRITE RP::RP-EVL-OF-BITP-CALL))
 (1 1 (:REWRITE RP::RP-EVL-OF-BINARY-+-CALL))
 (1 1 (:REWRITE RP::RP-EVL-OF-BINARY-*-CALL))
 (1 1 (:REWRITE RP::RP-EVL-OF-BAD-ATOM<=-CALL))
 (1 1 (:REWRITE RP::RP-EVL-OF-ACL2-NUMBERP-CALL))
 (1 1 (:REWRITE RP::RP-EVL-OF-<-CALL))
 (1 1 (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
 )
(RP::RP-EVL-OF-RP-EX-COUNTERPART
 (1828 1828 (:META RP::BINARY-OR**/AND**-GUARD-META-CORRECT))
 (1248 1248 (:TYPE-PRESCRIPTION KWOTE-LST))
 (500 239 (:REWRITE RP::RP-EVL-OF-SYMBOLP-CALL))
 (500 239 (:REWRITE RP::RP-EVL-OF-SYMBOL-PACKAGE-NAME-CALL))
 (500 239 (:REWRITE RP::RP-EVL-OF-SYMBOL-NAME-CALL))
 (500 239 (:REWRITE RP::RP-EVL-OF-STRINGP-CALL))
 (500 239 (:REWRITE RP::RP-EVL-OF-RP-EQUAL-SUBTERMS-CALL))
 (500 239 (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-SUBTERMS-CALL))
 (500 239 (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-CALL))
 (500 239 (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CALL))
 (500 239 (:REWRITE RP::RP-EVL-OF-REALPART-CALL))
 (500 239 (:REWRITE RP::RP-EVL-OF-RATIONALP-CALL))
 (500 239 (:REWRITE RP::RP-EVL-OF-NUMERATOR-CALL))
 (500 239 (:REWRITE RP::RP-EVL-OF-INTERN-IN-PACKAGE-OF-SYMBOL-CALL))
 (500 239 (:REWRITE RP::RP-EVL-OF-IMAGPART-CALL))
 (500 239 (:REWRITE RP::RP-EVL-OF-FORCE-CALL))
 (500 239 (:REWRITE RP::RP-EVL-OF-FORCE$-CALL))
 (500 239 (:REWRITE RP::RP-EVL-OF-DENOMINATOR-CALL))
 (500 239 (:REWRITE RP::RP-EVL-OF-CONSP-CALL))
 (500 239 (:REWRITE RP::RP-EVL-OF-COMPLEX-RATIONALP-CALL))
 (500 239 (:REWRITE RP::RP-EVL-OF-COERCE-CALL))
 (500 239 (:REWRITE RP::RP-EVL-OF-BINARY-+-CALL))
 (500 239 (:REWRITE RP::RP-EVL-OF-BINARY-*-CALL))
 (500 239 (:REWRITE RP::RP-EVL-OF-BAD-ATOM<=-CALL))
 (446 221 (:REWRITE RP::RP-EVL-OF-UNARY-/-CALL))
 (446 221 (:REWRITE RP::RP-EVL-OF-UNARY---CALL))
 (446 221 (:REWRITE RP::RP-EVL-OF-TYPESPEC-CHECK-CALL))
 (446 221 (:REWRITE RP::RP-EVL-OF-IFF-CALL))
 (446 221 (:REWRITE RP::RP-EVL-OF-CODE-CHAR-CALL))
 (446 221 (:REWRITE RP::RP-EVL-OF-CHARACTERP-CALL))
 (446 221 (:REWRITE RP::RP-EVL-OF-CHAR-CODE-CALL))
 (446 221 (:REWRITE RP::RP-EVL-OF-ACL2-NUMBERP-CALL))
 (446 221 (:REWRITE RP::RP-EVL-OF-<-CALL))
 (422 213 (:REWRITE RP::RP-EVL-OF-SYNP-CALL))
 (422 213 (:REWRITE RP::RP-EVL-OF-RETURN-LAST-CALL))
 (422 213 (:REWRITE RP::RP-EVL-OF-IMPLIES-CALL))
 (422 213 (:REWRITE RP::RP-EVL-OF-IF-CALL))
 (422 213 (:REWRITE RP::RP-EVL-OF-HIDE-CALL))
 (422 213 (:REWRITE RP::RP-EVL-OF-DONT-RW-CONTEXT-CALL))
 (422 213 (:REWRITE RP::RP-EVL-OF-CONS-CALL))
 (422 213 (:REWRITE RP::RP-EVL-OF-CASESPLIT-FROM-CONTEXT-TRIG-CALL))
 (409 213 (:REWRITE RP::RP-EVL-OF-RP-CALL))
 (404 207 (:REWRITE RP::RP-EVL-OF-EQUAL-CALL))
 (375 207 (:REWRITE RP::RP-EVL-OF-LAMBDA))
 (366 61 (:DEFINITION ASSOC-EQUAL))
 (183 11 (:DEFINITION RP::TRANS-LIST))
 (176 129 (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
 (166 26 (:LINEAR APPLY$-BADGEP-PROPERTIES . 1))
 (162 42 (:DEFINITION APPLY$-BADGEP))
 (158 158 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
 (132 132 (:REWRITE RP::RP-EVL-META-EXTRACT-FN-CHECK-DEF))
 (129 129 (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
 (120 42 (:DEFINITION WEAK-APPLY$-BADGE-P))
 (118 59 (:DEFINITION NTH))
 (102 23 (:REWRITE RP::RP-TERMP-CADDR))
 (87 23 (:REWRITE RP::RP-TERMP-SINGLE-STEP-3))
 (82 18 (:REWRITE APPLY$-BADGEP-PROPERTIES . 1))
 (71 71 (:REWRITE RP::CONSP-RP-TRANS-LST))
 (59 59 (:REWRITE NTH-WHEN-PREFIXP))
 (59 59 (:REWRITE ARITIES-OKP-IMPLIES-LOGICP))
 (42 42 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
 (26 10 (:REWRITE RP::RP-TERM-LISTP-OF-RP-TRANS-LST))
 (23 23 (:REWRITE MX-EV-META-EXTRACT-FNCALL))
 (23 23 (:REWRITE MEXTRACT-FNCALL))
 (18 18 (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
 (18 12 (:REWRITE DEFAULT-<-2))
 (18 12 (:REWRITE DEFAULT-<-1))
 (8 4 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (4 4 (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
 (4 4 (:REWRITE ACL2-NUMBER-LISTP-IMPLIES-ACL2-NUMBERP))
 )
