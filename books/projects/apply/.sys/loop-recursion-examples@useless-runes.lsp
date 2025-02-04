(|2^N-1|
 (28 2 (:DEFINITION FROM-TO-BY-DOWN-OPENER))
 (24 2 (:REWRITE TRUE-LIST-LISTP-IMPLIES-TRUE-LISTP-XXX))
 (19 2 (:DEFINITION TRUE-LIST-LISTP))
 (16 16 (:REWRITE DEFAULT-+-2))
 (16 16 (:REWRITE DEFAULT-+-1))
 (11 11 (:REWRITE DEFAULT-<-2))
 (11 11 (:REWRITE DEFAULT-<-1))
 (10 2 (:DEFINITION BINARY-APPEND))
 (8 4 (:REWRITE FOLD-CONSTS-IN-+))
 (7 5 (:REWRITE DEFAULT-CAR))
 (6 6 (:TYPE-PRESCRIPTION TRUE-LIST-LISTP))
 (6 6 (:REWRITE DEFAULT-*-2))
 (6 6 (:REWRITE DEFAULT-*-1))
 (6 5 (:REWRITE DEFAULT-CDR))
 (5 1 (:DEFINITION TRUE-LISTP))
 (4 4 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (2 2 (:REWRITE DEFAULT-UNARY-MINUS))
 (2 2 (:REWRITE ALWAYS$-P-LST-IMPLIES-P-ELEMENT-COROLLARY))
 (1 1 (:REWRITE ZP-OPEN))
 (1 1 (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
 )
(APPLY$-WARRANT-2^N-1)
(APPLY$-WARRANT-2^N-1-DEFINITION)
(APPLY$-WARRANT-2^N-1-NECC)
(APPLY$-2^N-1
 (2 2 (:TYPE-PRESCRIPTION APPLY$-PRIMP))
 (2 2 (:REWRITE DEFAULT-CAR))
 (2 1 (:REWRITE APPLY$-PRIMP-BADGE))
 (2 1 (:REWRITE APPLY$-PRIMITIVE))
 )
(|2^N-1|
 (416 3 (:DEFINITION SUM$))
 (368 3 (:REWRITE APPLY$-CONSP-ARITY-1))
 (266 19 (:DEFINITION FROM-TO-BY-DOWN-OPENER))
 (102 80 (:REWRITE DEFAULT-CAR))
 (95 19 (:DEFINITION BINARY-APPEND))
 (85 79 (:REWRITE DEFAULT-+-2))
 (85 79 (:REWRITE DEFAULT-+-1))
 (55 47 (:REWRITE DEFAULT-CDR))
 (48 48 (:REWRITE DEFAULT-<-2))
 (48 48 (:REWRITE DEFAULT-<-1))
 (48 4 (:REWRITE TRUE-LIST-LISTP-IMPLIES-TRUE-LISTP-XXX))
 (38 4 (:DEFINITION TRUE-LIST-LISTP))
 (12 12 (:TYPE-PRESCRIPTION TRUE-LIST-LISTP))
 (10 2 (:DEFINITION TRUE-LISTP))
 (9 9 (:REWRITE DEFAULT-*-2))
 (9 9 (:REWRITE DEFAULT-*-1))
 (8 8 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (5 5 (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
 (4 4 (:REWRITE ALWAYS$-P-LST-IMPLIES-P-ELEMENT-COROLLARY))
 (3 3 (:TYPE-PRESCRIPTION LEN))
 (2 2 (:REWRITE DEFAULT-UNARY-MINUS))
 (2 2 (:REWRITE APPLY$-WARRANT-2^N-1-NECC))
 )
(2^N-1-LOOP-LEMMA
 (2411 17 (:REWRITE APPLY$-CONSP-ARITY-1))
 (610 122 (:DEFINITION BINARY-APPEND))
 (515 429 (:REWRITE DEFAULT-+-2))
 (469 429 (:REWRITE DEFAULT-+-1))
 (317 317 (:REWRITE DEFAULT-<-2))
 (317 317 (:REWRITE DEFAULT-<-1))
 (297 287 (:REWRITE DEFAULT-CAR))
 (213 199 (:REWRITE DEFAULT-CDR))
 (80 16 (:REWRITE ZP-OPEN))
 (57 20 (:REWRITE DEFAULT-*-2))
 (48 25 (:REWRITE APPLY$-PRIMITIVE))
 (26 26 (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
 (23 23 (:TYPE-PRESCRIPTION APPLY$-PRIMP))
 (20 20 (:REWRITE DEFAULT-*-1))
 (17 17 (:TYPE-PRESCRIPTION LEN))
 (10 10 (:REWRITE APPLY$-WARRANT-2^N-1-NECC))
 (5 5 (:REWRITE ZIP-OPEN))
 (4 2 (:TYPE-PRESCRIPTION TRUE-LISTP-APPEND))
 (2 2 (:TYPE-PRESCRIPTION BINARY-APPEND))
 )
(2^N-1-IS-EXPT-2-N-1
 (32 2 (:DEFINITION EXPT))
 (14 1 (:DEFINITION FROM-TO-BY-DOWN-OPENER))
 (12 2 (:REWRITE COMMUTATIVITY-OF-+))
 (10 10 (:REWRITE DEFAULT-+-2))
 (10 10 (:REWRITE DEFAULT-+-1))
 (9 3 (:REWRITE FOLD-CONSTS-IN-+))
 (6 2 (:REWRITE DEFAULT-*-2))
 (5 5 (:REWRITE DEFAULT-<-2))
 (5 5 (:REWRITE DEFAULT-<-1))
 (5 1 (:DEFINITION BINARY-APPEND))
 (3 1 (:DEFINITION FROM-TO-BY))
 (2 2 (:TYPE-PRESCRIPTION FROM-TO-BY))
 (2 2 (:REWRITE ZIP-OPEN))
 (2 2 (:REWRITE DEFAULT-*-1))
 (1 1 (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
 (1 1 (:REWRITE DEFAULT-CDR))
 (1 1 (:REWRITE DEFAULT-CAR))
 (1 1 (:REWRITE APPLY$-WARRANT-2^N-1-NECC))
 )
(PSTERMP
 (8828 5 (:DEFINITION ALWAYS$))
 (8808 5 (:REWRITE APPLY$-CONSP-ARITY-1))
 (8788 5 (:REWRITE BETA-REDUCTION))
 (8747 10 (:REWRITE EV$-OPENER))
 (8732 40 (:DEFINITION TAMEP))
 (8707 50 (:DEFINITION SUITABLY-TAMEP-LISTP))
 (8390 66 (:DEFINITION APPLY$-BADGEP))
 (5619 27 (:DEFINITION SUBSETP-EQUAL))
 (5287 379 (:DEFINITION MEMBER-EQUAL))
 (4854 96 (:LINEAR APPLY$-BADGEP-PROPERTIES . 1))
 (3761 109 (:REWRITE APPLY$-BADGEP-PROPERTIES . 1))
 (3309 189 (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-1))
 (3253 3253 (:REWRITE DEFAULT-CDR))
 (1670 20 (:REWRITE ZP-OPEN))
 (894 894 (:REWRITE DEFAULT-CAR))
 (832 84 (:DEFINITION NATP))
 (632 114 (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
 (575 530 (:REWRITE APPLY$-PRIMP-BADGE))
 (567 567 (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-3))
 (520 2 (:DEFINITION INTEGER-LISTP))
 (438 438 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
 (434 200 (:REWRITE DEFAULT-+-2))
 (378 378 (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-2))
 (257 200 (:REWRITE DEFAULT-+-1))
 (238 110 (:REWRITE APPLY$-BADGEP-PROPERTIES . 3))
 (216 66 (:DEFINITION WEAK-APPLY$-BADGE-P))
 (162 27 (:DEFINITION ALL-NILS))
 (151 65 (:REWRITE APPLY$-BADGEP-PROPERTIES . 2))
 (140 125 (:REWRITE DEFAULT-<-2))
 (135 135 (:TYPE-PRESCRIPTION ALL-NILS))
 (134 52 (:LINEAR APPLY$-BADGEP-PROPERTIES . 2))
 (130 125 (:REWRITE DEFAULT-<-1))
 (110 110 (:TYPE-PRESCRIPTION TAMEP))
 (108 108 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
 (100 100 (:TYPE-PRESCRIPTION SUITABLY-TAMEP-LISTP))
 (64 16 (:DEFINITION INTEGER-ABS))
 (51 51 (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
 (50 50 (:TYPE-PRESCRIPTION APPLY$-PRIMP))
 (36 10 (:DEFINITION PAIRLIS$))
 (30 2 (:REWRITE TRUE-LIST-LISTP-IMPLIES-TRUE-LISTP-XXX))
 (26 10 (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
 (25 25 (:LINEAR MEMBER-EQUAL-ACL2-COUNT-SMALLER-3))
 (24 2 (:DEFINITION TRUE-LIST-LISTP))
 (17 17 (:LINEAR MEMBER-EQUAL-ACL2-COUNT-SMALLER-2))
 (16 16 (:REWRITE DEFAULT-UNARY-MINUS))
 (16 4 (:DEFINITION SYMBOL-LISTP))
 (14 2 (:DEFINITION RATIONAL-LISTP))
 (10 10 (:TYPE-PRESCRIPTION TRUE-LIST-LISTP))
 (10 10 (:TYPE-PRESCRIPTION RATIONAL-LISTP))
 (10 10 (:TYPE-PRESCRIPTION INTEGER-LISTP))
 (10 5 (:REWRITE APPLY$-PRIMITIVE))
 (9 9 (:LINEAR MEMBER-EQUAL-ACL2-COUNT-SMALLER-1))
 (8 8 (:REWRITE INTEGERP==>NUMERATOR-=-X))
 (8 8 (:REWRITE INTEGERP==>DENOMINATOR-=-1))
 (8 8 (:REWRITE DEFAULT-REALPART))
 (8 8 (:REWRITE DEFAULT-NUMERATOR))
 (8 8 (:REWRITE DEFAULT-IMAGPART))
 (8 8 (:REWRITE DEFAULT-DENOMINATOR))
 (8 8 (:REWRITE DEFAULT-COERCE-2))
 (8 8 (:REWRITE DEFAULT-COERCE-1))
 (5 5 (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
 (5 5 (:REWRITE ALWAYS$-P-LST-IMPLIES-P-ELEMENT))
 (2 2 (:REWRITE ALWAYS$-P-LST-IMPLIES-P-ELEMENT-COROLLARY))
 )
(APPLY$-WARRANT-PSTERMP)
(APPLY$-WARRANT-PSTERMP-DEFINITION)
(APPLY$-WARRANT-PSTERMP-NECC)
(APPLY$-PSTERMP
 (2 2 (:TYPE-PRESCRIPTION APPLY$-PRIMP))
 (2 2 (:REWRITE DEFAULT-CAR))
 (2 1 (:REWRITE APPLY$-PRIMP-BADGE))
 (2 1 (:REWRITE APPLY$-PRIMITIVE))
 )
(PSTERMP-INDUCTOR
 (292 121 (:REWRITE DEFAULT-+-2))
 (165 121 (:REWRITE DEFAULT-+-1))
 (107 107 (:REWRITE DEFAULT-CDR))
 (94 94 (:REWRITE DEFAULT-CAR))
 (40 10 (:DEFINITION INTEGER-ABS))
 (36 12 (:DEFINITION APPLY$-BADGEP))
 (30 6 (:REWRITE APPLY$-BADGEP-PROPERTIES . 3))
 (27 14 (:REWRITE DEFAULT-<-2))
 (24 12 (:DEFINITION WEAK-APPLY$-BADGE-P))
 (22 22 (:LINEAR MEMBER-EQUAL-ACL2-COUNT-SMALLER-3))
 (21 21 (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
 (18 14 (:REWRITE DEFAULT-<-1))
 (16 4 (:DEFINITION SYMBOL-LISTP))
 (15 15 (:LINEAR MEMBER-EQUAL-ACL2-COUNT-SMALLER-2))
 (15 3 (:REWRITE APPLY$-BADGEP-PROPERTIES . 2))
 (15 3 (:REWRITE APPLY$-BADGEP-PROPERTIES . 1))
 (12 12 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
 (10 10 (:REWRITE DEFAULT-UNARY-MINUS))
 (10 10 (:LINEAR MEMBER-EQUAL-ACL2-COUNT-SMALLER-0))
 (8 8 (:LINEAR MEMBER-EQUAL-ACL2-COUNT-SMALLER-1))
 (5 5 (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
 (5 5 (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
 (5 5 (:REWRITE INTEGERP==>NUMERATOR-=-X))
 (5 5 (:REWRITE INTEGERP==>DENOMINATOR-=-1))
 (5 5 (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
 (5 5 (:REWRITE DEFAULT-REALPART))
 (5 5 (:REWRITE DEFAULT-NUMERATOR))
 (5 5 (:REWRITE DEFAULT-IMAGPART))
 (5 5 (:REWRITE DEFAULT-DENOMINATOR))
 (5 5 (:REWRITE DEFAULT-COERCE-2))
 (5 5 (:REWRITE DEFAULT-COERCE-1))
 )
(APPLY$-WARRANT-PSTERMP-INDUCTOR)
(APPLY$-WARRANT-PSTERMP-INDUCTOR-DEFINITION)
(APPLY$-WARRANT-PSTERMP-INDUCTOR-NECC)
(APPLY$-PSTERMP-INDUCTOR
 (2 2 (:TYPE-PRESCRIPTION APPLY$-PRIMP))
 (2 2 (:REWRITE DEFAULT-CAR))
 (2 1 (:REWRITE APPLY$-PRIMP-BADGE))
 (2 1 (:REWRITE APPLY$-PRIMITIVE))
 )
(PSTERMP-INDUCTION-RULE)
(PSSUBST
 (92 45 (:REWRITE DEFAULT-+-2))
 (62 45 (:REWRITE DEFAULT-+-1))
 (45 5 (:DEFINITION LENGTH))
 (40 10 (:REWRITE COMMUTATIVITY-OF-+))
 (40 10 (:DEFINITION INTEGER-ABS))
 (33 7 (:DEFINITION LEN))
 (27 2 (:REWRITE STRUCTURE-OF-LOOP$-AS-ELEMENTS-BRIDGE))
 (26 26 (:REWRITE DEFAULT-CDR))
 (24 24 (:REWRITE DEFAULT-CAR))
 (21 1 (:DEFINITION MEMBER-EQUAL))
 (18 1 (:DEFINITION LOOP$-AS))
 (16 2 (:REWRITE TRUE-LIST-LISTP-IMPLIES-TRUE-LISTP-XXX))
 (15 3 (:DEFINITION TRUE-LISTP))
 (14 14 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (13 11 (:REWRITE DEFAULT-<-2))
 (12 12 (:REWRITE FOLD-CONSTS-IN-+))
 (12 11 (:REWRITE DEFAULT-<-1))
 (12 1 (:DEFINITION TRUE-LIST-LISTP))
 (11 11 (:TYPE-PRESCRIPTION LEN))
 (11 1 (:REWRITE NOT-MEMBER-LOOP$-AS-RATIONAL-LISTP-1))
 (10 10 (:REWRITE DEFAULT-UNARY-MINUS))
 (9 1 (:REWRITE NOT-MEMBER-LOOP$-AS-TRUE-LIST-1))
 (8 8 (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
 (7 7 (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
 (7 1 (:DEFINITION RATIONAL-LISTP))
 (6 6 (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
 (6 1 (:DEFINITION CDR-LOOP$-AS-TUPLE))
 (6 1 (:DEFINITION CAR-LOOP$-AS-TUPLE))
 (5 5 (:TYPE-PRESCRIPTION TRUE-LIST-LISTP))
 (5 5 (:TYPE-PRESCRIPTION RATIONAL-LISTP))
 (5 5 (:REWRITE INTEGERP==>NUMERATOR-=-X))
 (5 5 (:REWRITE INTEGERP==>DENOMINATOR-=-1))
 (5 5 (:REWRITE DEFAULT-REALPART))
 (5 5 (:REWRITE DEFAULT-NUMERATOR))
 (5 5 (:REWRITE DEFAULT-IMAGPART))
 (5 5 (:REWRITE DEFAULT-DENOMINATOR))
 (5 5 (:REWRITE DEFAULT-COERCE-2))
 (5 5 (:REWRITE DEFAULT-COERCE-1))
 (5 1 (:REWRITE NOT-MEMBER-LOOP$-AS-ACL2-NUMBER-1))
 (5 1 (:DEFINITION EMPTY-LOOP$-AS-TUPLEP))
 (4 4 (:REWRITE CDR-CONS))
 (4 4 (:LINEAR MEMBER-EQUAL-ACL2-COUNT-SMALLER-3))
 (3 3 (:REWRITE CAR-CONS))
 (3 3 (:LINEAR MEMBER-EQUAL-ACL2-COUNT-SMALLER-2))
 (3 1 (:REWRITE NOT-MEMBER-LOOP$-AS-SYMBOL-1))
 (3 1 (:REWRITE NOT-MEMBER-LOOP$-AS-RATIONAL-1))
 (3 1 (:REWRITE NOT-MEMBER-LOOP$-AS-INTEGER-1))
 (3 1 (:REWRITE EQUAL-LEN-1))
 (2 2 (:REWRITE ALWAYS$-P-LST-IMPLIES-P-ELEMENT-COROLLARY))
 (2 1 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (2 1 (:REWRITE NOT-MEMBER-LOOP$-AS-IDENTITY-1))
 (1 1 (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
 (1 1 (:REWRITE NOT-MEMBER-LOOP$-AS-GENERAL))
 (1 1 (:REWRITE NOT-MEMBER-LOOP$-AS-ALWAYS$-1))
 (1 1 (:REWRITE ACL2-NUMBER-LISTP-IMPLIES-ACL2-NUMBERP))
 )
(APPLY$-WARRANT-PSSUBST)
(APPLY$-WARRANT-PSSUBST-DEFINITION)
(APPLY$-WARRANT-PSSUBST-NECC)
(APPLY$-PSSUBST
 (22 22 (:TYPE-PRESCRIPTION PSSUBST))
 (6 6 (:REWRITE DEFAULT-CDR))
 (6 6 (:REWRITE DEFAULT-CAR))
 (2 2 (:TYPE-PRESCRIPTION APPLY$-PRIMP))
 (2 1 (:REWRITE APPLY$-PRIMP-BADGE))
 (2 1 (:REWRITE APPLY$-PRIMITIVE))
 )
(PSSUBST-INDUCTOR)
(APPLY$-WARRANT-PSSUBST-INDUCTOR)
(APPLY$-WARRANT-PSSUBST-INDUCTOR-DEFINITION)
(APPLY$-WARRANT-PSSUBST-INDUCTOR-NECC)
(APPLY$-PSSUBST-INDUCTOR
 (22 22 (:TYPE-PRESCRIPTION PSSUBST-INDUCTOR))
 (6 6 (:REWRITE DEFAULT-CDR))
 (6 6 (:REWRITE DEFAULT-CAR))
 (2 2 (:TYPE-PRESCRIPTION APPLY$-PRIMP))
 (2 1 (:REWRITE APPLY$-PRIMP-BADGE))
 (2 1 (:REWRITE APPLY$-PRIMITIVE))
 )
(PSSUBST-INDUCTION-RULE)
(PSTERMP-PSSUBST-[1]
 (2776088 2721719 (:REWRITE DEFAULT-CAR))
 (2088042 2050993 (:REWRITE DEFAULT-CDR))
 (1372450 10813 (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-1))
 (48316 24158 (:REWRITE DEFAULT-+-2))
 (47255 23855 (:REWRITE APPLY$-PRIMITIVE))
 (28731 28731 (:TYPE-PRESCRIPTION PSSUBST))
 (24158 24158 (:REWRITE DEFAULT-+-1))
 (23570 23570 (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
 (22270 22270 (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-3))
 (20686 20686 (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-2))
 (16286 16286 (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
 (5477 5477 (:REWRITE DEFAULT-COERCE-2))
 (5477 5477 (:REWRITE DEFAULT-COERCE-1))
 (3194 634 (:REWRITE APPLY$-BADGEP-PROPERTIES . 3))
 (1965 647 (:DEFINITION APPLY$-BADGEP))
 (1443 1443 (:REWRITE APPLY$-WARRANT-PSSUBST-NECC))
 (1435 1435 (:REWRITE APPLY$-WARRANT-PSTERMP-NECC))
 (1306 647 (:DEFINITION WEAK-APPLY$-BADGE-P))
 (647 647 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
 (65 13 (:LINEAR APPLY$-BADGEP-PROPERTIES . 1))
 )
(PSTERMP-PSSUBST-[2]
 (5367365 13835 (:DEFINITION COLLECT$+))
 (2740015 2683981 (:REWRITE DEFAULT-CAR))
 (2061194 2023144 (:REWRITE DEFAULT-CDR))
 (1371070 11148 (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-1))
 (47388 23694 (:REWRITE DEFAULT-+-2))
 (46476 23238 (:REWRITE APPLY$-PRIMITIVE))
 (27919 27919 (:TYPE-PRESCRIPTION PSSUBST))
 (23694 23694 (:REWRITE DEFAULT-+-1))
 (23096 23096 (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
 (22937 22937 (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-3))
 (21400 21400 (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-2))
 (16119 16119 (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
 (5351 5351 (:REWRITE DEFAULT-COERCE-2))
 (5351 5351 (:REWRITE DEFAULT-COERCE-1))
 (3282 650 (:REWRITE APPLY$-BADGEP-PROPERTIES . 3))
 (2021 663 (:DEFINITION APPLY$-BADGEP))
 (1409 1409 (:REWRITE APPLY$-WARRANT-PSSUBST-NECC))
 (1393 1393 (:REWRITE APPLY$-WARRANT-PSTERMP-NECC))
 (1342 663 (:DEFINITION WEAK-APPLY$-BADGE-P))
 (663 663 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
 (65 13 (:LINEAR APPLY$-BADGEP-PROPERTIES . 1))
 )
(PSTERMP-PSSUBST-[1]-WITHOUT-COMPOSE-RULES
 (1031609 16239 (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-1))
 (720805 716948 (:REWRITE DEFAULT-CAR))
 (577445 574353 (:REWRITE DEFAULT-CDR))
 (31140 15570 (:REWRITE DEFAULT-+-2))
 (28274 28274 (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-3))
 (26554 26554 (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-2))
 (25016 12513 (:REWRITE APPLY$-PRIMITIVE))
 (15570 15570 (:REWRITE DEFAULT-+-1))
 (15248 15248 (:TYPE-PRESCRIPTION PSSUBST))
 (15086 15086 (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
 (10363 10363 (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
 (3418 3418 (:REWRITE DEFAULT-COERCE-2))
 (3418 3418 (:REWRITE DEFAULT-COERCE-1))
 (2324 460 (:REWRITE APPLY$-BADGEP-PROPERTIES . 3))
 (1930 10 (:REWRITE COLLECT$+-SINGLETON))
 (1407 461 (:DEFINITION APPLY$-BADGEP))
 (940 940 (:REWRITE APPLY$-WARRANT-PSSUBST-NECC))
 (934 461 (:DEFINITION WEAK-APPLY$-BADGE-P))
 (932 932 (:REWRITE APPLY$-WARRANT-PSTERMP-NECC))
 (461 461 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
 (5 1 (:LINEAR APPLY$-BADGEP-PROPERTIES . 1))
 )
(PSOCCUR
 (92 45 (:REWRITE DEFAULT-+-2))
 (62 45 (:REWRITE DEFAULT-+-1))
 (45 5 (:DEFINITION LENGTH))
 (40 10 (:REWRITE COMMUTATIVITY-OF-+))
 (40 10 (:DEFINITION INTEGER-ABS))
 (33 7 (:DEFINITION LEN))
 (27 2 (:REWRITE STRUCTURE-OF-LOOP$-AS-ELEMENTS-BRIDGE))
 (26 26 (:REWRITE DEFAULT-CDR))
 (24 24 (:REWRITE DEFAULT-CAR))
 (21 1 (:DEFINITION MEMBER-EQUAL))
 (18 1 (:DEFINITION LOOP$-AS))
 (16 2 (:REWRITE TRUE-LIST-LISTP-IMPLIES-TRUE-LISTP-XXX))
 (15 3 (:DEFINITION TRUE-LISTP))
 (14 14 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (13 11 (:REWRITE DEFAULT-<-2))
 (12 12 (:REWRITE FOLD-CONSTS-IN-+))
 (12 11 (:REWRITE DEFAULT-<-1))
 (12 1 (:DEFINITION TRUE-LIST-LISTP))
 (11 11 (:TYPE-PRESCRIPTION LEN))
 (11 1 (:REWRITE NOT-MEMBER-LOOP$-AS-RATIONAL-LISTP-1))
 (10 10 (:REWRITE DEFAULT-UNARY-MINUS))
 (9 1 (:REWRITE NOT-MEMBER-LOOP$-AS-TRUE-LIST-1))
 (8 8 (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
 (7 7 (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
 (7 1 (:DEFINITION RATIONAL-LISTP))
 (6 6 (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
 (6 1 (:DEFINITION CDR-LOOP$-AS-TUPLE))
 (6 1 (:DEFINITION CAR-LOOP$-AS-TUPLE))
 (5 5 (:TYPE-PRESCRIPTION TRUE-LIST-LISTP))
 (5 5 (:TYPE-PRESCRIPTION RATIONAL-LISTP))
 (5 5 (:REWRITE INTEGERP==>NUMERATOR-=-X))
 (5 5 (:REWRITE INTEGERP==>DENOMINATOR-=-1))
 (5 5 (:REWRITE DEFAULT-REALPART))
 (5 5 (:REWRITE DEFAULT-NUMERATOR))
 (5 5 (:REWRITE DEFAULT-IMAGPART))
 (5 5 (:REWRITE DEFAULT-DENOMINATOR))
 (5 5 (:REWRITE DEFAULT-COERCE-2))
 (5 5 (:REWRITE DEFAULT-COERCE-1))
 (5 1 (:REWRITE NOT-MEMBER-LOOP$-AS-ACL2-NUMBER-1))
 (5 1 (:DEFINITION EMPTY-LOOP$-AS-TUPLEP))
 (4 4 (:REWRITE CDR-CONS))
 (4 4 (:LINEAR MEMBER-EQUAL-ACL2-COUNT-SMALLER-3))
 (3 3 (:REWRITE CAR-CONS))
 (3 3 (:LINEAR MEMBER-EQUAL-ACL2-COUNT-SMALLER-2))
 (3 1 (:REWRITE NOT-MEMBER-LOOP$-AS-SYMBOL-1))
 (3 1 (:REWRITE NOT-MEMBER-LOOP$-AS-RATIONAL-1))
 (3 1 (:REWRITE NOT-MEMBER-LOOP$-AS-INTEGER-1))
 (3 1 (:REWRITE EQUAL-LEN-1))
 (2 2 (:REWRITE ALWAYS$-P-LST-IMPLIES-P-ELEMENT-COROLLARY))
 (2 1 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (2 1 (:REWRITE NOT-MEMBER-LOOP$-AS-IDENTITY-1))
 (1 1 (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
 (1 1 (:REWRITE NOT-MEMBER-LOOP$-AS-GENERAL))
 (1 1 (:REWRITE NOT-MEMBER-LOOP$-AS-ALWAYS$-1))
 (1 1 (:REWRITE ACL2-NUMBER-LISTP-IMPLIES-ACL2-NUMBERP))
 )
(APPLY$-WARRANT-PSOCCUR)
(APPLY$-WARRANT-PSOCCUR-DEFINITION)
(APPLY$-WARRANT-PSOCCUR-NECC)
(APPLY$-PSOCCUR
 (4 4 (:REWRITE DEFAULT-CAR))
 (2 2 (:TYPE-PRESCRIPTION APPLY$-PRIMP))
 (2 2 (:REWRITE DEFAULT-CDR))
 (2 1 (:REWRITE APPLY$-PRIMP-BADGE))
 (2 1 (:REWRITE APPLY$-PRIMITIVE))
 )
(PSOCCUR-PSSUBST
 (1099246 3495 (:DEFINITION COLLECT$+))
 (10338 5169 (:REWRITE APPLY$-PRIMITIVE))
 (874 874 (:REWRITE APPLY$-WARRANT-PSSUBST-NECC))
 (874 874 (:REWRITE APPLY$-WARRANT-PSOCCUR-NECC))
 (30 6 (:LINEAR APPLY$-BADGEP-PROPERTIES . 1))
 (18 6 (:DEFINITION APPLY$-BADGEP))
 (12 6 (:DEFINITION WEAK-APPLY$-BADGE-P))
 (6 6 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
 )
