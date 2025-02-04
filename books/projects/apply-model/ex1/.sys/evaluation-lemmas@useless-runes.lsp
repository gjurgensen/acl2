(MODAPP::BADGE-IS-BADGE!
 (3 1 (:REWRITE MODAPP::APPLY$-PRIMP-BADGE))
 )
(MODAPP::BOOM
 (1061 485 (:REWRITE DEFAULT-+-2))
 (670 485 (:REWRITE DEFAULT-+-1))
 (395 22 (:REWRITE O<=-O-FINP-DEF))
 (328 82 (:DEFINITION INTEGER-ABS))
 (328 41 (:DEFINITION LENGTH))
 (236 236 (:REWRITE DEFAULT-CDR))
 (227 227 (:REWRITE DEFAULT-CAR))
 (205 41 (:DEFINITION LEN))
 (170 117 (:REWRITE DEFAULT-<-2))
 (152 117 (:REWRITE DEFAULT-<-1))
 (152 38 (:REWRITE O-P-O-INFP-CAR))
 (82 82 (:REWRITE DEFAULT-UNARY-MINUS))
 (81 22 (:REWRITE AC-<))
 (81 13 (:REWRITE O-FIRST-EXPT-<))
 (55 26 (:REWRITE O-FIRST-EXPT-DEF-O-FINP))
 (55 9 (:DEFINITION SYMBOL-LISTP))
 (44 22 (:REWRITE O-INFP-O-FINP-O<=))
 (41 41 (:TYPE-PRESCRIPTION LEN))
 (41 41 (:REWRITE DEFAULT-REALPART))
 (41 41 (:REWRITE DEFAULT-NUMERATOR))
 (41 41 (:REWRITE DEFAULT-IMAGPART))
 (41 41 (:REWRITE DEFAULT-DENOMINATOR))
 (41 41 (:REWRITE DEFAULT-COERCE-2))
 (41 41 (:REWRITE DEFAULT-COERCE-1))
 (29 13 (:REWRITE O-FIRST-COEFF-<))
 (28 7 (:REWRITE MODAPP::APPLY$-BADGEP-PROPERTIES . 1))
 (22 22 (:REWRITE |a < b & b < c  =>  a < c|))
 (14 7 (:DEFINITION MODAPP::APPLY$-BADGEP))
 (10 10 (:REWRITE ZP-OPEN))
 (7 7 (:TYPE-PRESCRIPTION MODAPP::APPLY$-BADGEP))
 )
(FLAG::FLAG-EQUIV-LEMMA)
(MODAPP::BOOM-EQUIVALENCES)
(MODAPP::FLAG-LEMMA-FOR-TAMEP-IS-TAMEP!
 (1529 1529 (:REWRITE DEFAULT-CDR))
 (979 979 (:REWRITE DEFAULT-CAR))
 (856 214 (:REWRITE O-P-O-INFP-CAR))
 (501 69 (:DEFINITION LEN))
 (214 214 (:REWRITE O-P-DEF-O-FINP-1))
 (183 114 (:REWRITE DEFAULT-+-2))
 (136 37 (:REWRITE ZP-OPEN))
 (114 114 (:REWRITE DEFAULT-+-1))
 (111 111 (:TYPE-PRESCRIPTION LEN))
 (33 21 (:REWRITE DEFAULT-<-2))
 (30 30 (:REWRITE DEFAULT-COERCE-2))
 (30 30 (:REWRITE DEFAULT-COERCE-1))
 (27 9 (:REWRITE FOLD-CONSTS-IN-+))
 (21 21 (:REWRITE DEFAULT-<-1))
 (6 6 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (6 6 (:REWRITE MODAPP::APPLY$-BADGEP-PROPERTIES . 1))
 )
(MODAPP::TAMEP-IS-TAMEP!)
(MODAPP::TAMEP-FUNCTIONP-IS-TAMEP-FUNCTIONP!)
(MODAPP::SUITABLY-TAMEP-LISTP-IS-SUITABLY-TAMEP-LISTP!)
(MODAPP::BANG
 (64179 30818 (:REWRITE DEFAULT-+-2))
 (41569 30818 (:REWRITE DEFAULT-+-1))
 (27085 3272 (:DEFINITION LENGTH))
 (25368 6342 (:DEFINITION INTEGER-ABS))
 (18683 3605 (:REWRITE O-P-O-INFP-CAR))
 (12770 9908 (:REWRITE DEFAULT-<-1))
 (11858 9908 (:REWRITE DEFAULT-<-2))
 (8806 103 (:REWRITE MODAPP::APPLY$-BADGEP-PROPERTIES . 1))
 (8660 73 (:DEFINITION MODAPP::APPLY$-BADGEP))
 (7906 3586 (:REWRITE O-P-DEF-O-FINP-1))
 (6342 6342 (:REWRITE DEFAULT-UNARY-MINUS))
 (5100 60 (:REWRITE MODAPP::TAMEP-IMPLICANT-1))
 (4980 60 (:REWRITE MODAPP::TAMEP-IS-TAMEP!))
 (4320 4320 (:TYPE-PRESCRIPTION O-FINP))
 (3624 492 (:DEFINITION SYMBOL-LISTP))
 (3272 3272 (:REWRITE DEFAULT-COERCE-2))
 (3272 3272 (:REWRITE DEFAULT-COERCE-1))
 (3171 3171 (:REWRITE DEFAULT-REALPART))
 (3171 3171 (:REWRITE DEFAULT-NUMERATOR))
 (3171 3171 (:REWRITE DEFAULT-IMAGPART))
 (3171 3171 (:REWRITE DEFAULT-DENOMINATOR))
 (2760 30 (:DEFINITION TRUE-LISTP))
 (2548 364 (:DEFINITION MODAPP::NATS))
 (1456 364 (:REWRITE ZP-OPEN))
 (1314 30 (:DEFINITION SUBSETP-EQUAL))
 (1134 120 (:DEFINITION MEMBER-EQUAL))
 (1128 183 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (283 283 (:TYPE-PRESCRIPTION MODAPP::APPLY$-BADGEP))
 (240 120 (:REWRITE MODAPP::APPLY$-BADGEP-PROPERTIES . 2))
 (223 31 (:DEFINITION NATP))
 (180 180 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 (180 30 (:DEFINITION ALL-NILS))
 (150 150 (:TYPE-PRESCRIPTION ALL-NILS))
 (120 120 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (120 120 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
 (120 60 (:LINEAR MODAPP::APPLY$-BADGEP-PROPERTIES))
 (97 47 (:REWRITE O-INFP->NEQ-0))
 (64 2 (:TYPE-PRESCRIPTION RETURN-LAST))
 (60 60 (:TYPE-PRESCRIPTION MODAPP::TAMEP))
 (30 30 (:TYPE-PRESCRIPTION BOOLEANP))
 (15 1 (:REWRITE O<=-O-FINP-DEF))
 (14 1 (:REWRITE O-FINP-<))
 (6 1 (:REWRITE O-FIRST-EXPT-<))
 (4 2 (:REWRITE O-FIRST-EXPT-DEF-O-FINP))
 (3 1 (:REWRITE AC-<))
 (2 2 (:TYPE-PRESCRIPTION THROW-NONEXEC-ERROR))
 (2 1 (:REWRITE O-INFP-O-FINP-O<=))
 (2 1 (:REWRITE O-FIRST-COEFF-<))
 (1 1 (:REWRITE |a < b & b < c  =>  a < c|))
 )
(FLAG::FLAG-EQUIV-LEMMA)
(MODAPP::BANG-EQUIVALENCES)
(MODAPP::LEN-PROW
 (78 75 (:REWRITE DEFAULT-CDR))
 (69 35 (:REWRITE DEFAULT-+-2))
 (36 12 (:REWRITE MODAPP::APPLY$-PRIMITIVE))
 (35 35 (:REWRITE DEFAULT-+-1))
 (24 24 (:TYPE-PRESCRIPTION MODAPP::APPLY$-PRIMP))
 (24 24 (:REWRITE DEFAULT-CAR))
 (18 9 (:REWRITE DEFAULT-<-1))
 (17 9 (:REWRITE DEFAULT-<-2))
 )
(MODAPP::FLAG-LEMMA-FOR-APPLY$!-IS-APPLY$
 (123506 115689 (:REWRITE DEFAULT-CDR))
 (68448 63235 (:REWRITE DEFAULT-CAR))
 (64765 14606 (:REWRITE O-P-O-INFP-CAR))
 (35360 4937 (:DEFINITION SYMBOL-LISTP))
 (21003 14578 (:REWRITE O-P-DEF-O-FINP-1))
 (17957 298 (:REWRITE O<=-O-FINP-DEF))
 (12339 6822 (:REWRITE DEFAULT-+-2))
 (8806 1304 (:DEFINITION MODAPP::NATS))
 (7541 6822 (:REWRITE DEFAULT-+-1))
 (6550 1778 (:REWRITE ZP-OPEN))
 (5576 465 (:DEFINITION PAIRLIS$))
 (5174 5174 (:TYPE-PRESCRIPTION O-FINP))
 (3254 374 (:DEFINITION ASSOC-EQUAL))
 (2079 1762 (:REWRITE DEFAULT-<-2))
 (2078 1762 (:REWRITE DEFAULT-<-1))
 (1909 1837 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (1504 305 (:DEFINITION MODAPP::SQUARE))
 (1390 1390 (:REWRITE DEFAULT-COERCE-2))
 (1390 1390 (:REWRITE DEFAULT-COERCE-1))
 (1298 585 (:REWRITE DEFAULT-*-2))
 (1210 569 (:REWRITE DEFAULT-*-1))
 (893 298 (:REWRITE AC-<))
 (770 276 (:REWRITE MODAPP::APPLY$-FOLDR))
 (596 298 (:REWRITE O-INFP-O-FINP-O<=))
 (590 216 (:REWRITE MODAPP::APPLY$-SUMLIST))
 (590 216 (:REWRITE MODAPP::APPLY$-PROW*))
 (590 216 (:REWRITE MODAPP::APPLY$-PROW))
 (590 216 (:REWRITE MODAPP::APPLY$-COLLECT-A))
 (494 494 (:TYPE-PRESCRIPTION MODAPP::APPLY$-WARRANT-FOLDR))
 (462 154 (:REWRITE MODAPP::APPLY$-NATS))
 (406 406 (:META MODAPP::APPLY$-PRIM-META-FN-CORRECT))
 (374 374 (:TYPE-PRESCRIPTION MODAPP::APPLY$-WARRANT-SUMLIST))
 (374 374 (:TYPE-PRESCRIPTION MODAPP::APPLY$-WARRANT-PROW*))
 (374 374 (:TYPE-PRESCRIPTION MODAPP::APPLY$-WARRANT-PROW))
 (374 374 (:TYPE-PRESCRIPTION MODAPP::APPLY$-WARRANT-COLLECT-A))
 (330 8 (:REWRITE MODAPP::APPLY$-BADGEP-PROPERTIES . 1))
 (322 4 (:DEFINITION MODAPP::APPLY$-BADGEP))
 (308 308 (:TYPE-PRESCRIPTION MODAPP::APPLY$-WARRANT-NATS))
 (298 298 (:REWRITE |a < b & b < c  =>  a < c|))
 (189 63 (:REWRITE MODAPP::APPLY$-SUM-OF-PRODUCTS))
 (174 86 (:REWRITE MODAPP::APPLY$-SQUARE))
 (126 126 (:TYPE-PRESCRIPTION MODAPP::APPLY$-WARRANT-SUM-OF-PRODUCTS))
 (116 2 (:DEFINITION SUBSETP-EQUAL))
 (104 8 (:DEFINITION MEMBER-EQUAL))
 (101 101 (:TYPE-PRESCRIPTION ZP))
 (88 88 (:TYPE-PRESCRIPTION MODAPP::APPLY$-WARRANT-SQUARE))
 (36 6 (:REWRITE O-FIRST-EXPT-<))
 (28 4 (:DEFINITION NATP))
 (24 12 (:REWRITE O-FIRST-EXPT-DEF-O-FINP))
 (24 2 (:DEFINITION TRUE-LISTP))
 (22 22 (:TYPE-PRESCRIPTION MODAPP::APPLY$-BADGEP))
 (20 4 (:REWRITE MODAPP::TAMEP-IMPLICANT-1))
 (16 8 (:REWRITE MODAPP::APPLY$-BADGEP-PROPERTIES . 2))
 (14 14 (:DEFINITION ENDP))
 (12 12 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 (12 6 (:REWRITE O-FIRST-COEFF-<))
 (12 6 (:LINEAR MODAPP::APPLY$-BADGEP-PROPERTIES))
 (12 2 (:DEFINITION ALL-NILS))
 (10 10 (:TYPE-PRESCRIPTION ALL-NILS))
 (9 9 (:DEFINITION EQ))
 (8 8 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (8 8 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
 (6 6 (:TYPE-PRESCRIPTION PAIRLIS$))
 (4 4 (:TYPE-PRESCRIPTION BOOLEANP))
 )
(MODAPP::APPLY$!-IS-APPLY$)
(MODAPP::EV$!-IS-EV$)
(MODAPP::EV$!-LIST-IS-EV$-LIST)
(MODAPP::SUMLIST!-IS-SUMLIST)
(MODAPP::FOLDR!-IS-FOLDR)
(MODAPP::PROW!-IS-PROW)
(MODAPP::PROW*!-IS-PROW*)
(MODAPP::COLLECT-A!-IS-COLLECT-A)
(MODAPP::SUM-OF-PRODUCTS!-IS-SUM-OF-PRODUCTS)
(MODAPP::APPLY$-USERFN1!-IS-APPLY$-USERFN)
(MODAPP::APPLY$-LAMBDA!-IS-APPLY$-LAMBDA
 (22 2 (:DEFINITION PAIRLIS$))
 (12 2 (:REWRITE O-P-O-INFP-CAR))
 (10 10 (:REWRITE DEFAULT-CDR))
 (8 8 (:REWRITE DEFAULT-CAR))
 (6 2 (:REWRITE O-P-DEF-O-FINP-1))
 (4 4 (:TYPE-PRESCRIPTION O-P))
 (4 4 (:TYPE-PRESCRIPTION O-FINP))
 (2 2 (:REWRITE MODAPP::EV$-OPENER))
 )
