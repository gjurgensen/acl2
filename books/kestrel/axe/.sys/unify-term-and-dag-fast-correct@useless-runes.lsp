(FLAG-LEMMA-FOR-UNIFY-TERM-AND-DAG-ITEM-FAST-CORRECT-HELPER
 (1340 639 (:REWRITE DEFAULT-CAR))
 (1037 163 (:REWRITE USE-ALL-CONSP-FOR-CAR))
 (859 33 (:DEFINITION LENGTH))
 (672 44 (:DEFINITION LEN))
 (546 442 (:REWRITE DEFAULT-CDR))
 (492 492 (:REWRITE USE-ALL-CONSP-2))
 (492 492 (:REWRITE USE-ALL-CONSP))
 (489 163 (:REWRITE CONSP-OF-CAR-WHEN-PSEUDO-DAGP))
 (370 370 (:TYPE-PRESCRIPTION ALL-CONSP))
 (345 11 (:DEFINITION SYMBOL-LISTP))
 (326 326 (:TYPE-PRESCRIPTION PSEUDO-DAGP))
 (326 163 (:REWRITE CONSP-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (297 185 (:REWRITE ALL-CONSP-WHEN-NOT-CONSP))
 (226 226 (:TYPE-PRESCRIPTION SYMBOL-TERM-ALISTP))
 (208 104 (:TYPE-PRESCRIPTION SYMBOLP-OF-CAR-OF-AREF1))
 (185 185 (:REWRITE ALL-CONSP-WHEN-NOT-CONSP-CHEAP))
 (173 173 (:REWRITE CAR-OF-CAR-WHEN-PSEUDO-DAGP-AUX))
 (168 42 (:REWRITE AREF1-WHEN-TOO-LARGE-CHEAP))
 (163 163 (:REWRITE TRUE-LISTP-OF-CAR-WHEN-WHEN-BOUNDED-NATP-ALISTP))
 (163 163 (:REWRITE CONSP-OF-CAR-WHEN-PSEUDO-DAGP-AUX-2))
 (163 163 (:REWRITE CONSP-OF-CAR-WHEN-PSEUDO-DAGP-AUX))
 (153 153 (:TYPE-PRESCRIPTION TYPE-OF-AREF1-WHEN-PSEUDO-DAG-ARRAYP-AUX))
 (120 60 (:REWRITE SYMBOL-ALISTP-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (115 115 (:TYPE-PRESCRIPTION PSEUDO-DAG-ARRAYP-AUX))
 (114 114 (:TYPE-PRESCRIPTION LEN))
 (110 22 (:REWRITE ALL-CONSP-OF-CDR))
 (108 49 (:REWRITE DEFAULT-+-2))
 (104 104 (:TYPE-PRESCRIPTION SYMBOLP-OF-CAR-OF-AREF1-WHEN-PSEUDO-DAG-ARRAYP))
 (99 99 (:REWRITE EQUAL-OF-NON-NATP-AND-CAAR-WHEN-WHEN-BOUNDED-NATP-ALISTP))
 (88 88 (:REWRITE LEN-WHEN-PSEUDO-DAGP-AUX))
 (88 88 (:REWRITE LEN-WHEN-DARGP-LESS-THAN))
 (88 88 (:REWRITE LEN-WHEN-BOUNDED-DAG-EXPRP-AND-QUOTEP))
 (84 42 (:TYPE-PRESCRIPTION ALEN1-TYPE))
 (61 61 (:REWRITE SYMBOLP-WHEN-BOUNDED-DAG-EXPRP))
 (58 58 (:REWRITE SYMBOLP-OF-CAR-WHEN-BOUNDED-DAG-EXPRP))
 (49 49 (:REWRITE DEFAULT-+-1))
 (47 47 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (45 5 (:REWRITE CONSP-OF-DARGS-OF-AREF1-WHEN-PSEUDO-DAG-ARRAYP-SIMPLE-IFF))
 (44 44 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (42 42 (:TYPE-PRESCRIPTION POSP-OF-ALEN1))
 (42 42 (:TYPE-PRESCRIPTION ARRAY1P))
 (38 38 (:REWRITE QUOTE-LEMMA-FOR-BOUNDED-DARG-LISTP-GEN-ALT))
 (33 8 (:REWRITE CAR-OF-DARGS-BECOMES-NTH-0-OF-DARGS))
 (29 4 (:DEFINITION NTH))
 (23 23 (:REWRITE TRUE-LISTP-WHEN-PSEUDO-DAGP-AUX))
 (22 11 (:TYPE-PRESCRIPTION TRUE-LISTP-OF-DARGS-OF-AREF1-WHEN-PSEUDO-DAG-ARRAYP-SIMPLE))
 (22 11 (:TYPE-PRESCRIPTION TRUE-LISTP-OF-DARGS-OF-AREF1-WHEN-PSEUDO-DAG-ARRAYP-AUX-SIMPLE))
 (21 21 (:TYPE-PRESCRIPTION PSEUDO-DAG-ARRAYP))
 (17 17 (:REWRITE TRUE-LISTP-OF-CAR-WHEN-BOUNDED-DARG-LISTP))
 (15 15 (:TYPE-PRESCRIPTION SYMBOL-LISTP))
 (15 5 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (11 11 (:TYPE-PRESCRIPTION TRUE-LISTP-OF-DARGS-OF-AREF1-WHEN-PSEUDO-DAG-ARRAYP))
 (11 11 (:REWRITE DEFAULT-COERCE-2))
 (11 11 (:REWRITE DEFAULT-COERCE-1))
 (6 6 (:REWRITE ASSOC-EQUAL-WHEN-PSEUDO-DAGP-AUX))
 (6 3 (:REWRITE IFF-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (5 5 (:REWRITE USE-ALL-RATIONALP-2))
 (5 5 (:REWRITE USE-ALL-RATIONALP))
 (5 5 (:REWRITE PSEUDO-DAG-ARRAYP-MONOTONE))
 (2 2 (:TYPE-PRESCRIPTION TRUE-LISTP))
 )
(UNIFY-TERM-AND-DAG-ITEM-FAST-CORRECT-HELPER)
(UNIFY-TERMS-AND-DAG-ITEMS-FAST-CORRECT-HELPER)
(UNIFY-TERM-AND-DAG-ITEM-FAST-CORRECT
 (160 1 (:DEFINITION PSEUDO-TERMP))
 (77 3 (:DEFINITION LENGTH))
 (60 4 (:DEFINITION LEN))
 (30 1 (:DEFINITION SYMBOL-LISTP))
 (28 2 (:REWRITE USE-ALL-CONSP-FOR-CAR))
 (21 15 (:REWRITE DEFAULT-CAR))
 (18 16 (:REWRITE DEFAULT-CDR))
 (12 12 (:REWRITE USE-ALL-CONSP-2))
 (12 12 (:REWRITE USE-ALL-CONSP))
 (12 4 (:REWRITE ALL-CONSP-WHEN-NOT-CONSP))
 (10 2 (:REWRITE ALL-CONSP-OF-CDR))
 (9 9 (:TYPE-PRESCRIPTION LEN))
 (8 8 (:TYPE-PRESCRIPTION ALL-CONSP))
 (8 8 (:REWRITE LEN-WHEN-PSEUDO-DAGP-AUX))
 (8 8 (:REWRITE LEN-WHEN-DARGP-LESS-THAN))
 (8 8 (:REWRITE LEN-WHEN-BOUNDED-DAG-EXPRP-AND-QUOTEP))
 (8 4 (:REWRITE DEFAULT-+-2))
 (6 2 (:REWRITE CONSP-OF-CAR-WHEN-PSEUDO-DAGP))
 (4 4 (:TYPE-PRESCRIPTION PSEUDO-DAGP))
 (4 4 (:REWRITE DEFAULT-+-1))
 (4 4 (:REWRITE ALL-CONSP-WHEN-NOT-CONSP-CHEAP))
 (4 2 (:REWRITE CONSP-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (3 3 (:REWRITE SYMBOLP-WHEN-BOUNDED-DAG-EXPRP))
 (2 2 (:TYPE-PRESCRIPTION SYMBOL-TERM-ALISTP))
 (2 2 (:REWRITE TRUE-LISTP-WHEN-PSEUDO-DAGP-AUX))
 (2 2 (:REWRITE TRUE-LISTP-OF-CAR-WHEN-WHEN-BOUNDED-NATP-ALISTP))
 (2 2 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (2 2 (:REWRITE SYMBOLP-OF-CAR-WHEN-BOUNDED-DAG-EXPRP))
 (2 2 (:REWRITE CONSP-OF-CAR-WHEN-PSEUDO-DAGP-AUX-2))
 (2 2 (:REWRITE CONSP-OF-CAR-WHEN-PSEUDO-DAGP-AUX))
 (2 2 (:REWRITE CAR-OF-CAR-WHEN-PSEUDO-DAGP-AUX))
 (1 1 (:TYPE-PRESCRIPTION SYMBOL-LISTP))
 (1 1 (:TYPE-PRESCRIPTION PSEUDO-TERM-LISTP))
 (1 1 (:REWRITE TRUE-LISTP-OF-CAR-WHEN-BOUNDED-DARG-LISTP))
 (1 1 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (1 1 (:REWRITE QUOTE-LEMMA-FOR-BOUNDED-DARG-LISTP-GEN-ALT))
 (1 1 (:REWRITE EQUAL-OF-NON-NATP-AND-CAAR-WHEN-WHEN-BOUNDED-NATP-ALISTP))
 (1 1 (:REWRITE DEFAULT-COERCE-2))
 (1 1 (:REWRITE DEFAULT-COERCE-1))
 )
(UNIFY-TERMS-AND-DAG-ITEMS-FAST-CORRECT
 (8 1 (:DEFINITION PSEUDO-TERM-LISTP))
 (2 2 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (1 1 (:TYPE-PRESCRIPTION PSEUDO-TERMP))
 (1 1 (:REWRITE USE-ALL-CONSP-2))
 (1 1 (:REWRITE USE-ALL-CONSP))
 (1 1 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (1 1 (:REWRITE DEFAULT-CDR))
 (1 1 (:REWRITE DEFAULT-CAR))
 )
