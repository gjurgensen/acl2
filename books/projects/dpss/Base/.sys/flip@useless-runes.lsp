(UAV->FLIP)
(T-IMPLIES-UAV-P-UAV->FLIP)
(UAV->FLIP
 (8 8 (:TYPE-PRESCRIPTION NOT-UAV-ID-P-FROM-NOT-ACL2-NUMBERP))
 )
(UAV-EQUIV-1-IMPLIES-EQUAL-UAV->FLIP)
(UAV->ID-UAV->FLIP
 (52 52 (:TYPE-PRESCRIPTION NOT-UAV-ID-P-FROM-NOT-ACL2-NUMBERP))
 (3 1 (:REWRITE UAV-FIX-WHEN-UAV-P))
 (2 2 (:TYPE-PRESCRIPTION UAV-P))
 (2 1 (:REWRITE DEFAULT-UNARY-MINUS))
 (2 1 (:LINEAR POSP-N))
 (1 1 (:TYPE-PRESCRIPTION ACL2-NUMBERP-UAV->DIRECTION))
 (1 1 (:REWRITE UAV-ID-FIX-CONSTANT))
 )
(UAV->DIRECTION-UAV->FLIP
 (3 1 (:REWRITE UAV-FIX-WHEN-UAV-P))
 (2 2 (:TYPE-PRESCRIPTION UAV-P))
 (2 2 (:REWRITE DEFAULT-UNARY-MINUS))
 )
(UAV->LOCATION-UAV->FLIP
 (3 1 (:REWRITE UAV-FIX-WHEN-UAV-P))
 (2 2 (:TYPE-PRESCRIPTION UAV-P))
 (2 1 (:REWRITE DEFAULT-UNARY-MINUS))
 (1 1 (:TYPE-PRESCRIPTION ACL2-NUMBERP-UAV->DIRECTION))
 )
(FLIP-UAV)
(T-T-IMPLIES-UAV-P-FLIP-UAV
 (2 2 (:TYPE-PRESCRIPTION UAV-ID-FIX))
 )
(FLIP-UAV
 (60 60 (:TYPE-PRESCRIPTION UAV-ID-FIX))
 )
(UAV-ID-EQUIV-IMPLIES-EQUAL-FLIP-UAV-1
 (72 72 (:TYPE-PRESCRIPTION UAV-ID-FIX))
 )
(UAV-LIST-EQUIV-IMPLIES-EQUAL-FLIP-UAV-2
 (115 115 (:TYPE-PRESCRIPTION UAV-ID-FIX))
 (32 32 (:TYPE-PRESCRIPTION ACL2-NUMBERP-UAV->DIRECTION))
 (19 4 (:REWRITE WEAK-UAV-ID-FIX-UAV-ID-P))
 (16 2 (:REWRITE POSITIVE-TO-ONE))
 (16 2 (:REWRITE NEGATIVE-DIRECTION-TO-NOT-ONE))
 (13 2 (:REWRITE EVENT-FOR-UAV-RIGHT))
 (13 2 (:REWRITE EVENT-FOR-UAV-N))
 (13 2 (:REWRITE EVENT-FOR-UAV-LEFT))
 (13 2 (:REWRITE EVENT-FOR-UAV-0))
 (12 4 (:REWRITE UAV-ID-FIX-NOT-UAV-ID-P))
 (8 2 (:REWRITE DEGENERATE-EVENT-SCENARIO))
 (6 1 (:DEFINITION OPEN-UAV-LIST-EQUIV))
 (4 4 (:REWRITE UAV-ID-FIX-CONSTANT))
 (4 4 (:REWRITE NORMALIZE-DIRECTION-DIRECTION))
 (3 3 (:REWRITE UAV-ID-P-CONSTANT))
 (2 2 (:REWRITE NEGATE-DIRECTION-EQUALITY-REWRITE-1))
 (2 2 (:REWRITE NEGATE-DIRECTION-EQUALITY-REWRITE-0))
 (2 2 (:REWRITE DEFAULT-CDR))
 (2 2 (:REWRITE DEFAULT-CAR))
 (2 1 (:LINEAR POSP-N))
 (1 1 (:REWRITE UAV-EXTENSIONALITY-REWRITE))
 (1 1 (:REWRITE EQUAL-N-TO-BOUNDED-INEQUALITY-1))
 )
(FLIP-ON-EVENTS-REC
 (56 11 (:REWRITE WEAK-UAV-ID-FIX-UAV-ID-P))
 (33 11 (:REWRITE UAV-ID-FIX-NOT-UAV-ID-P))
 (28 3 (:REWRITE LESS-THAN-ZERO-TO-UAV-ID-EQUIV))
 (11 11 (:REWRITE UAV-ID-FIX-CONSTANT))
 (9 9 (:REWRITE UAV-ID-P-CONSTANT))
 (5 5 (:REWRITE STENGTHEN-INTEGER-LINEAR-UPPER))
 (5 5 (:REWRITE STENGTHEN-INTEGER-LINEAR-LOWER-N))
 (5 5 (:REWRITE STENGTHEN-INTEGER-LINEAR-LOWER))
 (3 3 (:REWRITE POSITIVE-SUM))
 (2 2 (:REWRITE <-C-UAV-ID-FIX-REWRITE-0))
 (1 1 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (1 1 (:REWRITE HELPER-RULE))
 )
(T-T-IMPLIES-TRUE-LISTP-FLIP-ON-EVENTS-REC)
(FLIP-ON-EVENTS-REC
 (1 1 (:TYPE-PRESCRIPTION UAV-ID-FIX))
 )
(LEN-FLIP-ON-EVENTS-REC
 (692 42 (:REWRITE WF-ENSEMBLE-IMPLIES-BODY))
 (662 10 (:REWRITE BODY-IMPLIES-WF-ENSEMBLE))
 (422 13 (:DEFINITION UAV-LIST-P))
 (292 17 (:REWRITE UAV-LIST-P-OF-CDR-WHEN-UAV-LIST-P))
 (127 22 (:REWRITE WEAK-UAV-ID-FIX-UAV-ID-P))
 (100 100 (:TYPE-PRESCRIPTION UAV-LIST-P))
 (95 31 (:REWRITE UAV-LIST-P-WHEN-NOT-CONSP))
 (74 13 (:REWRITE UAV-P-OF-CAR-WHEN-UAV-LIST-P))
 (66 22 (:REWRITE UAV-ID-FIX-NOT-UAV-ID-P))
 (57 19 (:TYPE-PRESCRIPTION TRUE-LISTP-UPDATE-NTH))
 (44 44 (:TYPE-PRESCRIPTION WF-ENSEMBLE))
 (44 23 (:REWRITE DEFAULT-CDR))
 (35 18 (:REWRITE DEFAULT-CAR))
 (28 3 (:REWRITE LESS-THAN-ZERO-TO-UAV-ID-EQUIV))
 (25 5 (:DEFINITION UPDATE-NTH))
 (21 21 (:REWRITE UAV-ID-P-CONSTANT))
 (20 20 (:TYPE-PRESCRIPTION FLIP-UAV))
 (19 19 (:TYPE-PRESCRIPTION UPDATE-NTH))
 (13 13 (:TYPE-PRESCRIPTION UAV-P))
 (12 12 (:REWRITE STENGTHEN-INTEGER-LINEAR-UPPER))
 (12 12 (:REWRITE STENGTHEN-INTEGER-LINEAR-LOWER-N))
 (12 12 (:REWRITE STENGTHEN-INTEGER-LINEAR-LOWER))
 (5 5 (:REWRITE HELPER-RULE))
 (5 5 (:REWRITE <-C-UAV-ID-FIX-REWRITE-0))
 (3 3 (:REWRITE-QUOTED-CONSTANT UAV-LIST-FIX-UNDER-UAV-LIST-EQUIV))
 (3 3 (:REWRITE POSITIVE-SUM))
 (3 1 (:REWRITE UAV-LIST-P-OF-CONS))
 (2 2 (:TYPE-PRESCRIPTION SEQUENTIAL-ID-LIST-P))
 (1 1 (:REWRITE T-T-IMPLIES-UAV-P-FLIP-UAV))
 )
(UAV-LIST-P-UPDATE-NTH
 (1294 175 (:REWRITE WF-ENSEMBLE-IMPLIES-BODY))
 (1137 69 (:REWRITE BODY-IMPLIES-WF-ENSEMBLE))
 (226 226 (:TYPE-PRESCRIPTION WF-ENSEMBLE))
 (66 50 (:REWRITE DEFAULT-CAR))
 (63 47 (:REWRITE DEFAULT-CDR))
 (52 52 (:TYPE-PRESCRIPTION SEQUENTIAL-ID-LIST-P))
 (14 14 (:REWRITE STENGTHEN-INTEGER-LINEAR-UPPER))
 (14 14 (:REWRITE STENGTHEN-INTEGER-LINEAR-LOWER-N))
 (14 14 (:REWRITE STENGTHEN-INTEGER-LINEAR-LOWER))
 (9 9 (:REWRITE ZP-OPEN))
 )
(UAV-LISTP-FLIP-ON-EVENTS-REC
 (361 6 (:DEFINITION UAV-LIST-P))
 (352 27 (:REWRITE WF-ENSEMBLE-IMPLIES-BODY))
 (328 10 (:REWRITE BODY-IMPLIES-WF-ENSEMBLE))
 (169 9 (:REWRITE UAV-LIST-P-OF-CDR-WHEN-UAV-LIST-P))
 (94 94 (:TYPE-PRESCRIPTION UAV-ID-FIX))
 (59 26 (:REWRITE UAV-LIST-P-WHEN-NOT-CONSP))
 (42 6 (:REWRITE UAV-P-OF-CAR-WHEN-UAV-LIST-P))
 (34 34 (:TYPE-PRESCRIPTION WF-ENSEMBLE))
 (33 11 (:REWRITE UAV-ID-FIX-NOT-UAV-ID-P))
 (23 5 (:DEFINITION UPDATE-NTH))
 (21 11 (:REWRITE DEFAULT-CDR))
 (21 11 (:REWRITE DEFAULT-CAR))
 (10 10 (:REWRITE STENGTHEN-INTEGER-LINEAR-UPPER))
 (10 10 (:REWRITE STENGTHEN-INTEGER-LINEAR-LOWER-N))
 (10 10 (:REWRITE STENGTHEN-INTEGER-LINEAR-LOWER))
 (5 5 (:REWRITE HELPER-RULE))
 (5 5 (:REWRITE <-C-UAV-ID-FIX-REWRITE-0))
 (2 2 (:TYPE-PRESCRIPTION SEQUENTIAL-ID-LIST-P))
 (1 1 (:REWRITE UAV-ID-P-PLUS-C))
 (1 1 (:REWRITE UAV-ID-EQUIV-TO-DOUBLE-CONTAINMENT))
 (1 1 (:REWRITE POSITIVE-SUM))
 )
(T-T-IMPLIES-UAV-LIST-P-FLIP-ON-EVENTS-REC)
(NTH-FLIP-ON-EVENTS-REC
 (91 16 (:REWRITE WEAK-UAV-ID-FIX-UAV-ID-P))
 (48 16 (:REWRITE UAV-ID-FIX-NOT-UAV-ID-P))
 (28 3 (:REWRITE LESS-THAN-ZERO-TO-UAV-ID-EQUIV))
 (12 12 (:REWRITE STENGTHEN-INTEGER-LINEAR-UPPER))
 (12 12 (:REWRITE STENGTHEN-INTEGER-LINEAR-LOWER-N))
 (12 12 (:REWRITE STENGTHEN-INTEGER-LINEAR-LOWER))
 (8 7 (:REWRITE DEFAULT-CDR))
 (7 6 (:REWRITE DEFAULT-CAR))
 (6 2 (:DEFINITION UPDATE-NTH))
 (3 3 (:REWRITE UAV-ID-EQUIV-TO-DOUBLE-CONTAINMENT))
 (3 3 (:REWRITE POSITIVE-SUM))
 (1 1 (:REWRITE HELPER-RULE))
 (1 1 (:REWRITE <-C-UAV-ID-FIX-REWRITE-0))
 )
(ITH-UAV-FLIP-ON-EVENTS-REC
 (355 355 (:TYPE-PRESCRIPTION UAV-ID-FIX))
 (48 8 (:REWRITE WEAK-UAV-ID-FIX-UAV-ID-P))
 (42 1 (:DEFINITION FLIP-ON-EVENTS-REC))
 (24 8 (:REWRITE UAV-ID-FIX-NOT-UAV-ID-P))
 (16 1 (:REWRITE ZP-OPEN))
 (8 8 (:REWRITE UAV-ID-P-CONSTANT))
 (8 8 (:REWRITE UAV-ID-FIX-CONSTANT))
 (8 2 (:REWRITE <-C-UAV-ID-FIX-REWRITE-0))
 (5 3 (:REWRITE DEFAULT-CDR))
 (5 3 (:REWRITE DEFAULT-CAR))
 (5 1 (:DEFINITION UPDATE-NTH))
 (2 2 (:REWRITE STENGTHEN-INTEGER-LINEAR-UPPER))
 (2 2 (:REWRITE STENGTHEN-INTEGER-LINEAR-LOWER-N))
 (2 2 (:REWRITE STENGTHEN-INTEGER-LINEAR-LOWER))
 (2 1 (:LINEAR POSP-N))
 (1 1 (:REWRITE-QUOTED-CONSTANT UAV-LIST-FIX-UNDER-UAV-LIST-EQUIV))
 (1 1 (:REWRITE HELPER-RULE))
 )
(FLIP-ON-EVENTS)
(T-IMPLIES-UAV-LIST-P-FLIP-ON-EVENTS)
(FLIP-ON-EVENTS)
(UAV-LIST-EQUIV-1-IMPLIES-EQUAL-FLIP-ON-EVENTS)
(LEN-FLIP-ON-EVENTS)
(ITH-UAV-FLIP-ON-EVENTS
 (316 4 (:DEFINITION UAV-LIST-FIX$INLINE))
 (292 8 (:REWRITE UAV-LIST-FIX-WHEN-UAV-LIST-P))
 (284 4 (:DEFINITION FLIP-ON-EVENTS-REC))
 (268 16 (:DEFINITION UAV-LIST-P))
 (144 32 (:REWRITE WF-ENSEMBLE-IMPLIES-BODY))
 (124 20 (:REWRITE UAV-P-OF-CAR-WHEN-UAV-LIST-P))
 (116 4 (:REWRITE UAV-FIX-WHEN-UAV-P))
 (108 20 (:REWRITE UAV-LIST-P-OF-CDR-WHEN-UAV-LIST-P))
 (92 4 (:REWRITE ZP-OPEN))
 (56 56 (:TYPE-PRESCRIPTION WF-ENSEMBLE))
 (56 28 (:REWRITE BODY-IMPLIES-WF-ENSEMBLE))
 (47 5 (:REWRITE WEAK-UAV-ID-FIX-UAV-ID-P))
 (32 32 (:REWRITE UAV-LIST-P-WHEN-NOT-CONSP))
 (31 26 (:REWRITE DEFAULT-CDR))
 (31 26 (:REWRITE DEFAULT-CAR))
 (29 29 (:REWRITE STENGTHEN-INTEGER-LINEAR-UPPER))
 (29 29 (:REWRITE STENGTHEN-INTEGER-LINEAR-LOWER-N))
 (29 29 (:REWRITE STENGTHEN-INTEGER-LINEAR-LOWER))
 (20 4 (:DEFINITION UPDATE-NTH))
 (15 5 (:REWRITE UAV-ID-FIX-NOT-UAV-ID-P))
 (14 14 (:TYPE-PRESCRIPTION UAV-ID-P))
 (14 14 (:TYPE-PRESCRIPTION NOT-UAV-ID-P-FROM-NOT-ACL2-NUMBERP))
 (7 7 (:REWRITE POSITIVE-SUM))
 (6 6 (:REWRITE UAV-ID-P-CONSTANT))
 (5 5 (:REWRITE UAV-ID-FIX-CONSTANT))
 (4 4 (:REWRITE-QUOTED-CONSTANT UAV-LIST-FIX-UNDER-UAV-LIST-EQUIV))
 (4 4 (:REWRITE OPEN-UAV-LIST-FIX))
 )
(NOT-EXISTS-UAV-WITH-EVENT-FLIP-ON-EVENTS
 (362 46 (:REWRITE WF-ENSEMBLE-IMPLIES-BODY))
 (328 15 (:REWRITE BODY-IMPLIES-WF-ENSEMBLE))
 (260 17 (:DEFINITION UAV-LIST-P))
 (198 21 (:REWRITE UAV-LIST-P-OF-CDR-WHEN-UAV-LIST-P))
 (131 131 (:TYPE-PRESCRIPTION UAV-LIST-P))
 (100 21 (:REWRITE UAV-P-OF-CAR-WHEN-UAV-LIST-P))
 (80 2 (:DEFINITION PICK-A-POINT::UAV-LIST-EQUIV-POINT))
 (66 4 (:REWRITE UAV-FIX-WHEN-UAV-P))
 (38 38 (:REWRITE UAV-LIST-P-WHEN-NOT-CONSP))
 (32 32 (:TYPE-PRESCRIPTION ACL2-NUMBERP-UAV->DIRECTION))
 (31 27 (:REWRITE DEFAULT-CDR))
 (27 23 (:REWRITE DEFAULT-CAR))
 (23 23 (:TYPE-PRESCRIPTION UAV-P))
 (16 2 (:REWRITE POSITIVE-TO-ONE))
 (16 2 (:REWRITE NEGATIVE-DIRECTION-TO-NOT-ONE))
 (12 1 (:REWRITE EVENT-FOR-UAV-RIGHT))
 (12 1 (:REWRITE EVENT-FOR-UAV-N))
 (12 1 (:REWRITE EVENT-FOR-UAV-LEFT))
 (12 1 (:REWRITE EVENT-FOR-UAV-0))
 (8 1 (:REWRITE WEAK-UAV-ID-FIX-UAV-ID-P))
 (7 1 (:REWRITE DEGENERATE-EVENT-SCENARIO))
 (6 3 (:TYPE-PRESCRIPTION NOT-UAV-ID-P-FROM-NOT-ACL2-NUMBERP))
 (4 4 (:TYPE-PRESCRIPTION UAV-FIX$INLINE))
 (4 4 (:REWRITE NORMALIZE-DIRECTION-DIRECTION))
 (4 2 (:LINEAR POSP-N))
 (4 1 (:REWRITE UAV-ID-FIX-NOT-UAV-ID-P))
 (3 3 (:TYPE-PRESCRIPTION PICK-A-POINT::UAV-LIST-EQUIV-POINT))
 (3 3 (:TYPE-PRESCRIPTION UAV-ID-P))
 (3 3 (:REWRITE EQUAL-N-TO-BOUNDED-INEQUALITY-1))
 (2 2 (:REWRITE NEGATE-DIRECTION-EQUALITY-REWRITE-1))
 (2 2 (:REWRITE NEGATE-DIRECTION-EQUALITY-REWRITE-0))
 (1 1 (:REWRITE UAV-ID-P-CONSTANT))
 (1 1 (:REWRITE UAV-ID-FIX-CONSTANT))
 )
(NOT-EXISTS-UAV-WITH-EVENT-FLIP-ON-EVENTS-EQUAL
 (224 31 (:REWRITE WF-ENSEMBLE-IMPLIES-BODY))
 (187 14 (:REWRITE BODY-IMPLIES-WF-ENSEMBLE))
 (187 12 (:DEFINITION UAV-LIST-P))
 (140 2 (:DEFINITION LEN))
 (125 15 (:REWRITE UAV-LIST-P-OF-CDR-WHEN-UAV-LIST-P))
 (79 1 (:DEFINITION UAV-LIST-FIX$INLINE))
 (73 2 (:REWRITE UAV-LIST-FIX-WHEN-UAV-LIST-P))
 (55 13 (:REWRITE UAV-P-OF-CAR-WHEN-UAV-LIST-P))
 (42 42 (:TYPE-PRESCRIPTION WF-ENSEMBLE))
 (29 1 (:REWRITE UAV-FIX-WHEN-UAV-P))
 (26 26 (:REWRITE UAV-LIST-P-WHEN-NOT-CONSP))
 (19 19 (:REWRITE DEFAULT-CDR))
 (17 17 (:REWRITE DEFAULT-CAR))
 (14 14 (:TYPE-PRESCRIPTION UAV-P))
 (4 2 (:LINEAR POSP-N))
 (2 2 (:REWRITE UAV-EXTENSIONALITY-REWRITE))
 (2 2 (:REWRITE EXISTS-UAV-WITH-EVENT-SUFF))
 (2 2 (:REWRITE EQUAL-N-TO-BOUNDED-INEQUALITY-1))
 (2 1 (:REWRITE CDR-OF-UAV-LIST-FIX-X-UNDER-UAV-LIST-EQUIV))
 (2 1 (:REWRITE CAR-OF-UAV-LIST-FIX-X-UNDER-UAV-EQUIV))
 (1 1 (:REWRITE OPEN-UAV-LIST-FIX))
 (1 1 (:REWRITE CONSP-OF-UAV-LIST-FIX))
 )
(UAV-LEFT-BOUNDARY-UAV->FLIP
 (40 40 (:TYPE-PRESCRIPTION NOT-UAV-ID-P-FROM-NOT-ACL2-NUMBERP))
 (3 1 (:REWRITE UAV-FIX-WHEN-UAV-P))
 (2 2 (:TYPE-PRESCRIPTION UAV-P))
 (2 1 (:REWRITE DEFAULT-UNARY-MINUS))
 (2 1 (:LINEAR POSP-N))
 (1 1 (:TYPE-PRESCRIPTION ACL2-NUMBERP-UAV->DIRECTION))
 (1 1 (:REWRITE UAV-ID-FIX-CONSTANT))
 )
(UAV-RIGHT-BOUNDARY-UAV->FLIP
 (40 40 (:TYPE-PRESCRIPTION NOT-UAV-ID-P-FROM-NOT-ACL2-NUMBERP))
 (3 1 (:REWRITE UAV-FIX-WHEN-UAV-P))
 (2 2 (:TYPE-PRESCRIPTION UAV-P))
 (2 1 (:REWRITE DEFAULT-UNARY-MINUS))
 (2 1 (:LINEAR POSP-N))
 (1 1 (:TYPE-PRESCRIPTION ACL2-NUMBERP-UAV->DIRECTION))
 (1 1 (:REWRITE UAV-ID-FIX-CONSTANT))
 )
(UAV->LOCATION-FLIP-AUV
 (62 62 (:TYPE-PRESCRIPTION UAV-ID-FIX))
 (48 48 (:TYPE-PRESCRIPTION ACL2-NUMBERP-UAV->DIRECTION))
 (24 3 (:REWRITE POSITIVE-TO-ONE))
 (24 3 (:REWRITE NEGATIVE-DIRECTION-TO-NOT-ONE))
 (18 3 (:REWRITE WEAK-UAV-ID-FIX-UAV-ID-P))
 (12 1 (:REWRITE EVENT-FOR-UAV-RIGHT))
 (12 1 (:REWRITE EVENT-FOR-UAV-N))
 (12 1 (:REWRITE EVENT-FOR-UAV-LEFT))
 (12 1 (:REWRITE EVENT-FOR-UAV-0))
 (12 1 (:LINEAR LTE-MIN-TIME-TO-IMPENDING-IMPACT-EVENT-BOUNDED-BY-LOCATION-RIGHT))
 (12 1 (:LINEAR LTE-MIN-TIME-TO-IMPENDING-IMPACT-EVENT-BOUNDED-BY-LOCATION-LEFT))
 (9 3 (:REWRITE UAV-ID-FIX-NOT-UAV-ID-P))
 (7 1 (:REWRITE DEGENERATE-EVENT-SCENARIO))
 (6 6 (:REWRITE NORMALIZE-DIRECTION-DIRECTION))
 (3 3 (:REWRITE UAV-ID-P-CONSTANT))
 (3 3 (:REWRITE UAV-ID-FIX-CONSTANT))
 (3 3 (:REWRITE NEGATE-DIRECTION-EQUALITY-REWRITE-1))
 (3 3 (:REWRITE NEGATE-DIRECTION-EQUALITY-REWRITE-0))
 (2 1 (:LINEAR POSP-N))
 (1 1 (:REWRITE RIGHT-PERIMETER-PINCHING))
 (1 1 (:REWRITE EQUAL-N-TO-BOUNDED-INEQUALITY-1))
 )
(UAV->ID-FLIP-AUV
 (62 62 (:TYPE-PRESCRIPTION UAV-ID-FIX))
 (32 32 (:TYPE-PRESCRIPTION ACL2-NUMBERP-UAV->DIRECTION))
 (26 1 (:REWRITE ITH-UAV-ID-IS-I))
 (23 3 (:REWRITE WF-ENSEMBLE-IMPLIES-BODY))
 (20 1 (:REWRITE BODY-IMPLIES-WF-ENSEMBLE))
 (18 3 (:REWRITE WEAK-UAV-ID-FIX-UAV-ID-P))
 (16 2 (:REWRITE POSITIVE-TO-ONE))
 (16 2 (:REWRITE NEGATIVE-DIRECTION-TO-NOT-ONE))
 (14 1 (:DEFINITION UAV-LIST-P))
 (12 1 (:REWRITE EVENT-FOR-UAV-RIGHT))
 (12 1 (:REWRITE EVENT-FOR-UAV-N))
 (12 1 (:REWRITE EVENT-FOR-UAV-LEFT))
 (12 1 (:REWRITE EVENT-FOR-UAV-0))
 (9 3 (:REWRITE UAV-ID-FIX-NOT-UAV-ID-P))
 (7 7 (:TYPE-PRESCRIPTION UAV-LIST-P))
 (7 1 (:REWRITE DEGENERATE-EVENT-SCENARIO))
 (4 4 (:TYPE-PRESCRIPTION WF-ENSEMBLE))
 (4 4 (:REWRITE NORMALIZE-DIRECTION-DIRECTION))
 (3 3 (:REWRITE UAV-ID-P-CONSTANT))
 (3 3 (:REWRITE UAV-ID-FIX-CONSTANT))
 (2 2 (:TYPE-PRESCRIPTION SEQUENTIAL-ID-LIST-P))
 (2 2 (:REWRITE UAV-LIST-P-WHEN-NOT-CONSP))
 (2 2 (:REWRITE NEGATE-DIRECTION-EQUALITY-REWRITE-1))
 (2 2 (:REWRITE NEGATE-DIRECTION-EQUALITY-REWRITE-0))
 (2 1 (:REWRITE UAV-P-OF-CAR-WHEN-UAV-LIST-P))
 (2 1 (:REWRITE UAV-LIST-P-OF-CDR-WHEN-UAV-LIST-P))
 (2 1 (:LINEAR POSP-N))
 (1 1 (:TYPE-PRESCRIPTION UAV-P))
 (1 1 (:REWRITE EQUAL-N-TO-BOUNDED-INEQUALITY-1))
 (1 1 (:REWRITE DEFAULT-CDR))
 (1 1 (:REWRITE DEFAULT-CAR))
 )
(EQUAL-LEN-N-IMPLIES-CONSP
 (9 2 (:REWRITE WF-ENSEMBLE-IMPLIES-BODY))
 (6 1 (:REWRITE BODY-IMPLIES-WF-ENSEMBLE))
 (3 3 (:TYPE-PRESCRIPTION WF-ENSEMBLE))
 (2 1 (:REWRITE UAV-LIST-P-WHEN-NOT-CONSP))
 (2 1 (:LINEAR POSP-N))
 (1 1 (:TYPE-PRESCRIPTION UAV-LIST-P))
 )
(NATP-IMPLIES-NOT-LESS-THAN-ZERO)
(ORDERED-LOCATION-LIST-P-FLIP-ON-EVENTS
 (758 78 (:REWRITE WF-ENSEMBLE-IMPLIES-BODY))
 (728 13 (:REWRITE BODY-IMPLIES-WF-ENSEMBLE))
 (506 16 (:DEFINITION UAV-LIST-P))
 (414 36 (:REWRITE UAV-LIST-P-WHEN-NOT-CONSP))
 (388 41 (:REWRITE EQUAL-LEN-N-IMPLIES-CONSP))
 (274 20 (:REWRITE UAV-LIST-P-OF-CDR-WHEN-UAV-LIST-P))
 (120 120 (:TYPE-PRESCRIPTION UAV-LIST-P))
 (96 96 (:TYPE-PRESCRIPTION ACL2-NUMBERP-UAV->DIRECTION))
 (86 86 (:TYPE-PRESCRIPTION WF-ENSEMBLE))
 (72 6 (:LINEAR LTE-MIN-TIME-TO-IMPENDING-IMPACT-EVENT-BOUNDED-BY-LOCATION-RIGHT))
 (72 6 (:LINEAR LTE-MIN-TIME-TO-IMPENDING-IMPACT-EVENT-BOUNDED-BY-LOCATION-LEFT))
 (48 16 (:REWRITE UAV-P-OF-CAR-WHEN-UAV-LIST-P))
 (48 6 (:REWRITE POSITIVE-TO-ONE))
 (48 6 (:REWRITE NEGATIVE-DIRECTION-TO-NOT-ONE))
 (28 28 (:REWRITE DEFAULT-CDR))
 (26 26 (:REWRITE EQUAL-N-TO-BOUNDED-INEQUALITY-1))
 (16 16 (:TYPE-PRESCRIPTION UAV-P))
 (16 16 (:REWRITE DEFAULT-CAR))
 (12 12 (:REWRITE NORMALIZE-DIRECTION-DIRECTION))
 (12 4 (:REWRITE WHAT-WE-WANT-TO-SAY-ABOUT-<=LOCATION-ALL))
 (8 8 (:TYPE-PRESCRIPTION <=LOCATION-ALL-QUANT))
 (8 8 (:REWRITE RIGHT-PERIMETER-PINCHING))
 (8 4 (:LINEAR POSP-N))
 (6 6 (:REWRITE UAV-ID-FIX-CONSTANT))
 (6 6 (:REWRITE NEGATE-DIRECTION-EQUALITY-REWRITE-1))
 (6 6 (:REWRITE NEGATE-DIRECTION-EQUALITY-REWRITE-0))
 (4 4 (:REWRITE STENGTHEN-INTEGER-LINEAR-UPPER))
 (4 4 (:REWRITE STENGTHEN-INTEGER-LINEAR-LOWER-N))
 (4 4 (:REWRITE STENGTHEN-INTEGER-LINEAR-LOWER))
 (2 2 (:TYPE-PRESCRIPTION SEQUENTIAL-ID-LIST-P))
 )
(SEQUENTIAL-ID-LIST-P-FLIP-ON-EVENTS
 (280 24 (:REWRITE WF-ENSEMBLE-IMPLIES-BODY))
 (268 7 (:REWRITE BODY-IMPLIES-WF-ENSEMBLE))
 (102 7 (:DEFINITION UAV-LIST-P))
 (70 1 (:DEFINITION LEN))
 (68 4 (:DEFINITION SEQUENTIAL-ID-LIST-AUX-P-WITNESS))
 (64 1 (:REWRITE ORDERED-LOCATION-LIST-P-FLIP-ON-EVENTS))
 (62 8 (:REWRITE SEQUENTIAL-ID-LIST-AUX-P-WITNESS-WHEN-SEQUENTIAL))
 (55 8 (:REWRITE UAV-LIST-P-OF-CDR-WHEN-UAV-LIST-P))
 (54 2 (:DEFINITION ORDERED-LOCATION-LIST-P))
 (52 52 (:TYPE-PRESCRIPTION UAV-LIST-P))
 (50 11 (:DEFINITION UAV-FIX!))
 (44 5 (:DEFINITION SEQUENTIAL-ID-LIST-AUX-P))
 (40 9 (:REWRITE UAV-P-OF-CAR-WHEN-UAV-LIST-P))
 (30 30 (:TYPE-PRESCRIPTION WF-ENSEMBLE))
 (30 2 (:REWRITE UAV-FIX-WHEN-UAV-P))
 (21 21 (:REWRITE DEFAULT-CDR))
 (18 18 (:REWRITE DEFAULT-CAR))
 (16 4 (:REWRITE UAV-ID-FIX-NOT-UAV-ID-P))
 (15 15 (:REWRITE UAV-LIST-P-WHEN-NOT-CONSP))
 (12 6 (:TYPE-PRESCRIPTION NOT-UAV-ID-P-FROM-NOT-ACL2-NUMBERP))
 (11 4 (:REWRITE WEAK-UAV-ID-FIX-UAV-ID-P))
 (10 10 (:TYPE-PRESCRIPTION UAV-P))
 (10 10 (:TYPE-PRESCRIPTION ORDERED-LOCATION-LIST-P))
 (9 9 (:REWRITE UAV-FIX-UNDER-UAV-EQUIV))
 (6 6 (:TYPE-PRESCRIPTION UAV-ID-P))
 (6 6 (:TYPE-PRESCRIPTION SEQUENTIAL-ID-LIST-AUX-P-WITNESS))
 (4 4 (:TYPE-PRESCRIPTION <=LOCATION-ALL))
 (4 4 (:REWRITE UAV-ID-FIX-CONSTANT))
 (2 1 (:LINEAR POSP-N))
 (1 1 (:REWRITE UAV-ID-P-CONSTANT))
 (1 1 (:REWRITE EQUAL-N-TO-BOUNDED-INEQUALITY-1))
 )
(ESCORT-CONDITION-FLIP-ON-INVARIANTS-HELPER
 (4755 1585 (:REWRITE UAV-ID-FIX-NOT-UAV-ID-P))
 (2988 274 (:REWRITE LESS-THAN-ZERO-TO-UAV-ID-EQUIV))
 (2236 258 (:REWRITE BODY-IMPLIES-WF-ENSEMBLE))
 (1788 453 (:REWRITE UAV-ID-FIX-UAV-ID-P))
 (1624 327 (:LINEAR LTE-MIN-TIME-TO-IMPENDING-IMPACT-EVENT-BOUNDED-BY-LOCATION-RIGHT))
 (1592 327 (:LINEAR LTE-MIN-TIME-TO-IMPENDING-IMPACT-EVENT-BOUNDED-BY-LOCATION-LEFT))
 (1505 1505 (:REWRITE STENGTHEN-INTEGER-LINEAR-UPPER))
 (1462 86 (:DEFINITION UAV-LIST-P))
 (948 246 (:REWRITE <-C-UAV-ID-FIX-REWRITE-0))
 (860 172 (:REWRITE WF-ENSEMBLE-IMPLIES-BODY))
 (774 774 (:TYPE-PRESCRIPTION UAV-LIST-P))
 (286 286 (:REWRITE NEGATE-DIRECTION-EQUALITY-REWRITE-1))
 (280 280 (:REWRITE NEGATE-DIRECTION-EQUALITY-REWRITE-0))
 (193 193 (:META *META*-UNHIDE-HIDE))
 (174 77 (:REWRITE DEGENERATE-EVENT-SCENARIO))
 (172 172 (:REWRITE UAV-LIST-P-WHEN-NOT-CONSP))
 (172 86 (:REWRITE UAV-P-OF-CAR-WHEN-UAV-LIST-P))
 (172 86 (:REWRITE UAV-LIST-P-OF-CDR-WHEN-UAV-LIST-P))
 (96 33 (:REWRITE DEGENERATE-ZED))
 (86 86 (:TYPE-PRESCRIPTION UAV-P))
 (86 86 (:REWRITE DEFAULT-CDR))
 (86 86 (:REWRITE DEFAULT-CAR))
 (53 53 (:REWRITE EQUAL-N-TO-BOUNDED-INEQUALITY-1))
 (32 8 (:REWRITE UAV-ID-P-PLUS-C))
 (28 19 (:REWRITE DEFAULT-UNARY-MINUS))
 (23 5 (:LINEAR EVENLY-SPACED-BETWEE-PERIMETER-BOUNDARIES))
 (18 18 (:REWRITE PLUS-EQUAL-N-TO-EQUIV-N-MINUS-1))
 (17 17 (:REWRITE <-UAV-ID-FIX-N-REWRITE-2))
 (8 8 (:REWRITE NOT-UAV-ID-P-N))
 )
(ESCORT-CONDITION-FLIP-ON-INVARIANTS
 (78 9 (:REWRITE BODY-IMPLIES-WF-ENSEMBLE))
 (51 3 (:DEFINITION UAV-LIST-P))
 (30 6 (:REWRITE WF-ENSEMBLE-IMPLIES-BODY))
 (27 27 (:TYPE-PRESCRIPTION UAV-LIST-P))
 (6 6 (:REWRITE UAV-LIST-P-WHEN-NOT-CONSP))
 (6 3 (:REWRITE UAV-P-OF-CAR-WHEN-UAV-LIST-P))
 (6 3 (:REWRITE UAV-LIST-P-OF-CDR-WHEN-UAV-LIST-P))
 (6 3 (:LINEAR POSP-N))
 (3 3 (:TYPE-PRESCRIPTION UAV-P))
 (3 3 (:REWRITE DEFAULT-CDR))
 (3 3 (:REWRITE DEFAULT-CAR))
 (1 1 (:REWRITE ESCORT-CONDITION-NECC))
 )
(WF-ENSEMBLE-IMPLIES-ESCORT-CONDITION-FLIP-ON-EVENTS)
(WF-ENSEMBLE-IMPLIES-WF-ENSEMBLE-FLIP-ON-EVENTS
 (17 1 (:DEFINITION UAV-LIST-P))
 (10 2 (:REWRITE WF-ENSEMBLE-IMPLIES-BODY))
 (9 9 (:TYPE-PRESCRIPTION UAV-LIST-P))
 (2 2 (:REWRITE UAV-LIST-P-WHEN-NOT-CONSP))
 (2 1 (:REWRITE UAV-P-OF-CAR-WHEN-UAV-LIST-P))
 (2 1 (:REWRITE UAV-LIST-P-OF-CDR-WHEN-UAV-LIST-P))
 (2 1 (:LINEAR POSP-N))
 (1 1 (:TYPE-PRESCRIPTION UAV-P))
 (1 1 (:REWRITE DEFAULT-CDR))
 (1 1 (:REWRITE DEFAULT-CAR))
 )
(FLIP-ON-EVENTS-INVARIANTS)
(FLIP-ON-EVENTS-ELIMINATES-ALL-EVENTS
 (1144 132 (:REWRITE BODY-IMPLIES-WF-ENSEMBLE))
 (778 84 (:LINEAR LTE-MIN-TIME-TO-IMPENDING-IMPACT-EVENT-BOUNDED-BY-LOCATION-LEFT))
 (770 84 (:LINEAR LTE-MIN-TIME-TO-IMPENDING-IMPACT-EVENT-BOUNDED-BY-LOCATION-RIGHT))
 (748 44 (:DEFINITION UAV-LIST-P))
 (708 236 (:REWRITE UAV-ID-FIX-NOT-UAV-ID-P))
 (541 541 (:REWRITE STENGTHEN-INTEGER-LINEAR-UPPER))
 (476 56 (:REWRITE LESS-THAN-ZERO-TO-UAV-ID-EQUIV))
 (470 19 (:LINEAR EVENLY-SPACED-BOUNDARIES))
 (396 396 (:TYPE-PRESCRIPTION UAV-LIST-P))
 (193 193 (:REWRITE POSITIVE-SUM))
 (120 120 (:REWRITE NEGATE-DIRECTION-EQUALITY-REWRITE-1))
 (107 107 (:REWRITE NEGATE-DIRECTION-EQUALITY-REWRITE-0))
 (88 88 (:REWRITE UAV-LIST-P-WHEN-NOT-CONSP))
 (88 44 (:REWRITE UAV-P-OF-CAR-WHEN-UAV-LIST-P))
 (88 44 (:REWRITE UAV-LIST-P-OF-CDR-WHEN-UAV-LIST-P))
 (62 38 (:REWRITE <-C-UAV-ID-FIX-REWRITE-0))
 (46 29 (:REWRITE DEGENERATE-EVENT-SCENARIO))
 (44 44 (:TYPE-PRESCRIPTION UAV-P))
 (44 44 (:REWRITE DEFAULT-CDR))
 (44 44 (:REWRITE DEFAULT-CAR))
 (43 43 (:META *META*-UNHIDE-HIDE))
 (31 19 (:LINEAR EVENLY-SPACED-BOUNDARIES-CONSTANT))
 (28 28 (:REWRITE EQUAL-N-TO-BOUNDED-INEQUALITY-1))
 (22 22 (:REWRITE HELPER-RULE))
 (20 14 (:REWRITE DEGENERATE-ZED))
 (9 8 (:REWRITE DEFAULT-UNARY-MINUS))
 (9 3 (:LINEAR EVENLY-SPACED-BETWEE-PERIMETER-BOUNDARIES))
 (4 1 (:REWRITE UAV-ID-P-PLUS-C))
 (2 2 (:REWRITE EQUAL-DOUBLE-CONTAINMENT-2))
 (1 1 (:REWRITE NOT-UAV-ID-P-N))
 (1 1 (:REWRITE FORCE-REWRITE-N-CONSTANT-2))
 (1 1 (:REWRITE FORCE-REWRITE-N-CONSTANT-1))
 (1 1 (:REWRITE EXISTS-UAV-WITH-EVENT-SUFF))
 )
(MIN-TIME-TO-IMPACT-FOR-UAV-FLIP-ON-EVENTS-INVARIANT
 (3111 1037 (:REWRITE UAV-ID-FIX-NOT-UAV-ID-P))
 (1581 93 (:DEFINITION UAV-LIST-P))
 (1251 1251 (:REWRITE STENGTHEN-INTEGER-LINEAR-UPPER))
 (1059 271 (:LINEAR LTE-MIN-TIME-TO-IMPENDING-IMPACT-EVENT-BOUNDED-BY-LOCATION-RIGHT))
 (951 271 (:LINEAR LTE-MIN-TIME-TO-IMPENDING-IMPACT-EVENT-BOUNDED-BY-LOCATION-LEFT))
 (740 80 (:REWRITE LESS-THAN-ZERO-TO-UAV-ID-EQUIV))
 (604 153 (:REWRITE DEGENERATE-EVENT-SCENARIO))
 (510 102 (:REWRITE <-C-UAV-ID-FIX-REWRITE-0))
 (382 150 (:REWRITE DEFAULT-UNARY-MINUS))
 (345 115 (:REWRITE WHAT-WE-WANT-TO-SAY-ABOUT-<=LOCATION-ALL))
 (230 230 (:TYPE-PRESCRIPTION <=LOCATION-ALL-QUANT))
 (194 194 (:REWRITE UAV-LIST-P-WHEN-NOT-CONSP))
 (163 103 (:LINEAR EVENLY-SPACED-BOUNDARIES-CONSTANT))
 (156 156 (:META *META*-UNHIDE-HIDE))
 (134 134 (:REWRITE HELPER-RULE))
 (125 125 (:REWRITE EQUAL-N-TO-BOUNDED-INEQUALITY-1))
 (101 101 (:REWRITE DEFAULT-CDR))
 (101 101 (:REWRITE DEFAULT-CAR))
 (93 93 (:REWRITE ESCORT-CONDITION-NECC))
 (78 13 (:REWRITE NOT-EQUAL-INTO-INEQUALITY-1))
 (67 9 (:LINEAR EVENLY-SPACED-BETWEE-PERIMETER-BOUNDARIES))
 (66 11 (:REWRITE DEGENERATE-EQUAL-N-TO-UAV-ID-EQUIV))
 (36 36 (:REWRITE <-UAV-ID-FIX-N-REWRITE-2))
 (32 32 (:REWRITE DEGENERATE-ZED))
 (32 14 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (22 22 (:REWRITE PLUS-EQUAL-N-TO-EQUIV-N-MINUS-1))
 (12 12 (:REWRITE IMPLIES-RATIONALP-LEFT-PERIMETER-BOUNDARY))
 (1 1 (:REWRITE UAV-ID-P-PLUS-C))
 )
(IMPENDING-EVENT-FOR-UAV-STILL-IMPENDING-FLIP-ON-EVENTS
 (5102 1681 (:REWRITE UAV-ID-FIX-NOT-UAV-ID-P))
 (3468 204 (:DEFINITION UAV-LIST-P))
 (2922 2922 (:REWRITE STENGTHEN-INTEGER-LINEAR-UPPER))
 (1829 223 (:REWRITE LESS-THAN-ZERO-TO-UAV-ID-EQUIV))
 (965 535 (:LINEAR LTE-MIN-TIME-TO-IMPENDING-IMPACT-EVENT-BOUNDED-BY-LOCATION-RIGHT))
 (947 535 (:LINEAR LTE-MIN-TIME-TO-IMPENDING-IMPACT-EVENT-BOUNDED-BY-LOCATION-LEFT))
 (684 228 (:REWRITE WHAT-WE-WANT-TO-SAY-ABOUT-<=LOCATION-ALL))
 (496 496 (:META *META*-UNHIDE-HIDE))
 (482 162 (:REWRITE <-C-UAV-ID-FIX-REWRITE-0))
 (456 456 (:TYPE-PRESCRIPTION <=LOCATION-ALL-QUANT))
 (432 432 (:REWRITE UAV-LIST-P-WHEN-NOT-CONSP))
 (400 400 (:REWRITE NEGATE-DIRECTION-EQUALITY-REWRITE-1))
 (302 302 (:REWRITE HELPER-RULE))
 (228 228 (:REWRITE DEFAULT-CDR))
 (228 228 (:REWRITE DEFAULT-CAR))
 (204 204 (:REWRITE ESCORT-CONDITION-NECC))
 (144 24 (:REWRITE NOT-EQUAL-INTO-INEQUALITY-1))
 (140 34 (:DEFINITION =))
 (136 94 (:REWRITE DEGENERATE-EVENT-SCENARIO))
 (134 134 (:REWRITE EQUAL-N-TO-BOUNDED-INEQUALITY-1))
 (97 34 (:LINEAR EVENLY-SPACED-BETWEE-PERIMETER-BOUNDARIES))
 (53 53 (:REWRITE <-UAV-ID-FIX-N-REWRITE-2))
 (38 1 (:REWRITE AVERAGE-LOWER-BOUND))
 (8 2 (:REWRITE UAV-ID-P-PLUS-C))
 (6 6 (:REWRITE EQUAL-DOUBLE-CONTAINMENT-2))
 (3 3 (:REWRITE FORCE-REWRITE-N-CONSTANT-2))
 (3 3 (:REWRITE FORCE-REWRITE-N-CONSTANT-1))
 (1 1 (:REWRITE DEGENERATE-FIX-N))
 )
(NOT-ESCORT-FOR-UAV-FLIP-ON-EVENTS-INVARIANT
 (2132 709 (:REWRITE UAV-ID-FIX-NOT-UAV-ID-P))
 (1459 1459 (:REWRITE STENGTHEN-INTEGER-LINEAR-UPPER))
 (1018 137 (:REWRITE LESS-THAN-ZERO-TO-UAV-ID-EQUIV))
 (889 205 (:LINEAR LTE-MIN-TIME-TO-IMPENDING-IMPACT-EVENT-BOUNDED-BY-LOCATION-RIGHT))
 (865 205 (:LINEAR LTE-MIN-TIME-TO-IMPENDING-IMPACT-EVENT-BOUNDED-BY-LOCATION-LEFT))
 (731 43 (:DEFINITION UAV-LIST-P))
 (252 21 (:REWRITE EVENT-FOR-UAV-RIGHT))
 (252 21 (:REWRITE EVENT-FOR-UAV-N))
 (252 21 (:REWRITE EVENT-FOR-UAV-LEFT))
 (252 21 (:REWRITE EVENT-FOR-UAV-0))
 (194 194 (:REWRITE NEGATE-DIRECTION-EQUALITY-REWRITE-1))
 (194 194 (:REWRITE NEGATE-DIRECTION-EQUALITY-REWRITE-0))
 (193 182 (:REWRITE DEGENERATE-ZED))
 (178 178 (:META *META*-UNHIDE-HIDE))
 (135 135 (:REWRITE HELPER-RULE))
 (127 59 (:REWRITE <-C-UAV-ID-FIX-REWRITE-0))
 (87 87 (:REWRITE UAV-LIST-P-WHEN-NOT-CONSP))
 (72 12 (:REWRITE NOT-EQUAL-INTO-INEQUALITY-1))
 (57 19 (:REWRITE WHAT-WE-WANT-TO-SAY-ABOUT-<=LOCATION-ALL))
 (56 56 (:REWRITE EQUAL-N-TO-BOUNDED-INEQUALITY-1))
 (44 44 (:REWRITE DEFAULT-CDR))
 (44 44 (:REWRITE DEFAULT-CAR))
 (43 43 (:REWRITE ESCORT-CONDITION-NECC))
 (38 38 (:TYPE-PRESCRIPTION <=LOCATION-ALL-QUANT))
 (38 21 (:REWRITE DEGENERATE-EVENT-SCENARIO))
 (10 10 (:REWRITE <-UAV-ID-FIX-N-REWRITE-2))
 (7 7 (:REWRITE EQUAL-DOUBLE-CONTAINMENT-2))
 (6 6 (:REWRITE FORCE-REWRITE-N-CONSTANT-2))
 )
(WITHOUT-SUBSUMPTION-DISABLE-QUICK-AND-DIRTY)
(NOT-EVENT-FOR-UAV-FLIP-ON-EVENTS-INVARIANT
 (1077 359 (:REWRITE UAV-ID-FIX-NOT-UAV-ID-P))
 (901 53 (:DEFINITION UAV-LIST-P))
 (851 851 (:REWRITE STENGTHEN-INTEGER-LINEAR-UPPER))
 (606 100 (:LINEAR LTE-MIN-TIME-TO-IMPENDING-IMPACT-EVENT-BOUNDED-BY-LOCATION-RIGHT))
 (606 100 (:LINEAR LTE-MIN-TIME-TO-IMPENDING-IMPACT-EVENT-BOUNDED-BY-LOCATION-LEFT))
 (604 75 (:REWRITE LESS-THAN-ZERO-TO-UAV-ID-EQUIV))
 (477 477 (:TYPE-PRESCRIPTION UAV-LIST-P))
 (233 105 (:REWRITE DEGENERATE-EVENT-SCENARIO))
 (220 220 (:REWRITE NEGATE-DIRECTION-EQUALITY-REWRITE-0))
 (219 219 (:REWRITE NEGATE-DIRECTION-EQUALITY-REWRITE-1))
 (180 52 (:REWRITE <-C-UAV-ID-FIX-REWRITE-0))
 (117 89 (:LINEAR EVENLY-SPACED-BOUNDARIES-CONSTANT))
 (106 106 (:REWRITE UAV-LIST-P-WHEN-NOT-CONSP))
 (106 53 (:REWRITE UAV-P-OF-CAR-WHEN-UAV-LIST-P))
 (106 53 (:REWRITE UAV-LIST-P-OF-CDR-WHEN-UAV-LIST-P))
 (54 54 (:REWRITE HELPER-RULE))
 (53 53 (:TYPE-PRESCRIPTION UAV-P))
 (53 53 (:REWRITE ESCORT-CONDITION-NECC))
 (53 53 (:REWRITE DEFAULT-CDR))
 (53 53 (:REWRITE DEFAULT-CAR))
 (51 51 (:META *META*-UNHIDE-HIDE))
 (43 43 (:REWRITE EQUAL-N-TO-BOUNDED-INEQUALITY-1))
 (41 35 (:REWRITE DEGENERATE-ZED))
 (22 11 (:REWRITE DEFAULT-UNARY-MINUS))
 (21 7 (:LINEAR EVENLY-SPACED-BETWEE-PERIMETER-BOUNDARIES))
 (18 6 (:REWRITE WHAT-WE-WANT-TO-SAY-ABOUT-<=LOCATION-ALL))
 (16 16 (:REWRITE <-UAV-ID-FIX-N-REWRITE-2))
 (12 12 (:TYPE-PRESCRIPTION <=LOCATION-ALL-QUANT))
 (12 3 (:REWRITE CLEAN-UP-EQUALITY))
 )
(NOT-IMPACT-EVENT-FOR-UAV-FLIP-ON-EVENTS-INVARIANT
 (101 101 (:TYPE-PRESCRIPTION UAV-ID-FIX))
 (28 4 (:REWRITE BODY-IMPLIES-WF-ENSEMBLE))
 (18 3 (:REWRITE WEAK-UAV-ID-FIX-UAV-ID-P))
 (17 1 (:DEFINITION UAV-LIST-P))
 (15 3 (:REWRITE WF-ENSEMBLE-IMPLIES-BODY))
 (9 3 (:REWRITE UAV-ID-FIX-NOT-UAV-ID-P))
 (3 3 (:REWRITE UAV-LIST-P-WHEN-NOT-CONSP))
 (3 3 (:REWRITE UAV-ID-P-CONSTANT))
 (3 3 (:REWRITE UAV-ID-FIX-CONSTANT))
 (2 2 (:REWRITE DEFAULT-CDR))
 (2 2 (:REWRITE DEFAULT-CAR))
 (2 1 (:LINEAR POSP-N))
 (1 1 (:REWRITE ESCORT-CONDITION-NECC))
 )
(IMPENDING-ESCORT-FOR-UAV-STILL-IMPENDING-FLIP-ON-EVENTS
 (1305 51 (:LINEAR AVERAGE-UPPER-BOUND))
 (1305 51 (:LINEAR AVERAGE-LOWER-BOUND))
 (1204 142 (:REWRITE BODY-IMPLIES-WF-ENSEMBLE))
 (1107 369 (:REWRITE UAV-ID-FIX-NOT-UAV-ID-P))
 (782 46 (:DEFINITION UAV-LIST-P))
 (501 501 (:REWRITE STENGTHEN-INTEGER-LINEAR-UPPER))
 (480 96 (:REWRITE WF-ENSEMBLE-IMPLIES-BODY))
 (426 29 (:REWRITE EVENT-FOR-UAV-N))
 (412 42 (:REWRITE LESS-THAN-ZERO-TO-UAV-ID-EQUIV))
 (250 29 (:REWRITE EVENT-FOR-UAV-0))
 (234 78 (:REWRITE WHAT-WE-WANT-TO-SAY-ABOUT-<=LOCATION-ALL))
 (233 233 (:REWRITE RIGHT-PERIMETER-PINCHING))
 (190 26 (:REWRITE <-C-UAV-ID-FIX-REWRITE-0))
 (156 156 (:TYPE-PRESCRIPTION <=LOCATION-ALL-QUANT))
 (122 102 (:LINEAR LTE-MIN-TIME-TO-IMPENDING-IMPACT-EVENT-BOUNDED-BY-LOCATION-RIGHT))
 (112 10 (:DEFINITION =))
 (107 102 (:LINEAR LTE-MIN-TIME-TO-IMPENDING-IMPACT-EVENT-BOUNDED-BY-LOCATION-LEFT))
 (104 29 (:REWRITE DEGENERATE-EVENT-SCENARIO))
 (102 102 (:META *META*-UNHIDE-HIDE))
 (96 96 (:REWRITE UAV-LIST-P-WHEN-NOT-CONSP))
 (83 83 (:REWRITE NEGATE-DIRECTION-EQUALITY-REWRITE-1))
 (82 54 (:LINEAR EVENLY-SPACED-BOUNDARIES-CONSTANT))
 (74 17 (:REWRITE DEGENERATE-ZED))
 (50 50 (:REWRITE DEFAULT-CDR))
 (50 50 (:REWRITE DEFAULT-CAR))
 (46 46 (:REWRITE ESCORT-CONDITION-NECC))
 (38 38 (:REWRITE EQUAL-N-TO-BOUNDED-INEQUALITY-1))
 (30 4 (:LINEAR EVENLY-SPACED-BETWEE-PERIMETER-BOUNDARIES))
 (26 26 (:REWRITE HELPER-RULE))
 (15 15 (:REWRITE <-UAV-ID-FIX-N-REWRITE-2))
 (4 4 (:REWRITE PLUS-EQUAL-N-TO-EQUIV-N-MINUS-1))
 (4 1 (:REWRITE UAV-ID-P-PLUS-C))
 (1 1 (:REWRITE NOT-UAV-ID-P-N))
 )
(IMPENDING-IMPACT-EVENT-FOR-UAV-FLIP-ON-EVENTS-INVARIANT
 (64 64 (:TYPE-PRESCRIPTION ACL2-NUMBERP-UAV->DIRECTION))
 (32 4 (:REWRITE POSITIVE-TO-ONE))
 (32 4 (:REWRITE NEGATIVE-DIRECTION-TO-NOT-ONE))
 (26 3 (:REWRITE BODY-IMPLIES-WF-ENSEMBLE))
 (24 2 (:REWRITE EVENT-FOR-UAV-RIGHT))
 (24 2 (:REWRITE EVENT-FOR-UAV-N))
 (24 2 (:REWRITE EVENT-FOR-UAV-LEFT))
 (24 2 (:REWRITE EVENT-FOR-UAV-0))
 (17 1 (:DEFINITION UAV-LIST-P))
 (14 2 (:REWRITE DEGENERATE-EVENT-SCENARIO))
 (10 2 (:REWRITE WF-ENSEMBLE-IMPLIES-BODY))
 (9 9 (:TYPE-PRESCRIPTION UAV-LIST-P))
 (8 8 (:REWRITE NORMALIZE-DIRECTION-DIRECTION))
 (4 4 (:REWRITE NEGATE-DIRECTION-EQUALITY-REWRITE-1))
 (4 4 (:REWRITE NEGATE-DIRECTION-EQUALITY-REWRITE-0))
 (2 2 (:REWRITE UAV-LIST-P-WHEN-NOT-CONSP))
 (2 2 (:REWRITE EQUAL-N-TO-BOUNDED-INEQUALITY-1))
 (2 1 (:REWRITE UAV-P-OF-CAR-WHEN-UAV-LIST-P))
 (2 1 (:REWRITE UAV-LIST-P-OF-CDR-WHEN-UAV-LIST-P))
 (2 1 (:LINEAR POSP-N))
 (1 1 (:TYPE-PRESCRIPTION UAV-P))
 (1 1 (:REWRITE ESCORT-CONDITION-NECC))
 (1 1 (:REWRITE DEFAULT-CDR))
 (1 1 (:REWRITE DEFAULT-CAR))
 )
