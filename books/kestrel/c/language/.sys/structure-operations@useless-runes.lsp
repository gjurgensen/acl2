(C::VALUE-STRUCT-READ-AUX
 (10 7 (:REWRITE DEFAULT-CDR))
 (10 7 (:REWRITE DEFAULT-CAR))
 (4 4 (:REWRITE C::IDENTP-WHEN-IN-IDENT-SETP-BINDS-FREE-X))
 (2 2 (:REWRITE SUBSETP-TRANS2))
 (2 2 (:REWRITE SUBSETP-TRANS))
 (1 1 (:REWRITE C::MEMBER-VALUE-LISTP-WHEN-NOT-CONSP))
 )
(C::VALUE-RESULTP-OF-VALUE-STRUCT-READ-AUX
 (66 11 (:REWRITE C::VALUEP-WHEN-VALUE-OPTIONP))
 (36 9 (:REWRITE C::IDENT-FIX-WHEN-IDENTP))
 (33 11 (:REWRITE C::VALUE-OPTIONP-WHEN-VALUEP))
 (32 20 (:REWRITE DEFAULT-CAR))
 (25 13 (:REWRITE DEFAULT-CDR))
 (22 22 (:TYPE-PRESCRIPTION C::VALUE-OPTIONP))
 (20 20 (:REWRITE C::VALUEP-WHEN-MEMBER-EQUAL-OF-VALUE-LISTP))
 (18 18 (:TYPE-PRESCRIPTION C::IDENTP))
 (9 9 (:REWRITE C::IDENTP-WHEN-IN-IDENT-SETP-BINDS-FREE-X))
 )
(C::LEMMA
 (1057 10 (:REWRITE C::TYPEP-WHEN-TYPE-OPTIONP))
 (336 336 (:TYPE-PRESCRIPTION C::TYPE-KIND$INLINE))
 (284 198 (:REWRITE DEFAULT-CAR))
 (238 158 (:REWRITE DEFAULT-CDR))
 (216 24 (:REWRITE C::CDR-OF-MEMBER-TYPES-OF-MEMBER-VALUES))
 (168 48 (:REWRITE C::CAR-OF-MEMBER-TYPES-OF-MEMBER-VALUES))
 (56 28 (:REWRITE C::TYPE-FIX-WHEN-VOID))
 (56 28 (:REWRITE C::TYPE-FIX-WHEN-USHORT))
 (56 28 (:REWRITE C::TYPE-FIX-WHEN-ULONG))
 (56 28 (:REWRITE C::TYPE-FIX-WHEN-ULLONG))
 (56 28 (:REWRITE C::TYPE-FIX-WHEN-UINT))
 (56 28 (:REWRITE C::TYPE-FIX-WHEN-UCHAR))
 (56 28 (:REWRITE C::TYPE-FIX-WHEN-SSHORT))
 (56 28 (:REWRITE C::TYPE-FIX-WHEN-SLONG))
 (56 28 (:REWRITE C::TYPE-FIX-WHEN-SLLONG))
 (56 28 (:REWRITE C::TYPE-FIX-WHEN-SINT))
 (56 28 (:REWRITE C::TYPE-FIX-WHEN-SCHAR))
 (56 28 (:REWRITE C::TYPE-FIX-WHEN-CHAR))
 (55 55 (:REWRITE C::IDENTP-WHEN-IN-IDENT-SETP-BINDS-FREE-X))
 (38 38 (:REWRITE-QUOTED-CONSTANT C::MEMBER-TYPE-LIST-FIX-UNDER-MEMBER-TYPE-LIST-EQUIV))
 (30 2 (:REWRITE C::TYPE-OPTIONP-WHEN-TYPEP))
 (24 24 (:REWRITE C::CONSP-OF-MEMBER-TYPES-OF-MEMBER-VALUES))
 (16 16 (:REWRITE C::VALUEP-WHEN-MEMBER-EQUAL-OF-VALUE-LISTP))
 (12 12 (:TYPE-PRESCRIPTION C::TYPE-OPTIONP))
 (10 10 (:REWRITE C::TYPEP-WHEN-IN-TYPE-SETP-BINDS-FREE-X))
 (6 6 (:REWRITE C::TYPE-OPTIONP-OF-MEMBER-TYPE-LOOKUP))
 (2 2 (:REWRITE C::TYPE-OPTIONP-WHEN-IN-TYPE-OPTION-SETP-BINDS-FREE-X))
 )
(C::VALUE-STRUCT-READ-AUX-WHEN-MEMBER-TYPE-LOOKUP
 (54 2 (:DEFINITION C::VALUE-STRUCT-READ-AUX))
 (16 4 (:REWRITE C::IDENT-FIX-WHEN-IDENTP))
 (12 12 (:TYPE-PRESCRIPTION C::MEMBER-VALUE->NAME$INLINE))
 (12 12 (:TYPE-PRESCRIPTION C::IDENT-FIX$INLINE))
 (10 6 (:REWRITE DEFAULT-CDR))
 (10 6 (:REWRITE DEFAULT-CAR))
 (8 8 (:TYPE-PRESCRIPTION C::IDENTP))
 (7 1 (:REWRITE C::TYPEP-WHEN-TYPE-OPTIONP))
 (4 4 (:REWRITE C::MEMBER-TYPES-OF-MEMBER-VALUES-WHEN-NOT-CONSP))
 (4 4 (:REWRITE C::IDENTP-WHEN-IN-IDENT-SETP-BINDS-FREE-X))
 (1 1 (:TYPE-PRESCRIPTION C::TYPE-OPTIONP))
 (1 1 (:REWRITE C::TYPEP-WHEN-IN-TYPE-SETP-BINDS-FREE-X))
 (1 1 (:REWRITE C::TYPE-OPTIONP-OF-MEMBER-TYPE-LOOKUP))
 )
(C::VALUE-STRUCT-READ-AUX-OF-IDENT-FIX-NAME
 (23 15 (:REWRITE DEFAULT-CAR))
 (19 11 (:REWRITE DEFAULT-CDR))
 (11 11 (:REWRITE C::IDENTP-WHEN-IN-IDENT-SETP-BINDS-FREE-X))
 )
(C::VALUE-STRUCT-READ-AUX-IDENT-EQUIV-CONGRUENCE-ON-NAME)
(C::VALUE-STRUCT-READ-AUX-OF-MEMBER-VALUE-LIST-FIX-MEMBERS
 (598 298 (:REWRITE DEFAULT-CDR))
 (540 270 (:REWRITE DEFAULT-CAR))
 (476 122 (:REWRITE C::IDENT-FIX-WHEN-IDENTP))
 (262 35 (:REWRITE C::MEMBER-VALUE-LIST-FIX-WHEN-MEMBER-VALUE-LISTP))
 (236 236 (:TYPE-PRESCRIPTION C::IDENTP))
 (118 118 (:REWRITE C::IDENTP-WHEN-IN-IDENT-SETP-BINDS-FREE-X))
 (86 86 (:REWRITE C::MEMBER-VALUE-LISTP-WHEN-SUBSETP-EQUAL))
 (54 43 (:REWRITE C::MEMBER-VALUE-LISTP-WHEN-NOT-CONSP))
 (48 8 (:REWRITE C::MEMBER-VALUE-LISTP-OF-CDR-WHEN-MEMBER-VALUE-LISTP))
 )
(C::VALUE-STRUCT-READ-AUX-MEMBER-VALUE-LIST-EQUIV-CONGRUENCE-ON-MEMBERS)
(C::VALUE-STRUCT-READ)
(C::VALUE-RESULTP-OF-VALUE-STRUCT-READ)
(C::VALUE-STRUCT-READ-OF-IDENT-FIX-NAME)
(C::VALUE-STRUCT-READ-IDENT-EQUIV-CONGRUENCE-ON-NAME)
(C::VALUE-STRUCT-READ-OF-VALUE-FIX-STRUCT)
(C::VALUE-STRUCT-READ-VALUE-EQUIV-CONGRUENCE-ON-STRUCT)
(C::VALUE-STRUCT-WRITE-AUX
 (75 47 (:REWRITE DEFAULT-CDR))
 (74 46 (:REWRITE DEFAULT-CAR))
 (51 1 (:DEFINITION C::VALUE-STRUCT-WRITE-AUX))
 (7 1 (:REWRITE C::MEMBER-VALUE-LIST-FIX-WHEN-MEMBER-VALUE-LISTP))
 (7 1 (:REWRITE C::MEMBER-VALUE-FIX-WHEN-MEMBER-VALUEP))
 (6 6 (:REWRITE C::IDENTP-WHEN-IN-IDENT-SETP-BINDS-FREE-X))
 (4 4 (:REWRITE C::VALUEP-WHEN-MEMBER-EQUAL-OF-VALUE-LISTP))
 (3 3 (:REWRITE SUBSETP-TRANS2))
 (3 3 (:REWRITE SUBSETP-TRANS))
 (3 1 (:REWRITE SUBSETP-IMPLIES-SUBSETP-CDR))
 (1 1 (:REWRITE C::VALUE-FIX-WHEN-VALUEP))
 (1 1 (:REWRITE C::MEMBER-VALUE-LISTP-WHEN-NOT-CONSP))
 )
(C::MEMBER-VALUE-LIST-RESULTP-OF-VALUE-STRUCT-WRITE-AUX
 (102 3 (:REWRITE C::MEMBER-VALUE-LIST-FIX-WHEN-MEMBER-VALUE-LISTP))
 (61 16 (:REWRITE C::IDENT-FIX-WHEN-IDENTP))
 (60 3 (:REWRITE C::MEMBER-VALUE-LISTP-OF-CDR-WHEN-MEMBER-VALUE-LISTP))
 (57 3 (:REWRITE C::MEMBER-VALUE-FIX-WHEN-MEMBER-VALUEP))
 (55 35 (:REWRITE DEFAULT-CAR))
 (45 25 (:REWRITE DEFAULT-CDR))
 (42 3 (:REWRITE C::MEMBER-VALUEP-OF-CAR-WHEN-MEMBER-VALUE-LISTP))
 (34 34 (:REWRITE C::MEMBER-VALUE-LISTP-WHEN-SUBSETP-EQUAL))
 (30 30 (:TYPE-PRESCRIPTION C::IDENTP))
 (30 3 (:REWRITE C::VALUE-FIX-WHEN-VALUEP))
 (20 17 (:REWRITE C::MEMBER-VALUE-LISTP-WHEN-NOT-CONSP))
 (15 15 (:REWRITE C::IDENTP-WHEN-IN-IDENT-SETP-BINDS-FREE-X))
 (15 3 (:REWRITE C::VALUEP-WHEN-VALUE-OPTIONP))
 (9 9 (:TYPE-PRESCRIPTION C::VALUEP))
 (6 6 (:TYPE-PRESCRIPTION C::VALUE-OPTIONP))
 (6 6 (:TYPE-PRESCRIPTION C::MEMBER-VALUEP))
 (6 6 (:REWRITE C::VALUEP-WHEN-MEMBER-EQUAL-OF-VALUE-LISTP))
 (6 6 (:REWRITE C::MEMBER-VALUEP-WHEN-MEMBER-EQUAL-OF-MEMBER-VALUE-LISTP))
 (6 3 (:REWRITE C::VALUE-OPTIONP-WHEN-VALUEP))
 )
(C::MEMBER-VALUE-LISTP-OF-VALUE-STRUCT-WRITE-AUX
 (172 43 (:REWRITE C::IDENT-FIX-WHEN-IDENTP))
 (145 91 (:REWRITE DEFAULT-CAR))
 (122 68 (:REWRITE DEFAULT-CDR))
 (86 86 (:TYPE-PRESCRIPTION C::IDENTP))
 (77 4 (:REWRITE C::MEMBER-VALUE-FIX-WHEN-MEMBER-VALUEP))
 (48 4 (:REWRITE C::MEMBER-VALUE-LIST-FIX-WHEN-MEMBER-VALUE-LISTP))
 (46 46 (:REWRITE C::VALUEP-WHEN-MEMBER-EQUAL-OF-VALUE-LISTP))
 (43 43 (:REWRITE C::IDENTP-WHEN-IN-IDENT-SETP-BINDS-FREE-X))
 (35 8 (:REWRITE C::MEMBER-VALUEP-WHEN-MEMBER-EQUAL-OF-MEMBER-VALUE-LISTP))
 (30 4 (:REWRITE C::MEMBER-VALUEP-OF-CAR-WHEN-MEMBER-VALUE-LISTP))
 (30 3 (:REWRITE C::VALUE-FIX-WHEN-VALUEP))
 (27 2 (:DEFINITION MEMBER-EQUAL))
 (24 4 (:REWRITE C::MEMBER-VALUE-LISTP-OF-CDR-WHEN-MEMBER-VALUE-LISTP))
 (23 19 (:REWRITE C::MEMBER-VALUE-LISTP-WHEN-NOT-CONSP))
 (20 1 (:REWRITE SUBSETP-OF-CONS))
 (14 2 (:REWRITE SUBSETP-CAR-MEMBER))
 (11 11 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 (8 8 (:TYPE-PRESCRIPTION C::MEMBER-VALUEP))
 (6 6 (:REWRITE SUBSETP-TRANS2))
 (6 6 (:REWRITE SUBSETP-TRANS))
 (4 4 (:REWRITE SUBSETP-MEMBER . 2))
 (4 4 (:REWRITE SUBSETP-MEMBER . 1))
 (3 3 (:REWRITE SUBSETP-WHEN-ATOM-RIGHT))
 (3 3 (:REWRITE SUBSETP-WHEN-ATOM-LEFT))
 )
(C::MEMBER-VALUE-LIST->NAME-LIST-OF-STRUCT-WRITE-AUX
 (304 76 (:REWRITE C::IDENT-FIX-WHEN-IDENTP))
 (263 161 (:REWRITE DEFAULT-CAR))
 (246 144 (:REWRITE DEFAULT-CDR))
 (152 152 (:TYPE-PRESCRIPTION C::IDENTP))
 (76 76 (:REWRITE C::IDENTP-WHEN-IN-IDENT-SETP-BINDS-FREE-X))
 (70 7 (:REWRITE C::VALUE-FIX-WHEN-VALUEP))
 (66 66 (:REWRITE C::VALUEP-WHEN-MEMBER-EQUAL-OF-VALUE-LISTP))
 (50 3 (:REWRITE C::MEMBER-VALUE-LIST-FIX-WHEN-MEMBER-VALUE-LISTP))
 (45 3 (:REWRITE C::MEMBER-VALUE-FIX-WHEN-MEMBER-VALUEP))
 (44 7 (:REWRITE C::MEMBER-VALUE-LISTP-OF-CDR-WHEN-MEMBER-VALUE-LISTP))
 (30 3 (:REWRITE C::MEMBER-VALUEP-OF-CAR-WHEN-MEMBER-VALUE-LISTP))
 (26 26 (:REWRITE C::MEMBER-VALUE-LISTP-WHEN-SUBSETP-EQUAL))
 (13 13 (:REWRITE C::MEMBER-VALUE-LISTP-WHEN-NOT-CONSP))
 (6 6 (:TYPE-PRESCRIPTION C::MEMBER-VALUEP))
 (6 6 (:REWRITE C::MEMBER-VALUEP-WHEN-MEMBER-EQUAL-OF-MEMBER-VALUE-LISTP))
 )
(C::VALUE-STRUCT-READ-AUX-OF-VALUE-STRUCT-WRITE-AUX
 (871 220 (:REWRITE C::IDENT-FIX-WHEN-IDENTP))
 (808 468 (:REWRITE DEFAULT-CDR))
 (787 447 (:REWRITE DEFAULT-CAR))
 (434 434 (:TYPE-PRESCRIPTION C::IDENTP))
 (420 42 (:REWRITE C::VALUE-FIX-WHEN-VALUEP))
 (371 25 (:REWRITE C::MEMBER-VALUE-FIX-WHEN-MEMBER-VALUEP))
 (328 18 (:REWRITE C::MEMBER-VALUE-LIST-FIX-WHEN-MEMBER-VALUE-LISTP))
 (316 50 (:REWRITE C::MEMBER-VALUE-LISTP-OF-CDR-WHEN-MEMBER-VALUE-LISTP))
 (246 25 (:REWRITE C::MEMBER-VALUEP-OF-CAR-WHEN-MEMBER-VALUE-LISTP))
 (217 217 (:REWRITE C::IDENTP-WHEN-IN-IDENT-SETP-BINDS-FREE-X))
 (186 186 (:REWRITE C::MEMBER-VALUE-LISTP-WHEN-SUBSETP-EQUAL))
 (142 142 (:REWRITE C::VALUEP-WHEN-MEMBER-EQUAL-OF-VALUE-LISTP))
 (93 93 (:REWRITE C::MEMBER-VALUE-LISTP-WHEN-NOT-CONSP))
 (50 50 (:TYPE-PRESCRIPTION C::MEMBER-VALUEP))
 (50 50 (:REWRITE C::MEMBER-VALUEP-WHEN-MEMBER-EQUAL-OF-MEMBER-VALUE-LISTP))
 (3 3 (:TYPE-PRESCRIPTION C::MEMBER-VALUE-LIST-FIX$INLINE))
 )
(C::LEMMA
 (801 30 (:REWRITE C::MEMBER-VALUE-FIX-WHEN-MEMBER-VALUEP))
 (725 32 (:REWRITE C::MEMBER-VALUE-LIST-FIX-WHEN-MEMBER-VALUE-LISTP))
 (691 454 (:REWRITE DEFAULT-CAR))
 (658 425 (:REWRITE DEFAULT-CDR))
 (584 11 (:REWRITE C::TYPEP-WHEN-TYPE-OPTIONP))
 (526 66 (:REWRITE C::MEMBER-VALUE-LISTP-OF-CDR-WHEN-MEMBER-VALUE-LISTP))
 (365 30 (:REWRITE C::MEMBER-VALUEP-OF-CAR-WHEN-MEMBER-VALUE-LISTP))
 (353 61 (:REWRITE C::MEMBER-VALUEP-WHEN-MEMBER-EQUAL-OF-MEMBER-VALUE-LISTP))
 (336 336 (:TYPE-PRESCRIPTION C::TYPE-KIND$INLINE))
 (239 48 (:REWRITE C::VALUEP-WHEN-VALUE-OPTIONP))
 (225 10 (:DEFINITION MEMBER-EQUAL))
 (189 36 (:REWRITE C::VALUE-FIX-WHEN-VALUEP))
 (187 17 (:REWRITE SUBSETP-CAR-MEMBER))
 (171 142 (:REWRITE C::MEMBER-VALUE-LISTP-WHEN-NOT-CONSP))
 (171 33 (:REWRITE SUBSETP-IMPLIES-SUBSETP-CDR))
 (140 33 (:REWRITE C::VALUE-OPTIONP-WHEN-VALUEP))
 (135 135 (:REWRITE C::IDENTP-WHEN-IN-IDENT-SETP-BINDS-FREE-X))
 (96 96 (:REWRITE C::VALUEP-WHEN-MEMBER-EQUAL-OF-VALUE-LISTP))
 (84 75 (:REWRITE SUBSETP-WHEN-ATOM-LEFT))
 (84 2 (:REWRITE SUBSETP-OF-CONS))
 (81 81 (:TYPE-PRESCRIPTION C::VALUE-OPTIONP))
 (80 80 (:REWRITE SUBSETP-TRANS2))
 (80 80 (:REWRITE SUBSETP-TRANS))
 (75 75 (:REWRITE SUBSETP-WHEN-ATOM-RIGHT))
 (69 4 (:REWRITE C::TYPE-OPTIONP-WHEN-TYPEP))
 (60 60 (:TYPE-PRESCRIPTION C::MEMBER-VALUEP))
 (56 28 (:REWRITE C::TYPE-FIX-WHEN-VOID))
 (56 28 (:REWRITE C::TYPE-FIX-WHEN-USHORT))
 (56 28 (:REWRITE C::TYPE-FIX-WHEN-ULONG))
 (56 28 (:REWRITE C::TYPE-FIX-WHEN-ULLONG))
 (56 28 (:REWRITE C::TYPE-FIX-WHEN-UINT))
 (56 28 (:REWRITE C::TYPE-FIX-WHEN-UCHAR))
 (56 28 (:REWRITE C::TYPE-FIX-WHEN-SSHORT))
 (56 28 (:REWRITE C::TYPE-FIX-WHEN-SLONG))
 (56 28 (:REWRITE C::TYPE-FIX-WHEN-SLLONG))
 (56 28 (:REWRITE C::TYPE-FIX-WHEN-SINT))
 (56 28 (:REWRITE C::TYPE-FIX-WHEN-SCHAR))
 (56 28 (:REWRITE C::TYPE-FIX-WHEN-CHAR))
 (52 52 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 (38 1 (:REWRITE C::EQUAL-OF-MEMBER-VALUE))
 (35 35 (:REWRITE-QUOTED-CONSTANT C::MEMBER-TYPE-LIST-FIX-UNDER-MEMBER-TYPE-LIST-EQUIV))
 (20 20 (:REWRITE SUBSETP-MEMBER . 2))
 (20 20 (:REWRITE SUBSETP-MEMBER . 1))
 (15 15 (:TYPE-PRESCRIPTION C::TYPE-OPTIONP))
 (11 11 (:REWRITE C::TYPEP-WHEN-IN-TYPE-SETP-BINDS-FREE-X))
 (6 6 (:TYPE-PRESCRIPTION C::MEMBER-VALUE->VALUE$INLINE))
 (4 4 (:REWRITE C::TYPE-OPTIONP-WHEN-IN-TYPE-OPTION-SETP-BINDS-FREE-X))
 (3 3 (:REWRITE C::TYPE-OPTIONP-OF-MEMBER-TYPE-LOOKUP))
 (1 1 (:REWRITE C::CONSP-OF-MEMBER-VALUE-LIST-FIX))
 )
(C::VALUE-STRUCT-WRITE-AUX-WHEN-MEMBER-TYPE-LOOKUP
 (84 1 (:DEFINITION C::VALUE-STRUCT-WRITE-AUX))
 (15 3 (:REWRITE C::VALUEP-WHEN-VALUE-OPTIONP))
 (13 8 (:REWRITE DEFAULT-CDR))
 (13 8 (:REWRITE DEFAULT-CAR))
 (12 3 (:REWRITE C::IDENT-FIX-WHEN-IDENTP))
 (12 1 (:REWRITE C::MEMBER-VALUE-LIST-FIX-WHEN-MEMBER-VALUE-LISTP))
 (11 1 (:REWRITE C::MEMBER-VALUE-FIX-WHEN-MEMBER-VALUEP))
 (10 1 (:REWRITE C::VALUE-FIX-WHEN-VALUEP))
 (9 2 (:REWRITE C::VALUE-OPTIONP-WHEN-VALUEP))
 (7 1 (:REWRITE C::TYPEP-WHEN-TYPE-OPTIONP))
 (6 6 (:TYPE-PRESCRIPTION C::MEMBER-VALUE->NAME$INLINE))
 (6 6 (:TYPE-PRESCRIPTION C::IDENTP))
 (6 6 (:TYPE-PRESCRIPTION C::IDENT-FIX$INLINE))
 (6 6 (:REWRITE C::VALUEP-WHEN-MEMBER-EQUAL-OF-VALUE-LISTP))
 (6 6 (:REWRITE C::MEMBER-VALUE-LISTP-WHEN-SUBSETP-EQUAL))
 (6 1 (:REWRITE C::MEMBER-VALUEP-OF-CAR-WHEN-MEMBER-VALUE-LISTP))
 (6 1 (:REWRITE C::MEMBER-VALUE-LISTP-OF-CDR-WHEN-MEMBER-VALUE-LISTP))
 (5 5 (:TYPE-PRESCRIPTION C::VALUE-OPTIONP))
 (4 4 (:REWRITE C::MEMBER-TYPES-OF-MEMBER-VALUES-WHEN-NOT-CONSP))
 (3 3 (:REWRITE C::MEMBER-VALUE-LISTP-WHEN-NOT-CONSP))
 (3 3 (:REWRITE C::IDENTP-WHEN-IN-IDENT-SETP-BINDS-FREE-X))
 (2 2 (:TYPE-PRESCRIPTION C::MEMBER-VALUEP))
 (2 2 (:REWRITE C::MEMBER-VALUEP-WHEN-MEMBER-EQUAL-OF-MEMBER-VALUE-LISTP))
 (1 1 (:TYPE-PRESCRIPTION C::TYPE-OPTIONP))
 (1 1 (:REWRITE C::TYPEP-WHEN-IN-TYPE-SETP-BINDS-FREE-X))
 (1 1 (:REWRITE C::TYPE-OPTIONP-OF-MEMBER-TYPE-LOOKUP))
 )
(C::VALUE-STRUCT-WRITE-AUX-OF-IDENT-FIX-NAME
 (66 44 (:REWRITE DEFAULT-CAR))
 (62 4 (:REWRITE C::MEMBER-VALUE-LIST-FIX-WHEN-MEMBER-VALUE-LISTP))
 (58 36 (:REWRITE DEFAULT-CDR))
 (56 4 (:REWRITE C::MEMBER-VALUE-FIX-WHEN-MEMBER-VALUEP))
 (50 8 (:REWRITE C::MEMBER-VALUE-LISTP-OF-CDR-WHEN-MEMBER-VALUE-LISTP))
 (40 4 (:REWRITE C::VALUE-FIX-WHEN-VALUEP))
 (36 4 (:REWRITE C::MEMBER-VALUEP-OF-CAR-WHEN-MEMBER-VALUE-LISTP))
 (32 32 (:REWRITE C::MEMBER-VALUE-LISTP-WHEN-SUBSETP-EQUAL))
 (23 23 (:REWRITE C::IDENTP-WHEN-IN-IDENT-SETP-BINDS-FREE-X))
 (20 4 (:REWRITE C::VALUEP-WHEN-VALUE-OPTIONP))
 (16 16 (:REWRITE C::MEMBER-VALUE-LISTP-WHEN-NOT-CONSP))
 (8 8 (:TYPE-PRESCRIPTION C::VALUE-OPTIONP))
 (8 8 (:TYPE-PRESCRIPTION C::MEMBER-VALUEP))
 (8 8 (:REWRITE C::VALUEP-WHEN-MEMBER-EQUAL-OF-VALUE-LISTP))
 (8 8 (:REWRITE C::MEMBER-VALUEP-WHEN-MEMBER-EQUAL-OF-MEMBER-VALUE-LISTP))
 (8 4 (:REWRITE C::VALUE-OPTIONP-WHEN-VALUEP))
 )
(C::VALUE-STRUCT-WRITE-AUX-IDENT-EQUIV-CONGRUENCE-ON-NAME)
(C::VALUE-STRUCT-WRITE-AUX-OF-VALUE-FIX-VAL
 (82 22 (:REWRITE C::IDENT-FIX-WHEN-IDENTP))
 (66 44 (:REWRITE DEFAULT-CAR))
 (62 4 (:REWRITE C::MEMBER-VALUE-LIST-FIX-WHEN-MEMBER-VALUE-LISTP))
 (58 36 (:REWRITE DEFAULT-CDR))
 (56 10 (:REWRITE C::VALUEP-WHEN-VALUE-OPTIONP))
 (56 4 (:REWRITE C::MEMBER-VALUE-FIX-WHEN-MEMBER-VALUEP))
 (50 8 (:REWRITE C::MEMBER-VALUE-LISTP-OF-CDR-WHEN-MEMBER-VALUE-LISTP))
 (40 40 (:TYPE-PRESCRIPTION C::IDENTP))
 (36 4 (:REWRITE C::MEMBER-VALUEP-OF-CAR-WHEN-MEMBER-VALUE-LISTP))
 (32 32 (:REWRITE C::MEMBER-VALUE-LISTP-WHEN-SUBSETP-EQUAL))
 (26 10 (:REWRITE C::VALUE-OPTIONP-WHEN-VALUEP))
 (20 20 (:TYPE-PRESCRIPTION C::VALUE-OPTIONP))
 (20 20 (:REWRITE C::IDENTP-WHEN-IN-IDENT-SETP-BINDS-FREE-X))
 (16 16 (:REWRITE C::MEMBER-VALUE-LISTP-WHEN-NOT-CONSP))
 (14 14 (:REWRITE C::VALUEP-WHEN-MEMBER-EQUAL-OF-VALUE-LISTP))
 (8 8 (:TYPE-PRESCRIPTION C::MEMBER-VALUEP))
 (8 8 (:REWRITE C::MEMBER-VALUEP-WHEN-MEMBER-EQUAL-OF-MEMBER-VALUE-LISTP))
 )
(C::VALUE-STRUCT-WRITE-AUX-VALUE-EQUIV-CONGRUENCE-ON-VAL)
(C::VALUE-STRUCT-WRITE-AUX-OF-MEMBER-VALUE-LIST-FIX-MEMBERS
 (7825 710 (:REWRITE C::MEMBER-VALUE-LIST-FIX-WHEN-MEMBER-VALUE-LISTP))
 (6670 931 (:REWRITE C::MEMBER-VALUE-LISTP-OF-CDR-WHEN-MEMBER-VALUE-LISTP))
 (4790 2819 (:REWRITE DEFAULT-CDR))
 (4026 314 (:REWRITE C::MEMBER-VALUEP-OF-CAR-WHEN-MEMBER-VALUE-LISTP))
 (3988 2221 (:REWRITE DEFAULT-CAR))
 (3468 879 (:REWRITE C::IDENT-FIX-WHEN-IDENTP))
 (3400 3400 (:REWRITE C::MEMBER-VALUE-LISTP-WHEN-SUBSETP-EQUAL))
 (2881 289 (:REWRITE C::VALUE-FIX-WHEN-VALUEP))
 (1726 1726 (:TYPE-PRESCRIPTION C::IDENTP))
 (1711 1700 (:REWRITE C::MEMBER-VALUE-LISTP-WHEN-NOT-CONSP))
 (1440 288 (:REWRITE C::VALUEP-WHEN-VALUE-OPTIONP))
 (863 863 (:REWRITE C::IDENTP-WHEN-IN-IDENT-SETP-BINDS-FREE-X))
 (650 650 (:REWRITE C::MEMBER-VALUEP-WHEN-MEMBER-EQUAL-OF-MEMBER-VALUE-LISTP))
 (576 576 (:TYPE-PRESCRIPTION C::VALUE-OPTIONP))
 (576 576 (:REWRITE C::VALUEP-WHEN-MEMBER-EQUAL-OF-VALUE-LISTP))
 (576 288 (:REWRITE C::VALUE-OPTIONP-WHEN-VALUEP))
 (156 156 (:REWRITE C::RETURN-TYPE-OF-MEMBER-VALUE-LIST-FIX.NEWX))
 )
(C::VALUE-STRUCT-WRITE-AUX-MEMBER-VALUE-LIST-EQUIV-CONGRUENCE-ON-MEMBERS)
(C::VALUE-STRUCT-WRITE)
(C::VALUE-RESULTP-OF-VALUE-STRUCT-WRITE)
(C::VALUE-KIND-OF-VALUE-STRUCT-WRITE)
(C::VALUEP-OF-VALUE-STRUCT-WRITE
 (29 4 (:REWRITE C::VALUEP-WHEN-VALUE-OPTIONP))
 (23 2 (:REWRITE C::VALUE-OPTIONP-WHEN-VALUEP))
 (8 8 (:REWRITE C::VALUEP-WHEN-MEMBER-EQUAL-OF-VALUE-LISTP))
 (6 6 (:TYPE-PRESCRIPTION C::VALUE-OPTIONP))
 (4 2 (:REWRITE DEFAULT-CDR))
 (4 2 (:REWRITE DEFAULT-CAR))
 )
(C::VALUE-STRUCT-READ-OF-VALUE-STRUCT-WRITE
 (49 8 (:REWRITE C::VALUEP-WHEN-VALUE-OPTIONP))
 (37 10 (:REWRITE C::IDENT-FIX-WHEN-IDENTP))
 (34 5 (:REWRITE C::VALUE-OPTIONP-WHEN-VALUEP))
 (32 14 (:REWRITE DEFAULT-CDR))
 (32 14 (:REWRITE DEFAULT-CAR))
 (21 3 (:REWRITE C::VALUE-FIX-WHEN-VALUEP))
 (18 18 (:TYPE-PRESCRIPTION C::IDENTP))
 (16 16 (:REWRITE C::VALUEP-WHEN-MEMBER-EQUAL-OF-VALUE-LISTP))
 (14 2 (:REWRITE C::MEMBER-VALUE-LIST-FIX-WHEN-MEMBER-VALUE-LISTP))
 (13 13 (:TYPE-PRESCRIPTION C::VALUE-OPTIONP))
 (9 9 (:REWRITE C::IDENTP-WHEN-IN-IDENT-SETP-BINDS-FREE-X))
 (4 4 (:TYPE-PRESCRIPTION C::MEMBER-VALUE-LISTP))
 (4 4 (:REWRITE C::MEMBER-VALUE-LISTP-WHEN-SUBSETP-EQUAL))
 (2 2 (:REWRITE C::MEMBER-VALUE-LISTP-WHEN-NOT-CONSP))
 )
(C::VALUE-STRUCT-WRITE-OF-IDENT-FIX-NAME)
(C::VALUE-STRUCT-WRITE-IDENT-EQUIV-CONGRUENCE-ON-NAME)
(C::VALUE-STRUCT-WRITE-OF-VALUE-FIX-VAL)
(C::VALUE-STRUCT-WRITE-VALUE-EQUIV-CONGRUENCE-ON-VAL)
(C::VALUE-STRUCT-WRITE-OF-VALUE-FIX-STRUCT
 (10 1 (:REWRITE C::VALUE-FIX-WHEN-VALUEP))
 (5 1 (:REWRITE C::VALUEP-WHEN-VALUE-OPTIONP))
 (2 2 (:TYPE-PRESCRIPTION C::VALUE-OPTIONP))
 (2 2 (:REWRITE C::VALUEP-WHEN-MEMBER-EQUAL-OF-VALUE-LISTP))
 (2 1 (:REWRITE C::VALUE-OPTIONP-WHEN-VALUEP))
 )
(C::VALUE-STRUCT-WRITE-VALUE-EQUIV-CONGRUENCE-ON-STRUCT)
