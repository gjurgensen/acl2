(NAT-OPTION-RESULTP)
(CONSP-WHEN-NAT-OPTION-RESULTP)
(NAT-OPTION-RESULT-KIND$INLINE)
(NAT-OPTION-RESULT-KIND-POSSIBILITIES)
(NAT-OPTION-RESULT-FIX$INLINE)
(NAT-OPTION-RESULTP-OF-NAT-OPTION-RESULT-FIX
 (13 1 (:REWRITE FTY::RESULTERR-FIX-WHEN-RESULTERRP))
 (13 1 (:REWRITE OMAP::ALISTP-WHEN-MAPP))
 (6 6 (:TYPE-PRESCRIPTION STRIP-CARS))
 (5 1 (:REWRITE OMAP::MFIX-IMPLIES-MAPP))
 (5 1 (:REWRITE OMAP::MAPP-WHEN-NOT-EMPTY))
 (4 4 (:TYPE-PRESCRIPTION OMAP::MAPP))
 (4 1 (:REWRITE NAT-OPTION-FIX-WHEN-NAT-OPTIONP))
 (4 1 (:REWRITE FTY::EQUAL-OF-STRIP-CARS))
 (3 3 (:REWRITE DEFAULT-CDR))
 (2 2 (:TYPE-PRESCRIPTION OMAP::MFIX))
 (2 2 (:TYPE-PRESCRIPTION OMAP::EMPTY))
 (2 2 (:REWRITE DEFAULT-CAR))
 (2 1 (:REWRITE OMAP::MFIX-WHEN-MAPP))
 (2 1 (:REWRITE OMAP::MAPP-NON-NIL-IMPLIES-NON-EMPTY))
 (1 1 (:TYPE-PRESCRIPTION FTY::RESULTERRP))
 (1 1 (:TYPE-PRESCRIPTION NATP))
 (1 1 (:TYPE-PRESCRIPTION NAT-OPTIONP))
 )
(NAT-OPTION-RESULT-FIX-WHEN-NAT-OPTION-RESULTP)
(NAT-OPTION-RESULT-FIX$INLINE
 (39 3 (:REWRITE OMAP::ALISTP-WHEN-MAPP))
 (17 17 (:REWRITE DEFAULT-CDR))
 (15 3 (:REWRITE OMAP::MFIX-IMPLIES-MAPP))
 (15 3 (:REWRITE OMAP::MAPP-WHEN-NOT-EMPTY))
 (12 12 (:TYPE-PRESCRIPTION OMAP::MAPP))
 (12 12 (:REWRITE DEFAULT-CAR))
 (6 6 (:TYPE-PRESCRIPTION OMAP::MFIX))
 (6 6 (:TYPE-PRESCRIPTION IDENTITY))
 (6 6 (:TYPE-PRESCRIPTION OMAP::EMPTY))
 (6 3 (:REWRITE OMAP::MFIX-WHEN-MAPP))
 (6 3 (:REWRITE OMAP::MAPP-NON-NIL-IMPLIES-NON-EMPTY))
 (2 2 (:DEFINITION STRIP-CARS))
 )
(FTY::TMP-DEFFIXTYPE-IDEMPOTENT)
(NAT-OPTION-RESULT-EQUIV$INLINE)
(NAT-OPTION-RESULT-EQUIV-IS-AN-EQUIVALENCE)
(NAT-OPTION-RESULT-EQUIV-IMPLIES-EQUAL-NAT-OPTION-RESULT-FIX-1)
(NAT-OPTION-RESULT-FIX-UNDER-NAT-OPTION-RESULT-EQUIV)
(EQUAL-OF-NAT-OPTION-RESULT-FIX-1-FORWARD-TO-NAT-OPTION-RESULT-EQUIV)
(EQUAL-OF-NAT-OPTION-RESULT-FIX-2-FORWARD-TO-NAT-OPTION-RESULT-EQUIV)
(NAT-OPTION-RESULT-EQUIV-OF-NAT-OPTION-RESULT-FIX-1-FORWARD)
(NAT-OPTION-RESULT-EQUIV-OF-NAT-OPTION-RESULT-FIX-2-FORWARD)
(NAT-OPTION-RESULT-KIND$INLINE-OF-NAT-OPTION-RESULT-FIX-X
 (5 1 (:REWRITE FTY::RESULTERR-FIX-WHEN-RESULTERRP))
 (4 1 (:DEFINITION FTY::RESULTERRP))
 (2 2 (:DEFINITION STRIP-CARS))
 (2 1 (:REWRITE FTY::EQUAL-OF-STRIP-CARS))
 (1 1 (:REWRITE NAT-OPTION-RESULT-FIX-WHEN-NAT-OPTION-RESULTP))
 )
(NAT-OPTION-RESULT-KIND$INLINE-NAT-OPTION-RESULT-EQUIV-CONGRUENCE-ON-X)
(NAT-OPTION-RESULT-OK->GET$INLINE)
(NAT-OPTIONP-OF-NAT-OPTION-RESULT-OK->GET)
(NAT-OPTION-RESULT-OK->GET$INLINE-OF-NAT-OPTION-RESULT-FIX-X
 (37 13 (:REWRITE NAT-OPTION-RESULT-FIX-WHEN-NAT-OPTION-RESULTP))
 (24 24 (:TYPE-PRESCRIPTION NAT-OPTION-RESULTP))
 )
(NAT-OPTION-RESULT-OK->GET$INLINE-NAT-OPTION-RESULT-EQUIV-CONGRUENCE-ON-X)
(NAT-OPTION-RESULT-OK->GET-WHEN-WRONG-KIND)
(NAT-OPTION-RESULT-OK)
(RETURN-TYPE-OF-NAT-OPTION-RESULT-OK
 (4 1 (:REWRITE NAT-OPTION-FIX-WHEN-NAT-OPTIONP))
 (1 1 (:TYPE-PRESCRIPTION NATP))
 (1 1 (:TYPE-PRESCRIPTION NAT-OPTIONP))
 )
(NAT-OPTION-RESULT-OK->GET-OF-NAT-OPTION-RESULT-OK
 (2 2 (:TYPE-PRESCRIPTION NATP))
 )
(NAT-OPTION-RESULT-OK-OF-FIELDS
 (3 1 (:REWRITE NAT-OPTION-RESULT-FIX-WHEN-NAT-OPTION-RESULTP))
 (2 2 (:TYPE-PRESCRIPTION NATP))
 (2 2 (:TYPE-PRESCRIPTION NAT-OPTION-RESULTP))
 )
(NAT-OPTION-RESULT-FIX-WHEN-OK
 (3 1 (:REWRITE NAT-OPTION-RESULT-FIX-WHEN-NAT-OPTION-RESULTP))
 (2 2 (:TYPE-PRESCRIPTION NAT-OPTION-RESULTP))
 (1 1 (:TYPE-PRESCRIPTION NATP))
 )
(EQUAL-OF-NAT-OPTION-RESULT-OK
 (6 6 (:DEFINITION NAT-OPTIONP))
 )
(NAT-OPTION-RESULT-OK-OF-NAT-OPTION-FIX-GET
 (1 1 (:TYPE-PRESCRIPTION NATP))
 )
(NAT-OPTION-RESULT-OK-NAT-OPTION-EQUIV-CONGRUENCE-ON-GET)
(NAT-OPTION-RESULT-ERR->GET$INLINE
 (39 3 (:REWRITE OMAP::ALISTP-WHEN-MAPP))
 (17 17 (:REWRITE DEFAULT-CDR))
 (15 3 (:REWRITE OMAP::MFIX-IMPLIES-MAPP))
 (15 3 (:REWRITE OMAP::MAPP-WHEN-NOT-EMPTY))
 (12 12 (:TYPE-PRESCRIPTION OMAP::MAPP))
 (12 12 (:REWRITE DEFAULT-CAR))
 (8 8 (:TYPE-PRESCRIPTION IDENTITY))
 (6 6 (:TYPE-PRESCRIPTION OMAP::MFIX))
 (6 6 (:TYPE-PRESCRIPTION OMAP::EMPTY))
 (6 3 (:REWRITE OMAP::MFIX-WHEN-MAPP))
 (6 3 (:REWRITE OMAP::MAPP-NON-NIL-IMPLIES-NON-EMPTY))
 (2 2 (:DEFINITION STRIP-CARS))
 )
(RESULTERRP-OF-NAT-OPTION-RESULT-ERR->GET
 (63 3 (:REWRITE FTY::RESULTERR-FIX-WHEN-RESULTERRP))
 (15 3 (:REWRITE FTY::EQUAL-OF-STRIP-CARS))
 (13 1 (:REWRITE OMAP::ALISTP-WHEN-MAPP))
 (5 1 (:REWRITE OMAP::MFIX-IMPLIES-MAPP))
 (5 1 (:REWRITE OMAP::MAPP-WHEN-NOT-EMPTY))
 (4 4 (:TYPE-PRESCRIPTION OMAP::MAPP))
 (3 3 (:REWRITE DEFAULT-CDR))
 (2 2 (:TYPE-PRESCRIPTION OMAP::MFIX))
 (2 2 (:TYPE-PRESCRIPTION OMAP::EMPTY))
 (2 2 (:REWRITE DEFAULT-CAR))
 (2 1 (:REWRITE OMAP::MFIX-WHEN-MAPP))
 (2 1 (:REWRITE OMAP::MAPP-NON-NIL-IMPLIES-NON-EMPTY))
 )
(NAT-OPTION-RESULT-ERR->GET$INLINE-OF-NAT-OPTION-RESULT-FIX-X
 (62 3 (:REWRITE FTY::RESULTERR-FIX-WHEN-RESULTERRP))
 (56 3 (:DEFINITION FTY::RESULTERRP))
 (40 30 (:TYPE-PRESCRIPTION IDENTITY))
 (20 20 (:TYPE-PRESCRIPTION STRIP-CARS))
 (15 3 (:REWRITE FTY::EQUAL-OF-STRIP-CARS))
 (13 13 (:TYPE-PRESCRIPTION NAT-OPTION-RESULT-FIX$INLINE))
 (12 4 (:REWRITE NAT-OPTION-RESULT-FIX-WHEN-NAT-OPTION-RESULTP))
 (8 8 (:TYPE-PRESCRIPTION NAT-OPTION-RESULTP))
 (6 6 (:DEFINITION STRIP-CARS))
 (3 3 (:TYPE-PRESCRIPTION FTY::RESULTERRP))
 (3 3 (:TYPE-PRESCRIPTION ALISTP))
 )
(NAT-OPTION-RESULT-ERR->GET$INLINE-NAT-OPTION-RESULT-EQUIV-CONGRUENCE-ON-X)
(NAT-OPTION-RESULT-ERR->GET-WHEN-WRONG-KIND
 (3 1 (:REWRITE FTY::RESULTERR-FIX-WHEN-RESULTERRP))
 (1 1 (:TYPE-PRESCRIPTION FTY::RESULTERRP))
 (1 1 (:DEFINITION FTY::RESULTERRP))
 )
(NAT-OPTION-RESULT-ERR
 (39 3 (:REWRITE OMAP::ALISTP-WHEN-MAPP))
 (17 17 (:REWRITE DEFAULT-CDR))
 (15 3 (:REWRITE OMAP::MFIX-IMPLIES-MAPP))
 (15 3 (:REWRITE OMAP::MAPP-WHEN-NOT-EMPTY))
 (12 12 (:TYPE-PRESCRIPTION OMAP::MAPP))
 (12 12 (:REWRITE DEFAULT-CAR))
 (6 6 (:TYPE-PRESCRIPTION OMAP::MFIX))
 (6 6 (:TYPE-PRESCRIPTION IDENTITY))
 (6 6 (:TYPE-PRESCRIPTION OMAP::EMPTY))
 (6 3 (:REWRITE OMAP::MFIX-WHEN-MAPP))
 (6 3 (:REWRITE OMAP::MAPP-NON-NIL-IMPLIES-NON-EMPTY))
 (2 2 (:DEFINITION STRIP-CARS))
 )
(RETURN-TYPE-OF-NAT-OPTION-RESULT-ERR
 (13 1 (:REWRITE OMAP::ALISTP-WHEN-MAPP))
 (5 1 (:REWRITE OMAP::MFIX-IMPLIES-MAPP))
 (5 1 (:REWRITE OMAP::MAPP-WHEN-NOT-EMPTY))
 (4 4 (:TYPE-PRESCRIPTION OMAP::MAPP))
 (3 3 (:REWRITE DEFAULT-CDR))
 (2 2 (:TYPE-PRESCRIPTION OMAP::MFIX))
 (2 2 (:TYPE-PRESCRIPTION OMAP::EMPTY))
 (2 2 (:REWRITE DEFAULT-CAR))
 (2 1 (:REWRITE OMAP::MFIX-WHEN-MAPP))
 (2 1 (:REWRITE OMAP::MAPP-NON-NIL-IMPLIES-NON-EMPTY))
 )
(NAT-OPTION-RESULT-ERR->GET-OF-NAT-OPTION-RESULT-ERR
 (30 24 (:TYPE-PRESCRIPTION IDENTITY))
 (23 1 (:REWRITE FTY::RESULTERR-FIX-WHEN-RESULTERRP))
 (21 1 (:DEFINITION FTY::RESULTERRP))
 (16 16 (:TYPE-PRESCRIPTION NAT-OPTION-RESULT-ERR))
 (6 6 (:TYPE-PRESCRIPTION STRIP-CARS))
 (6 1 (:REWRITE FTY::EQUAL-OF-STRIP-CARS))
 (2 2 (:DEFINITION STRIP-CARS))
 (1 1 (:TYPE-PRESCRIPTION FTY::RESULTERRP))
 (1 1 (:TYPE-PRESCRIPTION ALISTP))
 )
(NAT-OPTION-RESULT-ERR-OF-FIELDS
 (26 2 (:REWRITE FTY::RESULTERR-FIX-WHEN-RESULTERRP))
 (22 2 (:DEFINITION FTY::RESULTERRP))
 (18 18 (:TYPE-PRESCRIPTION IDENTITY))
 (12 12 (:TYPE-PRESCRIPTION STRIP-CARS))
 (8 2 (:REWRITE FTY::EQUAL-OF-STRIP-CARS))
 (4 4 (:DEFINITION STRIP-CARS))
 (3 1 (:REWRITE NAT-OPTION-RESULT-FIX-WHEN-NAT-OPTION-RESULTP))
 (2 2 (:TYPE-PRESCRIPTION FTY::RESULTERRP))
 (2 2 (:TYPE-PRESCRIPTION NAT-OPTION-RESULTP))
 (2 2 (:TYPE-PRESCRIPTION ALISTP))
 )
(NAT-OPTION-RESULT-FIX-WHEN-ERR
 (18 18 (:TYPE-PRESCRIPTION IDENTITY))
 (14 2 (:REWRITE FTY::RESULTERR-FIX-WHEN-RESULTERRP))
 (11 1 (:DEFINITION FTY::RESULTERRP))
 (6 6 (:TYPE-PRESCRIPTION STRIP-CARS))
 (4 1 (:REWRITE FTY::EQUAL-OF-STRIP-CARS))
 (3 1 (:REWRITE NAT-OPTION-RESULT-FIX-WHEN-NAT-OPTION-RESULTP))
 (2 2 (:TYPE-PRESCRIPTION NAT-OPTION-RESULTP))
 (2 2 (:DEFINITION STRIP-CARS))
 (1 1 (:TYPE-PRESCRIPTION FTY::RESULTERRP))
 (1 1 (:TYPE-PRESCRIPTION ALISTP))
 )
(EQUAL-OF-NAT-OPTION-RESULT-ERR
 (152 6 (:REWRITE FTY::RESULTERR-FIX-WHEN-RESULTERRP))
 (134 6 (:DEFINITION FTY::RESULTERRP))
 (52 4 (:REWRITE OMAP::ALISTP-WHEN-MAPP))
 (38 2 (:DEFINITION ALISTP))
 (30 6 (:REWRITE FTY::EQUAL-OF-STRIP-CARS))
 (24 12 (:DEFINITION STRIP-CARS))
 (23 23 (:REWRITE DEFAULT-CAR))
 (22 22 (:REWRITE DEFAULT-CDR))
 (20 4 (:REWRITE OMAP::MFIX-IMPLIES-MAPP))
 (20 4 (:REWRITE OMAP::MAPP-WHEN-NOT-EMPTY))
 (16 16 (:TYPE-PRESCRIPTION OMAP::MAPP))
 (12 12 (:TYPE-PRESCRIPTION STRIP-CARS))
 (10 2 (:REWRITE FTY::RESULTERRP-WHEN-RESULTERR-OPTIONP))
 (8 8 (:TYPE-PRESCRIPTION OMAP::MFIX))
 (8 8 (:TYPE-PRESCRIPTION OMAP::EMPTY))
 (8 8 (:TYPE-PRESCRIPTION ALISTP))
 (8 4 (:REWRITE OMAP::MFIX-WHEN-MAPP))
 (8 4 (:REWRITE OMAP::MAPP-NON-NIL-IMPLIES-NON-EMPTY))
 (4 4 (:TYPE-PRESCRIPTION FTY::RESULTERRP))
 (4 4 (:TYPE-PRESCRIPTION FTY::RESULTERR-OPTIONP))
 (4 2 (:REWRITE FTY::RESULTERR-OPTIONP-WHEN-RESULTERRP))
 )
(NAT-OPTION-RESULT-ERR-OF-RESULTERR-FIX-GET
 (12 12 (:TYPE-PRESCRIPTION IDENTITY))
 )
(NAT-OPTION-RESULT-ERR-RESULTERR-EQUIV-CONGRUENCE-ON-GET)
(NAT-OPTION-RESULT-FIX-REDEF
 (9 3 (:REWRITE NAT-OPTION-RESULT-FIX-WHEN-NAT-OPTION-RESULTP))
 (6 6 (:TYPE-PRESCRIPTION NAT-OPTION-RESULTP))
 )
(NAT-OPTION-RESULTP-WHEN-NAT-OPTIONP)
(NAT-OPTION-RESULTP-WHEN-RESULTERRP)
(NAT-OPTIONP-WHEN-NAT-OPTION-RESULTP-AND-NOT-RESULTERRP)
