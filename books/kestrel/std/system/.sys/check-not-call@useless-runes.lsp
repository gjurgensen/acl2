(CHECK-NOT-CALL)
(BOOLEANP-OF-CHECK-NOT-CALL.YES/NO
 (4 4 (:REWRITE DEFAULT-CDR))
 (2 2 (:REWRITE DEFAULT-CAR))
 )
(PSEUDO-TERMP-OF-CHECK-NOT-CALL.ARG
 (50 6 (:DEFINITION LENGTH))
 (41 41 (:REWRITE DEFAULT-CDR))
 (40 8 (:DEFINITION LEN))
 (31 31 (:REWRITE DEFAULT-CAR))
 (18 18 (:TYPE-PRESCRIPTION LEN))
 (16 8 (:REWRITE DEFAULT-+-2))
 (8 8 (:REWRITE DEFAULT-+-1))
 (6 6 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (6 2 (:DEFINITION SYMBOL-LISTP))
 (5 5 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (2 2 (:TYPE-PRESCRIPTION SYMBOL-LISTP))
 (2 2 (:REWRITE DEFAULT-COERCE-2))
 (2 2 (:REWRITE DEFAULT-COERCE-1))
 )
(ACL2-COUNT-OF-CHECK-NOT-CALL
 (47 24 (:REWRITE DEFAULT-+-2))
 (31 24 (:REWRITE DEFAULT-+-1))
 (16 16 (:REWRITE DEFAULT-CDR))
 (16 4 (:DEFINITION INTEGER-ABS))
 (16 2 (:DEFINITION LENGTH))
 (10 2 (:DEFINITION LEN))
 (9 9 (:REWRITE DEFAULT-CAR))
 (6 5 (:REWRITE DEFAULT-<-2))
 (6 5 (:REWRITE DEFAULT-<-1))
 (4 4 (:REWRITE DEFAULT-UNARY-MINUS))
 (2 2 (:TYPE-PRESCRIPTION LEN))
 (2 2 (:REWRITE DEFAULT-REALPART))
 (2 2 (:REWRITE DEFAULT-NUMERATOR))
 (2 2 (:REWRITE DEFAULT-IMAGPART))
 (2 2 (:REWRITE DEFAULT-DENOMINATOR))
 (2 2 (:REWRITE DEFAULT-COERCE-2))
 (2 2 (:REWRITE DEFAULT-COERCE-1))
 )
