(CHECK-IF-CALL
 (50 10 (:DEFINITION LEN))
 (48 48 (:REWRITE DEFAULT-CDR))
 (25 3 (:DEFINITION LENGTH))
 (20 10 (:REWRITE DEFAULT-+-2))
 (19 19 (:REWRITE DEFAULT-CAR))
 (10 10 (:REWRITE DEFAULT-+-1))
 (5 5 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (3 1 (:DEFINITION SYMBOL-LISTP))
 (1 1 (:TYPE-PRESCRIPTION SYMBOL-LISTP))
 (1 1 (:TYPE-PRESCRIPTION PSEUDO-TERM-LISTP))
 (1 1 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (1 1 (:REWRITE DEFAULT-COERCE-2))
 (1 1 (:REWRITE DEFAULT-COERCE-1))
 )
(BOOLEANP-OF-CHECK-IF-CALL.YES/NO
 (8 8 (:REWRITE DEFAULT-CDR))
 (5 5 (:REWRITE DEFAULT-CAR))
 (5 1 (:DEFINITION LEN))
 (2 1 (:REWRITE DEFAULT-+-2))
 (1 1 (:REWRITE DEFAULT-+-1))
 )
(PSEUDO-TERMP-OF-CHECK-IF-CALL.TEST
 (50 6 (:DEFINITION LENGTH))
 (48 48 (:REWRITE DEFAULT-CDR))
 (45 9 (:DEFINITION LEN))
 (35 35 (:REWRITE DEFAULT-CAR))
 (18 9 (:REWRITE DEFAULT-+-2))
 (9 9 (:REWRITE DEFAULT-+-1))
 (6 6 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (6 2 (:DEFINITION SYMBOL-LISTP))
 (5 5 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (2 2 (:TYPE-PRESCRIPTION SYMBOL-LISTP))
 (2 2 (:REWRITE DEFAULT-COERCE-2))
 (2 2 (:REWRITE DEFAULT-COERCE-1))
 )
(PSEUDO-TERMP-OF-CHECK-IF-CALL.THEN
 (200 24 (:DEFINITION LENGTH))
 (188 188 (:REWRITE DEFAULT-CDR))
 (127 127 (:REWRITE DEFAULT-CAR))
 (84 42 (:REWRITE DEFAULT-+-2))
 (42 42 (:REWRITE DEFAULT-+-1))
 (24 24 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (24 24 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (24 8 (:DEFINITION SYMBOL-LISTP))
 (8 8 (:TYPE-PRESCRIPTION SYMBOL-LISTP))
 (8 8 (:REWRITE DEFAULT-COERCE-2))
 (8 8 (:REWRITE DEFAULT-COERCE-1))
 )
(PSEUDO-TERMP-OF-CHECK-IF-CALL.ELSE
 (255 255 (:REWRITE DEFAULT-CDR))
 (250 30 (:DEFINITION LENGTH))
 (156 156 (:REWRITE DEFAULT-CAR))
 (106 53 (:REWRITE DEFAULT-+-2))
 (53 53 (:REWRITE DEFAULT-+-1))
 (30 30 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (30 30 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (30 10 (:DEFINITION SYMBOL-LISTP))
 (10 10 (:TYPE-PRESCRIPTION SYMBOL-LISTP))
 (10 10 (:REWRITE DEFAULT-COERCE-2))
 (10 10 (:REWRITE DEFAULT-COERCE-1))
 )
(ACL2-COUNT-OF-CHECK-IF-CALL.TEST
 (121 53 (:REWRITE DEFAULT-+-2))
 (70 53 (:REWRITE DEFAULT-+-1))
 (46 46 (:REWRITE DEFAULT-CDR))
 (32 8 (:REWRITE COMMUTATIVITY-OF-+))
 (32 8 (:DEFINITION INTEGER-ABS))
 (32 4 (:DEFINITION LENGTH))
 (18 18 (:REWRITE DEFAULT-CAR))
 (12 9 (:REWRITE DEFAULT-<-2))
 (10 9 (:REWRITE DEFAULT-<-1))
 (8 8 (:REWRITE DEFAULT-UNARY-MINUS))
 (4 4 (:REWRITE DEFAULT-REALPART))
 (4 4 (:REWRITE DEFAULT-NUMERATOR))
 (4 4 (:REWRITE DEFAULT-IMAGPART))
 (4 4 (:REWRITE DEFAULT-DENOMINATOR))
 (4 4 (:REWRITE DEFAULT-COERCE-2))
 (4 4 (:REWRITE DEFAULT-COERCE-1))
 )
(ACL2-COUNT-OF-CHECK-IF-CALL.THEN
 (121 53 (:REWRITE DEFAULT-+-2))
 (70 53 (:REWRITE DEFAULT-+-1))
 (46 46 (:REWRITE DEFAULT-CDR))
 (32 8 (:REWRITE COMMUTATIVITY-OF-+))
 (32 8 (:DEFINITION INTEGER-ABS))
 (32 4 (:DEFINITION LENGTH))
 (18 18 (:REWRITE DEFAULT-CAR))
 (12 9 (:REWRITE DEFAULT-<-2))
 (10 9 (:REWRITE DEFAULT-<-1))
 (8 8 (:REWRITE DEFAULT-UNARY-MINUS))
 (4 4 (:REWRITE DEFAULT-REALPART))
 (4 4 (:REWRITE DEFAULT-NUMERATOR))
 (4 4 (:REWRITE DEFAULT-IMAGPART))
 (4 4 (:REWRITE DEFAULT-DENOMINATOR))
 (4 4 (:REWRITE DEFAULT-COERCE-2))
 (4 4 (:REWRITE DEFAULT-COERCE-1))
 )
(ACL2-COUNT-OF-CHECK-IF-CALL.ELSE
 (489 223 (:REWRITE DEFAULT-+-2))
 (303 223 (:REWRITE DEFAULT-+-1))
 (168 42 (:REWRITE COMMUTATIVITY-OF-+))
 (168 42 (:DEFINITION INTEGER-ABS))
 (168 21 (:DEFINITION LENGTH))
 (131 131 (:REWRITE DEFAULT-CDR))
 (63 47 (:REWRITE DEFAULT-<-2))
 (52 47 (:REWRITE DEFAULT-<-1))
 (48 48 (:REWRITE DEFAULT-CAR))
 (42 42 (:REWRITE DEFAULT-UNARY-MINUS))
 (21 21 (:REWRITE DEFAULT-REALPART))
 (21 21 (:REWRITE DEFAULT-NUMERATOR))
 (21 21 (:REWRITE DEFAULT-IMAGPART))
 (21 21 (:REWRITE DEFAULT-DENOMINATOR))
 (21 21 (:REWRITE DEFAULT-COERCE-2))
 (21 21 (:REWRITE DEFAULT-COERCE-1))
 )
