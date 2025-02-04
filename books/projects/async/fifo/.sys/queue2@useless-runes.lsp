(ADE::QUEUE2$DATA-INS-LEN
 (1 1 (:REWRITE DEFAULT-<-2))
 (1 1 (:REWRITE DEFAULT-<-1))
 )
(ADE::QUEUE2$INS-LEN)
(ADE::QUEUE2*
 (24 24 (:TYPE-PRESCRIPTION POSP))
 )
(ADE::QUEUE2*$DESTRUCTURE
 (66 12 (:REWRITE APPEND-WHEN-NOT-CONSP))
 (60 60 (:TYPE-PRESCRIPTION POSP))
 (60 6 (:DEFINITION BINARY-APPEND))
 (16 16 (:REWRITE DEFAULT-CDR))
 (11 11 (:REWRITE DEFAULT-CAR))
 )
(ADE::NOT-PRIMP-QUEUE2)
(ADE::QUEUE2$NETLIST)
(ADE::QUEUE2&)
(ADE::CHECK-QUEUE2$NETLIST-64)
(ADE::QUEUE2$ST-FORMAT)
(ADE::QUEUE2$ST-FORMAT=>CONSTRAINT
 (5 1 (:DEFINITION LEN))
 (3 3 (:REWRITE NTH-WHEN-PREFIXP))
 (2 1 (:REWRITE DEFAULT-+-2))
 (1 1 (:REWRITE DEFAULT-CDR))
 (1 1 (:REWRITE DEFAULT-+-1))
 )
(ADE::QUEUE2$VALID-ST)
(ADE::QUEUE2$VALID-ST=>CONSTRAINT
 (5 5 (:REWRITE NTH-WHEN-PREFIXP))
 (5 1 (:DEFINITION LEN))
 (2 1 (:REWRITE DEFAULT-+-2))
 (1 1 (:REWRITE DEFAULT-CDR))
 (1 1 (:REWRITE DEFAULT-+-1))
 )
(ADE::QUEUE2$VALID-ST=>ST-FORMAT
 (14 14 (:REWRITE NTH-WHEN-PREFIXP))
 (8 2 (:DEFINITION STRIP-CARS))
 (4 4 (:REWRITE DEFAULT-CAR))
 (2 2 (:REWRITE DEFAULT-CDR))
 )
(ADE::QUEUE2$DATA-IN
 (6 2 (:REWRITE ADE::BV-IS-TRUE-LIST))
 (5 1 (:DEFINITION TRUE-LISTP))
 (4 4 (:TYPE-PRESCRIPTION ADE::BVP))
 (1 1 (:REWRITE DEFAULT-CDR))
 (1 1 (:REWRITE DEFAULT-<-2))
 (1 1 (:REWRITE DEFAULT-<-1))
 )
(ADE::LEN-QUEUE2$DATA-IN)
(ADE::QUEUE2$IN-ACT
 (10 5 (:TYPE-PRESCRIPTION ADE::BOOLEANP-JOINT-ACT))
 (5 5 (:TYPE-PRESCRIPTION BOOLEANP))
 )
(ADE::QUEUE2$IN-ACT-INACTIVE
 (10 1 (:DEFINITION NTHCDR))
 (6 1 (:REWRITE COMMUTATIVITY-OF-+))
 (5 5 (:REWRITE NTH-WHEN-PREFIXP))
 (5 1 (:REWRITE ADE::NFIX-OF-NAT))
 (4 4 (:REWRITE DEFAULT-+-2))
 (4 4 (:REWRITE DEFAULT-+-1))
 (3 1 (:REWRITE FOLD-CONSTS-IN-+))
 (3 1 (:DEFINITION NATP))
 (2 2 (:REWRITE DEFAULT-<-2))
 (2 2 (:REWRITE DEFAULT-<-1))
 (1 1 (:TYPE-PRESCRIPTION NATP))
 (1 1 (:REWRITE DEFAULT-CDR))
 (1 1 (:REWRITE DEFAULT-CAR))
 )
(ADE::QUEUE2$OUT-ACT
 (10 5 (:TYPE-PRESCRIPTION ADE::BOOLEANP-JOINT-ACT))
 (5 5 (:TYPE-PRESCRIPTION BOOLEANP))
 )
(ADE::QUEUE2$OUT-ACT-INACTIVE
 (10 1 (:DEFINITION NTHCDR))
 (6 1 (:REWRITE COMMUTATIVITY-OF-+))
 (5 5 (:REWRITE NTH-WHEN-PREFIXP))
 (5 1 (:REWRITE ADE::NFIX-OF-NAT))
 (4 4 (:REWRITE DEFAULT-+-2))
 (4 4 (:REWRITE DEFAULT-+-1))
 (3 1 (:REWRITE FOLD-CONSTS-IN-+))
 (3 1 (:DEFINITION NATP))
 (2 2 (:REWRITE DEFAULT-<-2))
 (2 2 (:REWRITE DEFAULT-<-1))
 (1 1 (:TYPE-PRESCRIPTION NATP))
 (1 1 (:REWRITE DEFAULT-CDR))
 (1 1 (:REWRITE DEFAULT-CAR))
 )
(ADE::QUEUE2$DATA-OUT)
(ADE::LEN-QUEUE2$DATA-OUT-1
 (10 2 (:DEFINITION LEN))
 (4 4 (:REWRITE NTH-WHEN-PREFIXP))
 (4 4 (:LINEAR LEN-WHEN-PREFIXP))
 (4 2 (:REWRITE DEFAULT-+-2))
 (2 2 (:REWRITE DEFAULT-CDR))
 (2 2 (:REWRITE DEFAULT-+-1))
 (2 2 (:LINEAR ADE::A-HELPFUL-LEMMA-FOR-TREE-INDUCTIONS))
 )
(ADE::LEN-QUEUE2$DATA-OUT-2
 (10 2 (:DEFINITION LEN))
 (8 8 (:REWRITE NTH-WHEN-PREFIXP))
 (4 4 (:LINEAR LEN-WHEN-PREFIXP))
 (4 2 (:REWRITE DEFAULT-+-2))
 (4 1 (:DEFINITION STRIP-CARS))
 (3 3 (:REWRITE DEFAULT-CDR))
 (2 2 (:REWRITE DEFAULT-CAR))
 (2 2 (:REWRITE DEFAULT-+-1))
 (2 2 (:LINEAR ADE::A-HELPFUL-LEMMA-FOR-TREE-INDUCTIONS))
 )
(ADE::BVP-QUEUE2$DATA-OUT
 (40 4 (:DEFINITION NTHCDR))
 (32 32 (:REWRITE NTH-WHEN-PREFIXP))
 (24 4 (:REWRITE COMMUTATIVITY-OF-+))
 (20 18 (:REWRITE DEFAULT-+-2))
 (18 18 (:REWRITE DEFAULT-+-1))
 (16 4 (:DEFINITION STRIP-CARS))
 (12 4 (:REWRITE FOLD-CONSTS-IN-+))
 (10 10 (:REWRITE DEFAULT-CDR))
 (10 2 (:DEFINITION LEN))
 (8 8 (:REWRITE DEFAULT-CAR))
 (8 4 (:TYPE-PRESCRIPTION ADE::BOOLEANP-JOINT-ACT))
 (8 4 (:REWRITE ADE::QUEUE2$OUT-ACT-INACTIVE))
 (4 4 (:TYPE-PRESCRIPTION BOOLEANP))
 )
(ADE::QUEUE2$OUTPUTS)
(ADE::QUEUE2$VALUE
 (432 216 (:REWRITE DEFAULT-+-2))
 (256 16 (:REWRITE ADE::DISJOINT-ATOM))
 (218 216 (:REWRITE DEFAULT-+-1))
 (196 45 (:DEFINITION BINARY-APPEND))
 (164 16 (:REWRITE ADE::DISJOINT-COMMUTATIVE))
 (144 16 (:REWRITE ADE::DISJOINT-SIS-SAME-SYM-2))
 (144 16 (:REWRITE ADE::DISJOINT-SIS-SAME-SYM-1))
 (120 8 (:DEFINITION ATOM))
 (112 112 (:TYPE-PRESCRIPTION PAIRLIS$))
 (110 26 (:REWRITE ADE::ASSOC-EQ-VALUES-ATOM))
 (96 32 (:REWRITE ADE::CAR-V-THREEFIX))
 (68 68 (:LINEAR LEN-WHEN-PREFIXP))
 (64 32 (:DEFINITION ADE::3V-FIX))
 (52 38 (:REWRITE ADE::V-THREEFIX-BVP))
 (48 6 (:REWRITE ADE::ASSOC-EQ-VALUES-ARGS-PAIRLIS$-ARGS))
 (40 40 (:TYPE-PRESCRIPTION ADE::3VP))
 (34 34 (:TYPE-PRESCRIPTION ADE::BVP))
 (34 34 (:LINEAR ADE::A-HELPFUL-LEMMA-FOR-TREE-INDUCTIONS))
 (32 16 (:REWRITE DEFAULT-<-2))
 (32 5 (:DEFINITION TRUE-LISTP))
 (30 15 (:TYPE-PRESCRIPTION ADE::BOOLEANP-JOINT-ACT))
 (27 19 (:REWRITE ADE::F-BUF-OF-NOT-BOOLEANP))
 (27 19 (:REWRITE ADE::F-BUF-OF-3VP))
 (26 10 (:REWRITE ADE::BV-IS-TRUE-LIST))
 (24 24 (:DEFINITION STRIP-CARS))
 (23 23 (:TYPE-PRESCRIPTION BOOLEANP))
 (22 22 (:TYPE-PRESCRIPTION ADE::F-BUF))
 (16 16 (:REWRITE DEFAULT-<-1))
 (12 3 (:REWRITE TAKE-WHEN-ATOM))
 (6 2 (:REWRITE ADE::FV-IF-WHEN-BVP))
 (6 1 (:REWRITE ADE::QUEUE2$OUT-ACT-INACTIVE))
 (5 5 (:REWRITE ADE::NTHCDR-OF-POS-CONST-IDX))
 (4 2 (:REWRITE DEFAULT-UNARY-MINUS))
 (4 1 (:REWRITE ADE::QUEUE2$IN-ACT-INACTIVE))
 (2 2 (:TYPE-PRESCRIPTION NO-DUPLICATESP-EQUAL))
 (2 2 (:REWRITE ADE::NO-DUPLICATESP-SIS))
 (2 2 (:REWRITE DEFAULT-SYMBOL-NAME))
 )
(ADE::QUEUE2$STEP
 (12 6 (:TYPE-PRESCRIPTION ADE::BOOLEANP-JOINT-ACT))
 (6 6 (:TYPE-PRESCRIPTION BOOLEANP))
 )
(ADE::QUEUE2$STATE
 (801 401 (:REWRITE DEFAULT-+-2))
 (512 32 (:REWRITE ADE::DISJOINT-ATOM))
 (406 401 (:REWRITE DEFAULT-+-1))
 (388 93 (:DEFINITION BINARY-APPEND))
 (328 32 (:REWRITE ADE::DISJOINT-COMMUTATIVE))
 (288 32 (:REWRITE ADE::DISJOINT-SIS-SAME-SYM-2))
 (288 32 (:REWRITE ADE::DISJOINT-SIS-SAME-SYM-1))
 (240 16 (:DEFINITION ATOM))
 (226 226 (:TYPE-PRESCRIPTION PAIRLIS$))
 (225 75 (:REWRITE ADE::CAR-V-THREEFIX))
 (179 39 (:REWRITE ADE::ASSOC-EQ-VALUES-ATOM))
 (150 75 (:DEFINITION ADE::3V-FIX))
 (132 66 (:TYPE-PRESCRIPTION ADE::BOOLEANP-JOINT-ACT))
 (116 116 (:LINEAR LEN-WHEN-PREFIXP))
 (111 91 (:REWRITE ADE::V-THREEFIX-BVP))
 (91 21 (:REWRITE ADE::FV-IF-WHEN-BVP))
 (90 90 (:TYPE-PRESCRIPTION BOOLEANP))
 (87 87 (:TYPE-PRESCRIPTION ADE::3VP))
 (84 84 (:DEFINITION STRIP-CARS))
 (66 33 (:REWRITE DEFAULT-<-2))
 (58 58 (:LINEAR ADE::A-HELPFUL-LEMMA-FOR-TREE-INDUCTIONS))
 (47 35 (:REWRITE ADE::F-BUF-OF-NOT-BOOLEANP))
 (47 35 (:REWRITE ADE::F-BUF-OF-3VP))
 (42 42 (:TYPE-PRESCRIPTION ADE::F-BUF))
 (38 38 (:TYPE-PRESCRIPTION ADE::FV-IF))
 (37 14 (:REWRITE TAKE-WHEN-ATOM))
 (34 34 (:TYPE-PRESCRIPTION ADE::UPDATE-ALIST))
 (33 33 (:REWRITE DEFAULT-<-1))
 (32 32 (:TYPE-PRESCRIPTION ADE::BVP))
 (16 16 (:REWRITE ADE::NTHCDR-OF-POS-CONST-IDX))
 (16 1 (:REWRITE LEN-OF-APPEND))
 (12 4 (:REWRITE ADE::BV-IS-TRUE-LIST))
 (8 4 (:REWRITE DEFAULT-UNARY-MINUS))
 (8 2 (:DEFINITION TRUE-LISTP))
 (6 1 (:REWRITE ADE::QUEUE2$OUT-ACT-INACTIVE))
 (4 1 (:REWRITE ADE::QUEUE2$IN-ACT-INACTIVE))
 (4 1 (:REWRITE COMMUTATIVITY-OF-+))
 (2 2 (:REWRITE DEFAULT-SYMBOL-NAME))
 (2 1 (:REWRITE PREFIXP-WHEN-PREFIXP))
 (1 1 (:REWRITE PREFIXP-TRANSITIVE . 2))
 (1 1 (:REWRITE PREFIXP-TRANSITIVE . 1))
 (1 1 (:REWRITE PREFIXP-ONE-WAY-OR-ANOTHER . 2))
 (1 1 (:REWRITE PREFIXP-ONE-WAY-OR-ANOTHER . 1))
 (1 1 (:REWRITE CONSP-OF-APPEND))
 )
(ADE::QUEUE2$INPUT-FORMAT)
(ADE::BOOLEANP-QUEUE2$IN-ACT
 (50 5 (:DEFINITION NTHCDR))
 (40 40 (:REWRITE NTH-WHEN-PREFIXP))
 (40 8 (:DEFINITION LEN))
 (36 28 (:REWRITE DEFAULT-+-2))
 (30 5 (:REWRITE COMMUTATIVITY-OF-+))
 (28 28 (:REWRITE DEFAULT-+-1))
 (26 4 (:REWRITE ADE::BV-IS-TRUE-LIST))
 (24 2 (:REWRITE ADE::LEN-NTHCDR))
 (19 19 (:REWRITE DEFAULT-CDR))
 (18 2 (:DEFINITION TRUE-LISTP))
 (15 5 (:REWRITE FOLD-CONSTS-IN-+))
 (12 2 (:DEFINITION BINARY-APPEND))
 (10 4 (:REWRITE APPEND-WHEN-NOT-CONSP))
 (8 4 (:TYPE-PRESCRIPTION ADE::BVP-NTHCDR))
 (8 4 (:REWRITE ADE::QUEUE2$IN-ACT-INACTIVE))
 (8 2 (:DEFINITION STRIP-CARS))
 (6 6 (:REWRITE DEFAULT-CAR))
 (6 4 (:REWRITE DEFAULT-<-1))
 (6 2 (:REWRITE ADE::BVP-NTHCDR))
 (4 4 (:REWRITE DEFAULT-<-2))
 (3 1 (:DEFINITION NATP))
 (1 1 (:TYPE-PRESCRIPTION NATP))
 )
(ADE::BOOLEANP-QUEUE2$OUT-ACT
 (50 5 (:DEFINITION NTHCDR))
 (40 40 (:REWRITE NTH-WHEN-PREFIXP))
 (40 8 (:DEFINITION LEN))
 (36 28 (:REWRITE DEFAULT-+-2))
 (30 5 (:REWRITE COMMUTATIVITY-OF-+))
 (28 28 (:REWRITE DEFAULT-+-1))
 (26 4 (:REWRITE ADE::BV-IS-TRUE-LIST))
 (24 2 (:REWRITE ADE::LEN-NTHCDR))
 (19 19 (:REWRITE DEFAULT-CDR))
 (18 2 (:DEFINITION TRUE-LISTP))
 (15 5 (:REWRITE FOLD-CONSTS-IN-+))
 (12 2 (:DEFINITION BINARY-APPEND))
 (10 4 (:REWRITE APPEND-WHEN-NOT-CONSP))
 (8 4 (:TYPE-PRESCRIPTION ADE::BVP-NTHCDR))
 (8 4 (:REWRITE ADE::QUEUE2$OUT-ACT-INACTIVE))
 (8 2 (:DEFINITION STRIP-CARS))
 (6 6 (:REWRITE DEFAULT-CAR))
 (6 4 (:REWRITE DEFAULT-<-1))
 (6 2 (:REWRITE ADE::BVP-NTHCDR))
 (4 4 (:REWRITE DEFAULT-<-2))
 (3 1 (:DEFINITION NATP))
 (1 1 (:TYPE-PRESCRIPTION NATP))
 )
(ADE::QUEUE2$ST-FORMAT-PRESERVED
 (54 4 (:REWRITE ADE::FV-IF-WHEN-BVP))
 (41 41 (:REWRITE NTH-WHEN-PREFIXP))
 (24 6 (:DEFINITION STRIP-CARS))
 (20 20 (:REWRITE DEFAULT-CAR))
 (20 15 (:REWRITE DEFAULT-+-2))
 (20 2 (:DEFINITION NTHCDR))
 (15 15 (:REWRITE DEFAULT-CDR))
 (15 15 (:REWRITE DEFAULT-+-1))
 (14 14 (:TYPE-PRESCRIPTION BOOLEANP))
 (12 6 (:TYPE-PRESCRIPTION ADE::BOOLEANP-QUEUE2$IN-ACT))
 (12 6 (:TYPE-PRESCRIPTION ADE::BOOLEANP-JOINT-ACT))
 (12 2 (:REWRITE COMMUTATIVITY-OF-+))
 (10 10 (:TYPE-PRESCRIPTION ADE::QUEUE2$INPUT-FORMAT))
 (10 2 (:DEFINITION PAIRLIS$))
 (6 6 (:TYPE-PRESCRIPTION ADE::QUEUE2$IN-ACT))
 (6 6 (:TYPE-PRESCRIPTION ADE::JOINT-ACT))
 (6 2 (:REWRITE FOLD-CONSTS-IN-+))
 (6 2 (:REWRITE ADE::BOOLEANP-QUEUE2$IN-ACT))
 (4 2 (:REWRITE ADE::QUEUE2$IN-ACT-INACTIVE))
 (2 2 (:REWRITE DEFAULT-UNARY-MINUS))
 (2 1 (:REWRITE ADE::QUEUE2$OUT-ACT-INACTIVE))
 )
(ADE::QUEUE2$VALUE-ALT
 (320 32 (:DEFINITION NTHCDR))
 (192 174 (:REWRITE DEFAULT-+-2))
 (192 32 (:REWRITE COMMUTATIVITY-OF-+))
 (174 174 (:REWRITE DEFAULT-+-1))
 (150 21 (:DEFINITION BINARY-APPEND))
 (144 9 (:REWRITE ADE::LEN-NTHCDR))
 (117 18 (:REWRITE ADE::BV-IS-TRUE-LIST))
 (90 42 (:REWRITE APPEND-WHEN-NOT-CONSP))
 (90 18 (:DEFINITION LEN))
 (81 9 (:DEFINITION TRUE-LISTP))
 (80 80 (:REWRITE DEFAULT-CDR))
 (65 65 (:REWRITE NTH-WHEN-PREFIXP))
 (48 8 (:REWRITE APPEND-ATOM-UNDER-LIST-EQUIV))
 (45 11 (:REWRITE ADE::QUEUE2$OUT-ACT-INACTIVE))
 (36 18 (:TYPE-PRESCRIPTION ADE::BVP-NTHCDR))
 (32 32 (:LINEAR LEN-WHEN-PREFIXP))
 (27 9 (:REWRITE ADE::BVP-NTHCDR))
 (21 21 (:REWRITE DEFAULT-CAR))
 (18 9 (:REWRITE DEFAULT-<-1))
 (16 16 (:LINEAR ADE::A-HELPFUL-LEMMA-FOR-TREE-INDUCTIONS))
 (9 9 (:REWRITE DEFAULT-<-2))
 (4 4 (:REWRITE DEFAULT-UNARY-MINUS))
 )
(ADE::QUEUE2$STATE-ALT
 (310 31 (:DEFINITION NTHCDR))
 (188 170 (:REWRITE DEFAULT-+-2))
 (186 31 (:REWRITE COMMUTATIVITY-OF-+))
 (170 170 (:REWRITE DEFAULT-+-1))
 (144 20 (:DEFINITION BINARY-APPEND))
 (144 9 (:REWRITE ADE::LEN-NTHCDR))
 (117 18 (:REWRITE ADE::BV-IS-TRUE-LIST))
 (90 18 (:DEFINITION LEN))
 (88 40 (:REWRITE APPEND-WHEN-NOT-CONSP))
 (81 9 (:DEFINITION TRUE-LISTP))
 (78 78 (:REWRITE DEFAULT-CDR))
 (48 8 (:REWRITE APPEND-ATOM-UNDER-LIST-EQUIV))
 (36 18 (:TYPE-PRESCRIPTION ADE::BVP-NTHCDR))
 (35 35 (:REWRITE NTH-WHEN-PREFIXP))
 (32 32 (:LINEAR LEN-WHEN-PREFIXP))
 (27 9 (:REWRITE ADE::BVP-NTHCDR))
 (20 20 (:REWRITE DEFAULT-CAR))
 (18 9 (:REWRITE DEFAULT-<-1))
 (16 16 (:LINEAR ADE::A-HELPFUL-LEMMA-FOR-TREE-INDUCTIONS))
 (9 9 (:REWRITE DEFAULT-<-2))
 (4 4 (:REWRITE DEFAULT-UNARY-MINUS))
 )
(ADE::QUEUE2$RUN)
(DEFOPENER-HINT
 (5 5 (:TYPE-PRESCRIPTION LAST))
 )
(DEFOPENER-TEMP)
(ADE::OPEN-QUEUE2$RUN-ZP)
(DEFOPENER-HINT
 (5 5 (:TYPE-PRESCRIPTION LAST))
 )
(DEFOPENER-TEMP)
(ADE::OPEN-QUEUE2$RUN)
(ADE::QUEUE2$RUN-PLUS
 (87 25 (:REWRITE ZP-OPEN))
 (32 15 (:REWRITE DEFAULT-CDR))
 (27 27 (:REWRITE DEFAULT-<-2))
 (27 27 (:REWRITE DEFAULT-<-1))
 (27 10 (:REWRITE DEFAULT-CAR))
 (24 12 (:TYPE-PRESCRIPTION TRUE-LISTP-NTHCDR-TYPE-PRESCRIPTION))
 (23 23 (:REWRITE DEFAULT-+-2))
 (23 23 (:REWRITE DEFAULT-+-1))
 (16 8 (:REWRITE FOLD-CONSTS-IN-+))
 (12 12 (:TYPE-PRESCRIPTION TRUE-LISTP))
 )
(ADE::QUEUE2$INPUT-FORMAT-N
 (6 2 (:REWRITE ADE::BV-IS-TRUE-LIST))
 (5 1 (:DEFINITION TRUE-LISTP))
 (4 4 (:TYPE-PRESCRIPTION ADE::BVP))
 (4 4 (:REWRITE DEFAULT-<-2))
 (4 4 (:REWRITE DEFAULT-<-1))
 (2 2 (:REWRITE DEFAULT-CDR))
 (2 2 (:REWRITE DEFAULT-CAR))
 )
(DEFOPENER-HINT
 (5 5 (:TYPE-PRESCRIPTION LAST))
 )
(DEFOPENER-TEMP)
(ADE::OPEN-QUEUE2$INPUT-FORMAT-N-ZP)
(DEFOPENER-HINT
 (5 5 (:TYPE-PRESCRIPTION LAST))
 )
(DEFOPENER-TEMP)
(ADE::OPEN-QUEUE2$INPUT-FORMAT-N)
(ADE::QUEUE2$INPUT-FORMAT-PLUS
 (38 38 (:REWRITE DEFAULT-<-2))
 (38 38 (:REWRITE DEFAULT-<-1))
 (28 28 (:REWRITE DEFAULT-+-2))
 (28 28 (:REWRITE DEFAULT-+-1))
 (27 15 (:REWRITE DEFAULT-CDR))
 (27 15 (:REWRITE DEFAULT-CAR))
 (24 12 (:TYPE-PRESCRIPTION TRUE-LISTP-NTHCDR-TYPE-PRESCRIPTION))
 (12 12 (:TYPE-PRESCRIPTION TRUE-LISTP))
 )
(ADE::QUEUE2$DE-N
 (90 30 (:REWRITE ZP-OPEN))
 (28 2 (:DEFINITION ADE::QUEUE2$RUN))
 (24 24 (:REWRITE DEFAULT-<-2))
 (24 24 (:REWRITE DEFAULT-<-1))
 (7 7 (:REWRITE DEFAULT-CDR))
 (7 7 (:REWRITE DEFAULT-CAR))
 (7 7 (:REWRITE DEFAULT-+-2))
 (7 7 (:REWRITE DEFAULT-+-1))
 (3 3 (:REWRITE ADE::QUEUE2$INPUT-FORMAT-PLUS))
 (2 2 (:REWRITE ADE::DE-PLUS))
 )
(ADE::QUEUE2$EXTRACT)
(ADE::QUEUE2$EXTRACT-NOT-EMPTY
 (120 120 (:REWRITE NTH-WHEN-PREFIXP))
 (80 40 (:TYPE-PRESCRIPTION ADE::BOOLEANP-JOINT-ACT))
 (52 34 (:REWRITE DEFAULT-+-2))
 (48 24 (:TYPE-PRESCRIPTION ADE::BOOLEANP-QUEUE2$OUT-ACT))
 (48 12 (:DEFINITION STRIP-CARS))
 (42 42 (:REWRITE DEFAULT-CDR))
 (40 40 (:TYPE-PRESCRIPTION BOOLEANP))
 (40 4 (:DEFINITION NTHCDR))
 (34 34 (:REWRITE DEFAULT-+-1))
 (29 29 (:REWRITE DEFAULT-CAR))
 (24 4 (:REWRITE COMMUTATIVITY-OF-+))
 (20 4 (:REWRITE ADE::NFIX-OF-NAT))
 (16 16 (:LINEAR LEN-WHEN-PREFIXP))
 (12 4 (:REWRITE FOLD-CONSTS-IN-+))
 (12 4 (:DEFINITION NATP))
 (8 8 (:REWRITE DEFAULT-<-2))
 (8 8 (:REWRITE DEFAULT-<-1))
 (8 8 (:LINEAR ADE::A-HELPFUL-LEMMA-FOR-TREE-INDUCTIONS))
 (8 4 (:REWRITE ADE::QUEUE2$OUT-ACT-INACTIVE))
 (4 4 (:TYPE-PRESCRIPTION NATP))
 )
(ADE::QUEUE2$EXTRACTED-STEP
 (24 12 (:TYPE-PRESCRIPTION ADE::BOOLEANP-QUEUE2$IN-ACT))
 (18 18 (:TYPE-PRESCRIPTION ADE::QUEUE2$INPUT-FORMAT))
 (12 6 (:TYPE-PRESCRIPTION ADE::BOOLEANP-QUEUE2$OUT-ACT))
 )
(ADE::QUEUE2$EXTRACTED-STEP-CORRECT
 (1784 134 (:DEFINITION NTHCDR))
 (1461 836 (:REWRITE DEFAULT-+-2))
 (1237 1237 (:REWRITE NTH-WHEN-PREFIXP))
 (1026 134 (:REWRITE COMMUTATIVITY-OF-+))
 (947 836 (:REWRITE DEFAULT-+-1))
 (654 654 (:REWRITE DEFAULT-CDR))
 (513 134 (:REWRITE FOLD-CONSTS-IN-+))
 (384 96 (:DEFINITION STRIP-CARS))
 (364 22 (:REWRITE ADE::LEN-NTHCDR))
 (348 297 (:REWRITE DEFAULT-CAR))
 (326 44 (:REWRITE ADE::BV-IS-TRUE-LIST))
 (238 22 (:DEFINITION TRUE-LISTP))
 (217 23 (:DEFINITION PAIRLIS$))
 (170 17 (:DEFINITION ADE::V-THREEFIX))
 (132 22 (:DEFINITION BINARY-APPEND))
 (128 44 (:TYPE-PRESCRIPTION ADE::BVP-NTHCDR))
 (119 17 (:REWRITE ADE::CAR-V-THREEFIX))
 (110 44 (:REWRITE APPEND-WHEN-NOT-CONSP))
 (68 34 (:DEFINITION ADE::3V-FIX))
 (66 34 (:REWRITE DEFAULT-<-1))
 (66 22 (:REWRITE ADE::BVP-NTHCDR))
 (54 34 (:REWRITE DEFAULT-<-2))
 (40 40 (:LINEAR LEN-WHEN-PREFIXP))
 (34 34 (:TYPE-PRESCRIPTION ADE::V-THREEFIX))
 (34 34 (:TYPE-PRESCRIPTION ADE::3VP))
 (20 20 (:LINEAR ADE::A-HELPFUL-LEMMA-FOR-TREE-INDUCTIONS))
 (20 10 (:REWRITE ADE::QUEUE2$IN-ACT-INACTIVE))
 (16 8 (:REWRITE ADE::QUEUE2$OUT-ACT-INACTIVE))
 (8 8 (:REWRITE DEFAULT-UNARY-MINUS))
 (6 6 (:TYPE-PRESCRIPTION ADE::FV-IF))
 (3 3 (:REWRITE TAKE-WHEN-ATOM))
 (3 1 (:DEFINITION NATP))
 (1 1 (:TYPE-PRESCRIPTION NATP))
 )
(ADE::QUEUE2$VALID-ST-PRESERVED
 (1330 101 (:DEFINITION NTHCDR))
 (1166 673 (:REWRITE DEFAULT-+-2))
 (1039 1039 (:REWRITE NTH-WHEN-PREFIXP))
 (766 101 (:REWRITE COMMUTATIVITY-OF-+))
 (753 673 (:REWRITE DEFAULT-+-1))
 (509 509 (:REWRITE DEFAULT-CDR))
 (383 101 (:REWRITE FOLD-CONSTS-IN-+))
 (332 83 (:DEFINITION STRIP-CARS))
 (289 17 (:REWRITE ADE::LEN-NTHCDR))
 (255 34 (:REWRITE ADE::BV-IS-TRUE-LIST))
 (245 221 (:REWRITE DEFAULT-CAR))
 (187 17 (:DEFINITION TRUE-LISTP))
 (150 15 (:DEFINITION ADE::V-THREEFIX))
 (118 14 (:DEFINITION PAIRLIS$))
 (102 34 (:TYPE-PRESCRIPTION ADE::BVP-NTHCDR))
 (102 17 (:DEFINITION BINARY-APPEND))
 (90 90 (:LINEAR LEN-WHEN-PREFIXP))
 (85 34 (:REWRITE APPEND-WHEN-NOT-CONSP))
 (56 8 (:REWRITE ADE::CAR-V-THREEFIX))
 (51 17 (:REWRITE ADE::BVP-NTHCDR))
 (46 23 (:DEFINITION ADE::3V-FIX))
 (45 45 (:LINEAR ADE::A-HELPFUL-LEMMA-FOR-TREE-INDUCTIONS))
 (39 39 (:REWRITE-QUOTED-CONSTANT NFIX-UNDER-NAT-EQUIV))
 (35 18 (:REWRITE DEFAULT-<-2))
 (35 18 (:REWRITE DEFAULT-<-1))
 (24 8 (:REWRITE ADE::QUEUE2$OUT-ACT-INACTIVE))
 (23 23 (:TYPE-PRESCRIPTION ADE::3VP))
 (16 16 (:REWRITE DEFAULT-UNARY-MINUS))
 (3 1 (:DEFINITION NATP))
 (1 1 (:TYPE-PRESCRIPTION NATP))
 )
(ADE::QUEUE2$EXTRACT-LEMMA
 (64 64 (:REWRITE NTH-WHEN-PREFIXP))
 (52 13 (:DEFINITION STRIP-CARS))
 (40 4 (:DEFINITION NTHCDR))
 (38 19 (:TYPE-PRESCRIPTION ADE::BOOLEANP-QUEUE2$OUT-ACT))
 (34 34 (:REWRITE DEFAULT-CAR))
 (30 30 (:REWRITE DEFAULT-CDR))
 (24 4 (:REWRITE COMMUTATIVITY-OF-+))
 (22 19 (:REWRITE DEFAULT-+-2))
 (19 19 (:REWRITE DEFAULT-+-1))
 (12 4 (:REWRITE FOLD-CONSTS-IN-+))
 (8 4 (:TYPE-PRESCRIPTION ADE::BOOLEANP-JOINT-ACT))
 (8 4 (:REWRITE ADE::QUEUE2$OUT-ACT-INACTIVE))
 (4 4 (:TYPE-PRESCRIPTION BOOLEANP))
 )
(ADE::QUEUE2$IN-SEQ
 (12 6 (:TYPE-PRESCRIPTION ADE::BOOLEANP-QUEUE2$IN-ACT))
 (6 6 (:TYPE-PRESCRIPTION ADE::QUEUE2$INPUT-FORMAT))
 )
(ADE::QUEUE2$IN-SEQ-NETLIST)
(ADE::QUEUE2$IN-SEQ-LEMMA
 (416 208 (:TYPE-PRESCRIPTION ADE::BOOLEANP-JOINT-ACT))
 (400 40 (:DEFINITION NTHCDR))
 (240 40 (:REWRITE COMMUTATIVITY-OF-+))
 (236 236 (:REWRITE NTH-WHEN-PREFIXP))
 (233 65 (:REWRITE ZP-OPEN))
 (232 232 (:REWRITE DEFAULT-+-2))
 (232 232 (:REWRITE DEFAULT-+-1))
 (213 35 (:DEFINITION BINARY-APPEND))
 (208 208 (:TYPE-PRESCRIPTION BOOLEANP))
 (168 56 (:REWRITE FOLD-CONSTS-IN-+))
 (166 70 (:REWRITE APPEND-WHEN-NOT-CONSP))
 (164 164 (:REWRITE DEFAULT-CAR))
 (131 131 (:REWRITE DEFAULT-CDR))
 (72 36 (:REWRITE ADE::QUEUE2$IN-ACT-INACTIVE))
 (64 64 (:REWRITE DEFAULT-<-2))
 (64 64 (:REWRITE DEFAULT-<-1))
 (28 14 (:REWRITE ADE::QUEUE2$OUT-ACT-INACTIVE))
 (12 12 (:REWRITE ADE::QUEUE2$INPUT-FORMAT-PLUS))
 (6 6 (:REWRITE APPEND-ATOM-UNDER-LIST-EQUIV))
 )
(ADE::QUEUE2$OUT-SEQ
 (12 6 (:TYPE-PRESCRIPTION ADE::BOOLEANP-QUEUE2$OUT-ACT))
 (6 6 (:TYPE-PRESCRIPTION ADE::QUEUE2$INPUT-FORMAT))
 )
(ADE::QUEUE2$OUT-SEQ-NETLIST)
(ADE::QUEUE2$OUT-SEQ-LEMMA
 (430 46 (:DEFINITION NTHCDR))
 (416 208 (:TYPE-PRESCRIPTION ADE::BOOLEANP-JOINT-ACT))
 (250 250 (:REWRITE NTH-WHEN-PREFIXP))
 (240 40 (:REWRITE COMMUTATIVITY-OF-+))
 (233 65 (:REWRITE ZP-OPEN))
 (232 232 (:REWRITE DEFAULT-+-2))
 (232 232 (:REWRITE DEFAULT-+-1))
 (213 35 (:DEFINITION BINARY-APPEND))
 (208 208 (:TYPE-PRESCRIPTION BOOLEANP))
 (168 56 (:REWRITE FOLD-CONSTS-IN-+))
 (166 70 (:REWRITE APPEND-WHEN-NOT-CONSP))
 (161 161 (:REWRITE DEFAULT-CAR))
 (155 137 (:REWRITE DEFAULT-CDR))
 (72 36 (:REWRITE ADE::QUEUE2$OUT-ACT-INACTIVE))
 (64 64 (:REWRITE DEFAULT-<-2))
 (64 64 (:REWRITE DEFAULT-<-1))
 (29 29 (:REWRITE ADE::QUEUE2$EXTRACT-LEMMA))
 (28 14 (:REWRITE ADE::QUEUE2$IN-ACT-INACTIVE))
 (18 18 (:TYPE-PRESCRIPTION ADE::SE))
 (12 12 (:REWRITE ADE::QUEUE2$INPUT-FORMAT-PLUS))
 (6 6 (:REWRITE APPEND-ATOM-UNDER-LIST-EQUIV))
 )
(ADE::QUEUE2$DATAFLOW-CORRECT-AUX
 (175 163 (:TYPE-PRESCRIPTION BINARY-APPEND))
 (53 16 (:REWRITE APPEND-WHEN-NOT-CONSP))
 (52 2 (:DEFINITION ADE::QUEUE2$IN-SEQ))
 (24 10 (:REWRITE DEFAULT-CDR))
 (12 12 (:REWRITE DEFAULT-CAR))
 (8 8 (:REWRITE APPEND-ATOM-UNDER-LIST-EQUIV))
 (8 4 (:TYPE-PRESCRIPTION ADE::BOOLEANP-QUEUE2$IN-ACT))
 (6 2 (:REWRITE CAR-OF-APPEND))
 (5 5 (:REWRITE CONSP-OF-APPEND))
 (4 4 (:TYPE-PRESCRIPTION ADE::QUEUE2$INPUT-FORMAT))
 (4 4 (:TYPE-PRESCRIPTION ADE::QUEUE2$IN-ACT))
 (4 2 (:REWRITE ADE::QUEUE2$IN-ACT-INACTIVE))
 (2 2 (:REWRITE ZP-OPEN))
 (2 2 (:REWRITE NTH-WHEN-PREFIXP))
 (2 2 (:REWRITE DEFAULT-+-2))
 (2 2 (:REWRITE DEFAULT-+-1))
 (2 2 (:REWRITE CDR-OF-APPEND-WHEN-CONSP))
 )
(ADE::QUEUE2$DATAFLOW-CORRECT
 (473 106 (:REWRITE ZP-OPEN))
 (382 61 (:DEFINITION BINARY-APPEND))
 (275 11 (:DEFINITION NTHCDR))
 (202 147 (:REWRITE DEFAULT-+-2))
 (194 155 (:REWRITE DEFAULT-CDR))
 (192 4 (:REWRITE TAKE-OF-TOO-MANY))
 (189 27 (:DEFINITION LEN))
 (182 2 (:DEFINITION TAKE))
 (162 156 (:REWRITE DEFAULT-CAR))
 (148 127 (:REWRITE DEFAULT-<-2))
 (147 147 (:REWRITE DEFAULT-+-1))
 (137 127 (:REWRITE DEFAULT-<-1))
 (94 27 (:REWRITE FOLD-CONSTS-IN-+))
 (88 4 (:REWRITE ADE::NFIX-OF-NAT))
 (78 43 (:REWRITE ADE::QUEUE2$IN-ACT-INACTIVE))
 (77 11 (:REWRITE COMMUTATIVITY-OF-+))
 (72 4 (:DEFINITION NATP))
 (64 2 (:REWRITE CONSP-OF-TAKE))
 (56 56 (:REWRITE NTH-WHEN-PREFIXP))
 (56 6 (:LINEAR ADE::QUEUE2$EXTRACT-NOT-EMPTY))
 (48 27 (:REWRITE ADE::QUEUE2$OUT-ACT-INACTIVE))
 (32 32 (:REWRITE APPEND-ATOM-UNDER-LIST-EQUIV))
 (28 28 (:TYPE-PRESCRIPTION ADE::QUEUE2$STEP))
 (16 4 (:REWRITE TAKE-WHEN-ATOM))
 (14 2 (:DEFINITION NFIX))
 (12 12 (:REWRITE ADE::QUEUE2$RUN-PLUS))
 (12 12 (:LINEAR LEN-WHEN-PREFIXP))
 (10 10 (:REWRITE ADE::QUEUE2$INPUT-FORMAT-PLUS))
 (6 6 (:LINEAR ADE::A-HELPFUL-LEMMA-FOR-TREE-INDUCTIONS))
 (4 4 (:TYPE-PRESCRIPTION NFIX))
 (4 4 (:TYPE-PRESCRIPTION NATP))
 (3 3 (:TYPE-PRESCRIPTION ADE::QUEUE2$RUN))
 )
(ADE::QUEUE2$FUNCTIONALLY-CORRECT
 (205 4 (:DEFINITION ADE::QUEUE2$OUT-SEQ))
 (109 4 (:REWRITE ADE::QUEUE2$EXTRACT-LEMMA))
 (104 4 (:DEFINITION ADE::QUEUE2$IN-SEQ))
 (80 32 (:REWRITE APPEND-WHEN-NOT-CONSP))
 (75 3 (:DEFINITION NTHCDR))
 (54 33 (:REWRITE ZP-OPEN))
 (44 44 (:TYPE-PRESCRIPTION ZP))
 (39 30 (:REWRITE DEFAULT-CDR))
 (32 23 (:REWRITE DEFAULT-+-2))
 (30 30 (:TYPE-PRESCRIPTION LEN))
 (24 24 (:REWRITE DEFAULT-CAR))
 (23 23 (:REWRITE DEFAULT-+-1))
 (21 3 (:REWRITE COMMUTATIVITY-OF-+))
 (21 3 (:DEFINITION LEN))
 (20 5 (:REWRITE ADE::OPEN-QUEUE2$INPUT-FORMAT-N-ZP))
 (20 5 (:REWRITE ADE::OPEN-QUEUE2$INPUT-FORMAT-N))
 (16 16 (:TYPE-PRESCRIPTION ADE::QUEUE2$INPUT-FORMAT))
 (16 8 (:TYPE-PRESCRIPTION ADE::BOOLEANP-QUEUE2$OUT-ACT))
 (16 8 (:TYPE-PRESCRIPTION ADE::BOOLEANP-QUEUE2$IN-ACT))
 (12 3 (:REWRITE ADE::OPEN-QUEUE2$RUN-ZP))
 (12 3 (:REWRITE ADE::OPEN-QUEUE2$RUN))
 (12 3 (:REWRITE ADE::OPEN-DE-N-ZP))
 (12 3 (:REWRITE ADE::OPEN-DE-N))
 (12 3 (:REWRITE FOLD-CONSTS-IN-+))
 (8 8 (:TYPE-PRESCRIPTION ADE::QUEUE2$OUT-ACT))
 (8 8 (:TYPE-PRESCRIPTION ADE::QUEUE2$IN-ACT))
 (8 8 (:REWRITE NTH-WHEN-PREFIXP))
 (8 8 (:REWRITE APPEND-ATOM-UNDER-LIST-EQUIV))
 (8 4 (:REWRITE ADE::QUEUE2$OUT-ACT-INACTIVE))
 (8 4 (:REWRITE ADE::QUEUE2$IN-ACT-INACTIVE))
 (6 3 (:REWRITE DEFAULT-<-2))
 (3 3 (:TYPE-PRESCRIPTION ADE::QUEUE2$RUN))
 (3 3 (:TYPE-PRESCRIPTION ADE::DE-N))
 (3 3 (:REWRITE DEFAULT-<-1))
 )
