(LTL-SEMANTICS-FOR-CIRCUIT)
(LTL-SEMANTICS-FOR-CIRCUITS*)
(REDUCE-PROBLEM-CONJUNCTION
 (296 139 (:REWRITE DEFAULT-+-2))
 (182 139 (:REWRITE DEFAULT-+-1))
 (88 22 (:REWRITE COMMUTATIVITY-OF-+))
 (88 22 (:DEFINITION INTEGER-ABS))
 (88 11 (:DEFINITION LENGTH))
 (70 70 (:REWRITE DEFAULT-CDR))
 (37 28 (:REWRITE DEFAULT-<-2))
 (34 28 (:REWRITE DEFAULT-<-1))
 (30 30 (:REWRITE DEFAULT-CAR))
 (22 22 (:REWRITE DEFAULT-UNARY-MINUS))
 (11 11 (:REWRITE DEFAULT-REALPART))
 (11 11 (:REWRITE DEFAULT-NUMERATOR))
 (11 11 (:REWRITE DEFAULT-IMAGPART))
 (11 11 (:REWRITE DEFAULT-DENOMINATOR))
 (11 11 (:REWRITE DEFAULT-COERCE-2))
 (11 11 (:REWRITE DEFAULT-COERCE-1))
 (1 1 (:TYPE-PRESCRIPTION TRUE-LISTP))
 )
(REDUCE-PROBLEM-CONE)
(REDUCE-PROBLEM-CONE*)
(COMPOSITIONAL-REDUCTION)
(LTL-SEMANTICS*-APPEND-REDUCTION
 (22308 29 (:REWRITE CIRCUIT-BISIM-IMPLIES-SAME-LTL-SEMANTICS))
 (12883 29 (:REWRITE CREATE-KRIPKE-PRODUCES-CIRCUIT-MODEL))
 (12825 29 (:DEFINITION CIRCUITP))
 (9367 29 (:DEFINITION CIRCUIT-MODELP))
 (7866 29 (:DEFINITION CONSISTENT-EQUATION-RECORD-P))
 (5799 406 (:DEFINITION MEMBERP))
 (3741 116 (:DEFINITION SUBSET))
 (3392 29 (:DEFINITION FIND-VARIABLES))
 (3132 116 (:REWRITE ORDERED-IMPLIES-UNIQUE))
 (2900 58 (:DEFINITION UNIQUEP))
 (2784 116 (:DEFINITION ORDEREDP))
 (2135 2117 (:REWRITE DEFAULT-CAR))
 (2084 2078 (:REWRITE DEFAULT-CDR))
 (1657 1657 (:TYPE-PRESCRIPTION MEMBERP))
 (1595 58 (:DEFINITION STRICT-EVALUATION-LIST-P))
 (1508 29 (:DEFINITION TRANSITION-SUBSET-P))
 (1392 348 (:REWRITE <<-TRICHOTOMY))
 (1334 1334 (:REWRITE VARIABLES-IN-LABEL-ARE-T-IN-Q))
 (1334 1334 (:REWRITE STRICT-EVALUATION-P-EXPANDED))
 (1334 1334 (:REWRITE EVALUATION-EQ-VARS-REDUCTION))
 (1305 58 (:DEFINITION ONLY-EVALUATIONS-P))
 (1218 29 (:DEFINITION ONLY-ALL-TRUTHS-P))
 (1218 29 (:DEFINITION LABEL-SUBSET-VARS))
 (1160 58 (:DEFINITION STRICT-EVALUATION-P))
 (928 928 (:TYPE-PRESCRIPTION <<))
 (928 232 (:REWRITE PROPER-SUBSET-IS-STRONGER-THAN-SUBSET))
 (899 29 (:DEFINITION ALL-TRUTHSP-LABEL))
 (783 783 (:REWRITE TRUTHP-LABEL-TO-SUBSET))
 (783 783 (:REWRITE TRANSITION-SUBSET-P-EXPANDED))
 (783 783 (:REWRITE ONLY-TRUTHSP-AND-SUBSET-TO-SUBSET))
 (783 783 (:REWRITE ALL-TRUTHSP-LABEL-EXPANDED))
 (696 116 (:REWRITE <<-ASYMMETRIC))
 (696 58 (:DEFINITION EVALUATION-P))
 (580 580 (:TYPE-PRESCRIPTION ORDEREDP))
 (580 29 (:DEFINITION ONLY-TRUTH-P))
 (553 553 (:TYPE-PRESCRIPTION SUBSET))
 (464 464 (:TYPE-PRESCRIPTION PROPER-SUBSET))
 (406 58 (:REWRITE NEXT-STATES-IN-STATES-CLARIFIED))
 (348 348 (:REWRITE MODELP-CHARACTERIZATION))
 (348 348 (:REWRITE <<-TRANSITIVE))
 (348 174 (:DEFINITION MV-NTH))
 (319 87 (:DEFINITION LEN))
 (290 290 (:TYPE-PRESCRIPTION STRICT-EVALUATION-LIST-P))
 (290 290 (:TYPE-PRESCRIPTION ONLY-EVALUATIONS-P))
 (290 290 (:TYPE-PRESCRIPTION EVALUATION-P))
 (261 29 (:DEFINITION TRUTHP-LABEL))
 (261 29 (:DEFINITION CONS-LIST-P))
 (234 234 (:TYPE-PRESCRIPTION UNIQUEP))
 (232 232 (:REWRITE SUBSET-IS-TRANSITIVE))
 (232 232 (:REWRITE PROPER-SUBSET-IS-TRANSITIVE))
 (203 203 (:TYPE-PRESCRIPTION ALL-TRUTHSP-LABEL))
 (174 174 (:TYPE-PRESCRIPTION LEN))
 (145 145 (:TYPE-PRESCRIPTION TRUTHP-LABEL))
 (145 145 (:TYPE-PRESCRIPTION TRANSITION-SUBSET-P))
 (145 145 (:TYPE-PRESCRIPTION ONLY-TRUTH-P))
 (145 145 (:TYPE-PRESCRIPTION ONLY-ALL-TRUTHS-P))
 (145 145 (:TYPE-PRESCRIPTION NEXT-STATES-IN-STATES))
 (145 145 (:TYPE-PRESCRIPTION LABEL-SUBSET-VARS))
 (145 145 (:TYPE-PRESCRIPTION CONS-LIST-P))
 (116 116 (:TYPE-PRESCRIPTION FIND-VARIABLES))
 (116 116 (:REWRITE EVALUATIONP-FOR-SUBSET))
 (116 116 (:REWRITE EVALUATION-P-ONLY-EVALUATIONS-REDUCTION))
 (116 58 (:REWRITE DEFAULT-+-2))
 (87 87 (:REWRITE ALL-TRUTHS-P-FROM-ONLY-ALL-TRUTHS-P))
 (87 29 (:REWRITE LTL-SEMANTICS-IS-DECOMPOSED-OVER-CONJUNCTION))
 (58 58 (:TYPE-PRESCRIPTION LTL-FORMULAP))
 (58 58 (:TYPE-PRESCRIPTION BOOLEANP))
 (58 58 (:TYPE-PRESCRIPTION ALL-EVALUATIONS-P))
 (58 58 (:REWRITE DEFAULT-+-1))
 (58 58 (:REWRITE COMPATIBLE-PATHS-HAVE-ONLY-STATES))
 (50 25 (:TYPE-PRESCRIPTION TRUE-LISTP-APPEND))
 (29 29 (:TYPE-PRESCRIPTION CIRCUITP))
 (29 29 (:TYPE-PRESCRIPTION CIRCUIT-MODELP))
 (29 29 (:REWRITE TRUTHP-LABEL-FROM-ONLY-TRUTHP))
 (29 29 (:REWRITE LABEL-SUBSET-SUBSET-REDUCTION))
 (25 25 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (25 25 (:TYPE-PRESCRIPTION BINARY-APPEND))
 )
(CONJUNCTION-PRODUCES-CORRECT-LIST
 (24006 44 (:REWRITE CIRCUIT-BISIM-IMPLIES-SAME-LTL-SEMANTICS))
 (13594 32 (:REWRITE CREATE-KRIPKE-PRODUCES-CIRCUIT-MODEL))
 (13530 32 (:DEFINITION CIRCUITP))
 (10336 32 (:DEFINITION CIRCUIT-MODELP))
 (8058 32 (:DEFINITION CONSISTENT-EQUATION-RECORD-P))
 (4128 128 (:DEFINITION SUBSET))
 (3456 128 (:REWRITE ORDERED-IMPLIES-UNIQUE))
 (3305 2759 (:REWRITE DEFAULT-CAR))
 (3200 64 (:DEFINITION UNIQUEP))
 (3072 128 (:DEFINITION ORDEREDP))
 (3066 32 (:DEFINITION FIND-VARIABLES))
 (2785 2719 (:REWRITE DEFAULT-CDR))
 (2152 2152 (:TYPE-PRESCRIPTION MEMBERP))
 (1760 64 (:DEFINITION STRICT-EVALUATION-LIST-P))
 (1664 32 (:DEFINITION TRANSITION-SUBSET-P))
 (1536 384 (:REWRITE <<-TRICHOTOMY))
 (1494 1494 (:REWRITE TRUTHP-LABEL-TO-SUBSET))
 (1494 1494 (:REWRITE TRANSITION-SUBSET-P-EXPANDED))
 (1494 1494 (:REWRITE ONLY-TRUTHSP-AND-SUBSET-TO-SUBSET))
 (1494 1494 (:REWRITE ALL-TRUTHSP-LABEL-EXPANDED))
 (1472 1472 (:REWRITE VARIABLES-IN-LABEL-ARE-T-IN-Q))
 (1472 1472 (:REWRITE STRICT-EVALUATION-P-EXPANDED))
 (1472 1472 (:REWRITE EVALUATION-EQ-VARS-REDUCTION))
 (1440 64 (:DEFINITION ONLY-EVALUATIONS-P))
 (1344 32 (:DEFINITION ONLY-ALL-TRUTHS-P))
 (1344 32 (:DEFINITION LABEL-SUBSET-VARS))
 (1280 64 (:DEFINITION STRICT-EVALUATION-P))
 (1024 1024 (:TYPE-PRESCRIPTION <<))
 (1024 256 (:REWRITE PROPER-SUBSET-IS-STRONGER-THAN-SUBSET))
 (992 32 (:DEFINITION ALL-TRUTHSP-LABEL))
 (768 128 (:REWRITE <<-ASYMMETRIC))
 (768 64 (:DEFINITION EVALUATION-P))
 (640 640 (:TYPE-PRESCRIPTION ORDEREDP))
 (640 32 (:DEFINITION ONLY-TRUTH-P))
 (624 624 (:TYPE-PRESCRIPTION SUBSET))
 (512 512 (:TYPE-PRESCRIPTION PROPER-SUBSET))
 (474 237 (:REWRITE DEFAULT-+-2))
 (448 64 (:REWRITE NEXT-STATES-IN-STATES-CLARIFIED))
 (384 384 (:REWRITE MODELP-CHARACTERIZATION))
 (384 384 (:REWRITE <<-TRANSITIVE))
 (384 192 (:DEFINITION MV-NTH))
 (320 320 (:TYPE-PRESCRIPTION STRICT-EVALUATION-LIST-P))
 (320 320 (:TYPE-PRESCRIPTION ONLY-EVALUATIONS-P))
 (320 320 (:TYPE-PRESCRIPTION EVALUATION-P))
 (288 32 (:DEFINITION TRUTHP-LABEL))
 (288 32 (:DEFINITION CONS-LIST-P))
 (272 272 (:TYPE-PRESCRIPTION UNIQUEP))
 (256 256 (:REWRITE SUBSET-IS-TRANSITIVE))
 (256 256 (:REWRITE PROPER-SUBSET-IS-TRANSITIVE))
 (237 237 (:REWRITE DEFAULT-+-1))
 (224 224 (:TYPE-PRESCRIPTION ALL-TRUTHSP-LABEL))
 (160 160 (:TYPE-PRESCRIPTION TRUTHP-LABEL))
 (160 160 (:TYPE-PRESCRIPTION TRANSITION-SUBSET-P))
 (160 160 (:TYPE-PRESCRIPTION ONLY-TRUTH-P))
 (160 160 (:TYPE-PRESCRIPTION ONLY-ALL-TRUTHS-P))
 (160 160 (:TYPE-PRESCRIPTION NEXT-STATES-IN-STATES))
 (160 160 (:TYPE-PRESCRIPTION LABEL-SUBSET-VARS))
 (160 160 (:TYPE-PRESCRIPTION CONS-LIST-P))
 (128 128 (:TYPE-PRESCRIPTION FIND-VARIABLES))
 (128 128 (:REWRITE EVALUATIONP-FOR-SUBSET))
 (128 128 (:REWRITE EVALUATION-P-ONLY-EVALUATIONS-REDUCTION))
 (125 21 (:LINEAR CONSP-TO-LEN-EXPANDED))
 (96 96 (:REWRITE ALL-TRUTHS-P-FROM-ONLY-ALL-TRUTHS-P))
 (64 64 (:TYPE-PRESCRIPTION BOOLEANP))
 (64 64 (:TYPE-PRESCRIPTION ALL-EVALUATIONS-P))
 (64 64 (:REWRITE COMPATIBLE-PATHS-HAVE-ONLY-STATES))
 (32 32 (:TYPE-PRESCRIPTION CIRCUITP))
 (32 32 (:TYPE-PRESCRIPTION CIRCUIT-MODELP))
 (32 32 (:REWRITE TRUTHP-LABEL-FROM-ONLY-TRUTHP))
 (32 32 (:REWRITE LABEL-SUBSET-SUBSET-REDUCTION))
 (6 1 (:DEFINITION BINARY-APPEND))
 )
(NOT-MEMBERP-UNION-REDUCTION
 (49 49 (:REWRITE TRUTHP-LABEL-TO-SUBSET))
 (49 49 (:REWRITE TRANSITION-SUBSET-P-EXPANDED))
 (49 49 (:REWRITE ONLY-TRUTHSP-AND-SUBSET-TO-SUBSET))
 (49 49 (:REWRITE ALL-TRUTHSP-LABEL-EXPANDED))
 (38 37 (:REWRITE DEFAULT-CAR))
 (27 26 (:REWRITE DEFAULT-CDR))
 (13 13 (:TYPE-PRESCRIPTION SET-UNION))
 )
(UNIQUEP-SET-UNION-REDUCTION
 (504 126 (:REWRITE <<-TRICHOTOMY))
 (336 336 (:TYPE-PRESCRIPTION <<))
 (252 42 (:REWRITE <<-ASYMMETRIC))
 (157 138 (:REWRITE DEFAULT-CAR))
 (126 126 (:REWRITE <<-TRANSITIVE))
 (111 111 (:TYPE-PRESCRIPTION SET-UNION))
 (50 50 (:REWRITE TRUTHP-LABEL-TO-SUBSET))
 (50 50 (:REWRITE TRANSITION-SUBSET-P-EXPANDED))
 (50 50 (:REWRITE ONLY-TRUTHSP-AND-SUBSET-TO-SUBSET))
 (50 50 (:REWRITE ALL-TRUTHSP-LABEL-EXPANDED))
 )
(CONSISTENT-EQUATION-RECORD-P-EXPANDED)
(SET-UNION-SUBSET-REDUCTION
 (136 34 (:REWRITE PROPER-SUBSET-IS-STRONGER-THAN-SUBSET))
 (65 65 (:TYPE-PRESCRIPTION PROPER-SUBSET))
 (52 51 (:REWRITE DEFAULT-CAR))
 (48 48 (:REWRITE TRUTHP-LABEL-TO-SUBSET))
 (48 48 (:REWRITE TRANSITION-SUBSET-P-EXPANDED))
 (48 48 (:REWRITE ONLY-TRUTHSP-AND-SUBSET-TO-SUBSET))
 (48 48 (:REWRITE ALL-TRUTHSP-LABEL-EXPANDED))
 (41 40 (:REWRITE DEFAULT-CDR))
 (34 34 (:REWRITE PROPER-SUBSET-IS-TRANSITIVE))
 (11 11 (:TYPE-PRESCRIPTION SET-UNION))
 (3 3 (:REWRITE PROPER-SUBSET-IS-IRREFLEXIVE))
 )
(FIND-VARIABLES*-SUBSET-OF-VARIABLES
 (216 8 (:REWRITE ORDERED-IMPLIES-UNIQUE))
 (192 8 (:DEFINITION ORDEREDP))
 (96 24 (:REWRITE <<-TRICHOTOMY))
 (64 64 (:TYPE-PRESCRIPTION <<))
 (53 53 (:REWRITE DEFAULT-CDR))
 (48 12 (:REWRITE PROPER-SUBSET-IS-STRONGER-THAN-SUBSET))
 (48 8 (:REWRITE <<-ASYMMETRIC))
 (41 41 (:REWRITE DEFAULT-CAR))
 (40 40 (:TYPE-PRESCRIPTION ORDEREDP))
 (28 28 (:REWRITE TRUTHP-LABEL-TO-SUBSET))
 (28 28 (:REWRITE TRANSITION-SUBSET-P-EXPANDED))
 (28 28 (:REWRITE ONLY-TRUTHSP-AND-SUBSET-TO-SUBSET))
 (28 28 (:REWRITE ALL-TRUTHSP-LABEL-EXPANDED))
 (24 24 (:TYPE-PRESCRIPTION PROPER-SUBSET))
 (24 24 (:REWRITE <<-TRANSITIVE))
 (12 12 (:REWRITE SUBSET-IS-TRANSITIVE))
 (12 12 (:REWRITE PROPER-SUBSET-IS-TRANSITIVE))
 (6 6 (:REWRITE VARIABLES-IN-LABEL-ARE-T-IN-Q))
 (6 6 (:REWRITE STRICT-EVALUATION-P-EXPANDED))
 (6 6 (:REWRITE EVALUATION-EQ-VARS-REDUCTION))
 )
(FIND-VARIABLES*-IS-SUBSET-CONCRETIZED
 (75 1 (:DEFINITION FIND-VARIABLES*))
 (72 1 (:DEFINITION FIND-VARIABLES))
 (57 5 (:DEFINITION MEMBERP))
 (54 2 (:REWRITE ORDERED-IMPLIES-UNIQUE))
 (48 2 (:DEFINITION ORDEREDP))
 (43 1 (:DEFINITION UNIQUEP))
 (24 6 (:REWRITE <<-TRICHOTOMY))
 (21 21 (:REWRITE DEFAULT-CDR))
 (21 21 (:REWRITE DEFAULT-CAR))
 (16 16 (:TYPE-PRESCRIPTION <<))
 (12 2 (:REWRITE <<-ASYMMETRIC))
 (11 3 (:DEFINITION LEN))
 (10 10 (:TYPE-PRESCRIPTION ORDEREDP))
 (9 9 (:REWRITE TRUTHP-LABEL-TO-SUBSET))
 (9 9 (:REWRITE TRANSITION-SUBSET-P-EXPANDED))
 (9 9 (:REWRITE ONLY-TRUTHSP-AND-SUBSET-TO-SUBSET))
 (9 9 (:REWRITE ALL-TRUTHSP-LABEL-EXPANDED))
 (6 6 (:TYPE-PRESCRIPTION LEN))
 (6 6 (:REWRITE VARIABLES-IN-LABEL-ARE-T-IN-Q))
 (6 6 (:REWRITE STRICT-EVALUATION-P-EXPANDED))
 (6 6 (:REWRITE EVALUATION-EQ-VARS-REDUCTION))
 (6 6 (:REWRITE <<-TRANSITIVE))
 (4 2 (:REWRITE DEFAULT-+-2))
 (4 1 (:REWRITE PROPER-SUBSET-IS-STRONGER-THAN-SUBSET))
 (2 2 (:REWRITE DEFAULT-+-1))
 (1 1 (:TYPE-PRESCRIPTION PROPER-SUBSET))
 (1 1 (:REWRITE SUBSET-IS-TRANSITIVE))
 (1 1 (:REWRITE PROPER-SUBSET-IS-TRANSITIVE))
 (1 1 (:REWRITE PROPER-SUBSET-IS-IRREFLEXIVE))
 )
(FIND-VARIABLES-1-PASS-IS-SUBSET
 (237 3 (:DEFINITION FIND-VARIABLES*))
 (228 3 (:DEFINITION FIND-VARIABLES))
 (218 20 (:DEFINITION MEMBERP))
 (216 8 (:REWRITE ORDERED-IMPLIES-UNIQUE))
 (192 8 (:DEFINITION ORDEREDP))
 (172 4 (:DEFINITION UNIQUEP))
 (96 24 (:REWRITE <<-TRICHOTOMY))
 (95 95 (:REWRITE DEFAULT-CAR))
 (83 83 (:REWRITE DEFAULT-CDR))
 (64 64 (:TYPE-PRESCRIPTION <<))
 (56 14 (:REWRITE PROPER-SUBSET-IS-STRONGER-THAN-SUBSET))
 (48 8 (:REWRITE <<-ASYMMETRIC))
 (40 40 (:TYPE-PRESCRIPTION ORDEREDP))
 (37 37 (:REWRITE TRUTHP-LABEL-TO-SUBSET))
 (37 37 (:REWRITE TRANSITION-SUBSET-P-EXPANDED))
 (37 37 (:REWRITE ONLY-TRUTHSP-AND-SUBSET-TO-SUBSET))
 (37 37 (:REWRITE ALL-TRUTHSP-LABEL-EXPANDED))
 (33 9 (:DEFINITION LEN))
 (28 28 (:TYPE-PRESCRIPTION PROPER-SUBSET))
 (24 24 (:REWRITE <<-TRANSITIVE))
 (18 18 (:TYPE-PRESCRIPTION LEN))
 (15 15 (:REWRITE VARIABLES-IN-LABEL-ARE-T-IN-Q))
 (15 15 (:REWRITE STRICT-EVALUATION-P-EXPANDED))
 (15 15 (:REWRITE EVALUATION-EQ-VARS-REDUCTION))
 (14 14 (:REWRITE SUBSET-IS-TRANSITIVE))
 (14 14 (:REWRITE PROPER-SUBSET-IS-TRANSITIVE))
 (12 6 (:REWRITE DEFAULT-+-2))
 (6 6 (:TYPE-PRESCRIPTION FIND-ALL-VARIABLES-1-PASS))
 (6 6 (:REWRITE DEFAULT-+-1))
 )
(MEMBERP-UNION-REDUCTION-1
 (93 6 (:REWRITE NOT-MEMBERP-UNION-REDUCTION))
 (47 47 (:REWRITE TRUTHP-LABEL-TO-SUBSET))
 (47 47 (:REWRITE TRANSITION-SUBSET-P-EXPANDED))
 (47 47 (:REWRITE ONLY-TRUTHSP-AND-SUBSET-TO-SUBSET))
 (47 47 (:REWRITE ALL-TRUTHSP-LABEL-EXPANDED))
 (33 32 (:REWRITE DEFAULT-CAR))
 (28 27 (:REWRITE DEFAULT-CDR))
 (13 13 (:TYPE-PRESCRIPTION SET-UNION))
 )
(MEMBERP-FIND-ALL-VARIABLES-REDUCTION
 (1242 46 (:REWRITE ORDERED-IMPLIES-UNIQUE))
 (1104 46 (:DEFINITION ORDEREDP))
 (765 9 (:DEFINITION FIND-ALL-VARIABLES-1-PASS))
 (711 9 (:DEFINITION FIND-VARIABLES*))
 (684 9 (:DEFINITION FIND-VARIABLES))
 (552 138 (:REWRITE <<-TRICHOTOMY))
 (368 368 (:TYPE-PRESCRIPTION <<))
 (332 332 (:REWRITE DEFAULT-CDR))
 (326 326 (:REWRITE DEFAULT-CAR))
 (276 46 (:REWRITE <<-ASYMMETRIC))
 (230 230 (:TYPE-PRESCRIPTION ORDEREDP))
 (138 138 (:REWRITE <<-TRANSITIVE))
 (117 117 (:REWRITE TRUTHP-LABEL-TO-SUBSET))
 (117 117 (:REWRITE TRANSITION-SUBSET-P-EXPANDED))
 (117 117 (:REWRITE ONLY-TRUTHSP-AND-SUBSET-TO-SUBSET))
 (117 117 (:REWRITE ALL-TRUTHSP-LABEL-EXPANDED))
 (99 27 (:DEFINITION LEN))
 (80 20 (:REWRITE PROPER-SUBSET-IS-STRONGER-THAN-SUBSET))
 (80 4 (:DEFINITION SUBSET))
 (54 54 (:TYPE-PRESCRIPTION LEN))
 (45 45 (:REWRITE VARIABLES-IN-LABEL-ARE-T-IN-Q))
 (45 45 (:REWRITE STRICT-EVALUATION-P-EXPANDED))
 (45 45 (:REWRITE EVALUATION-EQ-VARS-REDUCTION))
 (36 18 (:REWRITE DEFAULT-+-2))
 (34 34 (:TYPE-PRESCRIPTION PROPER-SUBSET))
 (20 20 (:REWRITE PROPER-SUBSET-IS-TRANSITIVE))
 (18 18 (:REWRITE DEFAULT-+-1))
 (11 7 (:TYPE-PRESCRIPTION FIND-ALL-VARIABLES))
 (6 6 (:REWRITE PROPER-SUBSET-IS-IRREFLEXIVE))
 (4 4 (:TYPE-PRESCRIPTION SET-UNION))
 )
(FIND-ALL-VARIABLES-PRODUCES-SUBSET
 (2187 9 (:DEFINITION FIND-ALL-VARIABLES))
 (972 36 (:REWRITE ORDERED-IMPLIES-UNIQUE))
 (864 36 (:DEFINITION ORDEREDP))
 (774 18 (:DEFINITION UNIQUEP))
 (765 9 (:DEFINITION FIND-ALL-VARIABLES-1-PASS))
 (732 69 (:DEFINITION MEMBERP))
 (711 9 (:DEFINITION FIND-VARIABLES*))
 (684 9 (:DEFINITION FIND-VARIABLES))
 (432 108 (:REWRITE <<-TRICHOTOMY))
 (326 326 (:REWRITE DEFAULT-CAR))
 (304 304 (:REWRITE DEFAULT-CDR))
 (288 288 (:TYPE-PRESCRIPTION <<))
 (216 36 (:REWRITE <<-ASYMMETRIC))
 (196 49 (:REWRITE PROPER-SUBSET-IS-STRONGER-THAN-SUBSET))
 (180 180 (:TYPE-PRESCRIPTION ORDEREDP))
 (153 49 (:REWRITE SUBSET-IS-TRANSITIVE))
 (127 127 (:REWRITE TRUTHP-LABEL-TO-SUBSET))
 (127 127 (:REWRITE TRANSITION-SUBSET-P-EXPANDED))
 (127 127 (:REWRITE ONLY-TRUTHSP-AND-SUBSET-TO-SUBSET))
 (127 127 (:REWRITE ALL-TRUTHSP-LABEL-EXPANDED))
 (108 108 (:REWRITE <<-TRANSITIVE))
 (99 27 (:DEFINITION LEN))
 (89 89 (:TYPE-PRESCRIPTION PROPER-SUBSET))
 (54 54 (:TYPE-PRESCRIPTION LEN))
 (49 49 (:REWRITE PROPER-SUBSET-IS-TRANSITIVE))
 (45 45 (:REWRITE VARIABLES-IN-LABEL-ARE-T-IN-Q))
 (45 45 (:REWRITE STRICT-EVALUATION-P-EXPANDED))
 (45 45 (:REWRITE EVALUATION-EQ-VARS-REDUCTION))
 (36 18 (:REWRITE DEFAULT-+-2))
 (27 9 (:REWRITE SET-UNION-SUBSET-REDUCTION))
 (18 18 (:TYPE-PRESCRIPTION UNIQUEP))
 (18 18 (:REWRITE DEFAULT-+-1))
 (10 10 (:TYPE-PRESCRIPTION FIND-ALL-VARIABLES))
 (9 9 (:REWRITE SUBSET-IS-REFLEXIVE))
 (9 9 (:REWRITE PROPER-SUBSET-IS-IRREFLEXIVE))
 (9 9 (:REWRITE FIND-VARIABLES-1-PASS-IS-SUBSET))
 )
(SET-INTERSECT-IS-SUBSET
 (913 97 (:REWRITE SUBSET-IS-TRANSITIVE))
 (388 97 (:REWRITE PROPER-SUBSET-IS-STRONGER-THAN-SUBSET))
 (268 268 (:REWRITE TRUTHP-LABEL-TO-SUBSET))
 (268 268 (:REWRITE TRANSITION-SUBSET-P-EXPANDED))
 (268 268 (:REWRITE ONLY-TRUTHSP-AND-SUBSET-TO-SUBSET))
 (268 268 (:REWRITE ALL-TRUTHSP-LABEL-EXPANDED))
 (264 262 (:REWRITE DEFAULT-CAR))
 (221 220 (:REWRITE DEFAULT-CDR))
 (194 194 (:TYPE-PRESCRIPTION PROPER-SUBSET))
 (97 97 (:REWRITE PROPER-SUBSET-IS-TRANSITIVE))
 )
(MEMBERP-REMOVE-REDUCTION
 (125 125 (:REWRITE DEFAULT-CAR))
 (123 123 (:REWRITE TRUTHP-LABEL-TO-SUBSET))
 (123 123 (:REWRITE TRANSITION-SUBSET-P-EXPANDED))
 (123 123 (:REWRITE ONLY-TRUTHSP-AND-SUBSET-TO-SUBSET))
 (123 123 (:REWRITE ALL-TRUTHSP-LABEL-EXPANDED))
 (116 116 (:REWRITE DEFAULT-CDR))
 )
(REMOVE-DUPLICATES-IS-SUBSET
 (72 18 (:REWRITE PROPER-SUBSET-IS-STRONGER-THAN-SUBSET))
 (72 4 (:DEFINITION REMOVE-DUPLICATE-OCCURRENCES))
 (64 18 (:REWRITE SUBSET-IS-TRANSITIVE))
 (38 38 (:REWRITE DEFAULT-CAR))
 (36 36 (:TYPE-PRESCRIPTION PROPER-SUBSET))
 (33 33 (:REWRITE DEFAULT-CDR))
 (32 32 (:REWRITE TRUTHP-LABEL-TO-SUBSET))
 (32 32 (:REWRITE TRANSITION-SUBSET-P-EXPANDED))
 (32 32 (:REWRITE ONLY-TRUTHSP-AND-SUBSET-TO-SUBSET))
 (32 32 (:REWRITE ALL-TRUTHSP-LABEL-EXPANDED))
 (18 18 (:REWRITE PROPER-SUBSET-IS-TRANSITIVE))
 )
(CONE-VARIABLES-ARE-SUBSET
 (404 1 (:DEFINITION FIND-ALL-VARIABLES))
 (296 22 (:DEFINITION MEMBERP))
 (227 1 (:DEFINITION FIND-ALL-VARIABLES-1-PASS))
 (219 1 (:DEFINITION FIND-VARIABLES*))
 (216 1 (:DEFINITION FIND-VARIABLES))
 (123 4 (:REWRITE ORDERED-IMPLIES-UNIQUE))
 (111 4 (:DEFINITION ORDEREDP))
 (108 6 (:DEFINITION REMOVE-DUPLICATE-OCCURRENCES))
 (107 7 (:REWRITE SUBSET-IS-TRANSITIVE))
 (102 6 (:DEFINITION SET-INTERSECT))
 (89 80 (:REWRITE DEFAULT-CDR))
 (88 2 (:DEFINITION UNIQUEP))
 (78 75 (:REWRITE DEFAULT-CAR))
 (56 2 (:REWRITE MEMBERP-FIND-ALL-VARIABLES-REDUCTION))
 (48 12 (:REWRITE <<-TRICHOTOMY))
 (43 43 (:REWRITE TRUTHP-LABEL-TO-SUBSET))
 (43 43 (:REWRITE TRANSITION-SUBSET-P-EXPANDED))
 (43 43 (:REWRITE ONLY-TRUTHSP-AND-SUBSET-TO-SUBSET))
 (43 43 (:REWRITE ALL-TRUTHSP-LABEL-EXPANDED))
 (42 12 (:REWRITE PROPER-SUBSET-IS-STRONGER-THAN-SUBSET))
 (33 33 (:TYPE-PRESCRIPTION SET-INTERSECT))
 (32 32 (:TYPE-PRESCRIPTION <<))
 (24 4 (:REWRITE <<-ASYMMETRIC))
 (20 20 (:TYPE-PRESCRIPTION ORDEREDP))
 (19 19 (:TYPE-PRESCRIPTION PROPER-SUBSET))
 (12 12 (:REWRITE <<-TRANSITIVE))
 (12 6 (:TYPE-PRESCRIPTION FIND-ALL-VARIABLES))
 (11 3 (:DEFINITION LEN))
 (11 1 (:REWRITE SET-UNION-SUBSET-REDUCTION))
 (10 10 (:REWRITE PROPER-SUBSET-IS-TRANSITIVE))
 (6 6 (:TYPE-PRESCRIPTION LEN))
 (5 5 (:REWRITE VARIABLES-IN-LABEL-ARE-T-IN-Q))
 (5 5 (:REWRITE TRUTHP-LABEL-IS-A-SUBSET))
 (5 5 (:REWRITE STRICT-EVALUATION-P-EXPANDED))
 (5 5 (:REWRITE EVALUATION-EQ-VARS-REDUCTION))
 (5 1 (:REWRITE FIND-VARIABLES-1-PASS-IS-SUBSET))
 (4 2 (:REWRITE DEFAULT-+-2))
 (2 2 (:TYPE-PRESCRIPTION UNIQUEP))
 (2 2 (:REWRITE DEFAULT-+-1))
 (1 1 (:REWRITE PROPER-SUBSET-IS-IRREFLEXIVE))
 )
(CIRCUITP-TO-CONE-VARIABLES
 (427 1 (:DEFINITION FIND-ALL-VARIABLES))
 (260 18 (:DEFINITION MEMBERP))
 (251 1 (:DEFINITION FIND-ALL-VARIABLES-1-PASS))
 (243 1 (:DEFINITION FIND-VARIABLES*))
 (240 1 (:DEFINITION FIND-VARIABLES))
 (177 6 (:REWRITE ORDERED-IMPLIES-UNIQUE))
 (159 6 (:DEFINITION ORDEREDP))
 (131 3 (:DEFINITION UNIQUEP))
 (90 81 (:REWRITE DEFAULT-CDR))
 (90 5 (:DEFINITION REMOVE-DUPLICATE-OCCURRENCES))
 (85 5 (:DEFINITION SET-INTERSECT))
 (77 74 (:REWRITE DEFAULT-CAR))
 (72 18 (:REWRITE <<-TRICHOTOMY))
 (48 48 (:TYPE-PRESCRIPTION <<))
 (36 6 (:REWRITE <<-ASYMMETRIC))
 (35 35 (:REWRITE TRUTHP-LABEL-TO-SUBSET))
 (35 35 (:REWRITE TRANSITION-SUBSET-P-EXPANDED))
 (35 35 (:REWRITE ONLY-TRUTHSP-AND-SUBSET-TO-SUBSET))
 (35 35 (:REWRITE ALL-TRUTHSP-LABEL-EXPANDED))
 (30 30 (:TYPE-PRESCRIPTION ORDEREDP))
 (29 29 (:REWRITE VARIABLES-IN-LABEL-ARE-T-IN-Q))
 (29 29 (:REWRITE STRICT-EVALUATION-P-EXPANDED))
 (29 29 (:REWRITE EVALUATION-EQ-VARS-REDUCTION))
 (21 1 (:DEFINITION STRICT-EVALUATION-LIST-P))
 (20 1 (:DEFINITION SUBSET))
 (19 19 (:TYPE-PRESCRIPTION SET-INTERSECT))
 (18 18 (:REWRITE <<-TRANSITIVE))
 (16 16 (:TYPE-PRESCRIPTION MEMBERP))
 (16 1 (:DEFINITION STRICT-EVALUATION-P))
 (14 5 (:REWRITE PROPER-SUBSET-IS-STRONGER-THAN-SUBSET))
 (14 1 (:DEFINITION ONLY-EVALUATIONS-P))
 (11 3 (:DEFINITION LEN))
 (11 1 (:REWRITE SET-UNION-SUBSET-REDUCTION))
 (8 1 (:DEFINITION EVALUATION-P))
 (6 6 (:TYPE-PRESCRIPTION PROPER-SUBSET))
 (6 6 (:TYPE-PRESCRIPTION LEN))
 (6 1 (:DEFINITION CONS-LIST-P))
 (5 1 (:REWRITE FIND-VARIABLES-1-PASS-IS-SUBSET))
 (4 2 (:REWRITE DEFAULT-+-2))
 (3 3 (:REWRITE TRUTHP-LABEL-IS-A-SUBSET))
 (3 3 (:REWRITE PROPER-SUBSET-IS-TRANSITIVE))
 (3 3 (:REWRITE INTERSECT-IS-A-SUBSET-2))
 (2 2 (:REWRITE SUBSET-IS-TRANSITIVE))
 (2 2 (:REWRITE EVALUATIONP-FOR-SUBSET))
 (2 2 (:REWRITE EVALUATION-P-ONLY-EVALUATIONS-REDUCTION))
 (2 2 (:REWRITE DEFAULT-+-1))
 (1 1 (:TYPE-PRESCRIPTION EVALUATION-P))
 (1 1 (:REWRITE STRICT-EVALUATION-P-NECC))
 )
(CONE-OF-INFLUENCE-REDUCTION-FOR-SPECIFIC
 (331 2 (:REWRITE CIRCUIT-BISIM-IMPLIES-SAME-LTL-SEMANTICS))
 (323 1 (:DEFINITION CIRCUIT-MODELP))
 (279 1 (:REWRITE CONE-OF-INFLUENCE-REDUCTION-IS-SOUND))
 (98 3 (:DEFINITION SUBSET))
 (88 4 (:DEFINITION CREATE-RESTRICTED-VAR-SET))
 (80 80 (:REWRITE TRUTHP-LABEL-TO-SUBSET))
 (80 80 (:REWRITE TRANSITION-SUBSET-P-EXPANDED))
 (80 80 (:REWRITE ONLY-TRUTHSP-AND-SUBSET-TO-SUBSET))
 (80 80 (:REWRITE ALL-TRUTHSP-LABEL-EXPANDED))
 (76 76 (:REWRITE DEFAULT-CAR))
 (75 15 (:DEFINITION LEN))
 (71 71 (:REWRITE DEFAULT-CDR))
 (60 60 (:TYPE-PRESCRIPTION MEMBERP))
 (52 1 (:DEFINITION TRANSITION-SUBSET-P))
 (42 1 (:DEFINITION ONLY-ALL-TRUTHS-P))
 (42 1 (:DEFINITION LABEL-SUBSET-VARS))
 (31 1 (:DEFINITION ALL-TRUTHSP-LABEL))
 (30 15 (:REWRITE DEFAULT-+-2))
 (28 1 (:DEFINITION STRICT-EVALUATION-LIST-P))
 (25 25 (:REWRITE VARIABLES-IN-LABEL-ARE-T-IN-Q))
 (25 25 (:REWRITE STRICT-EVALUATION-P-EXPANDED))
 (25 25 (:REWRITE EVALUATION-EQ-VARS-REDUCTION))
 (24 6 (:REWRITE PROPER-SUBSET-IS-STRONGER-THAN-SUBSET))
 (23 1 (:DEFINITION ONLY-EVALUATIONS-P))
 (20 1 (:DEFINITION STRICT-EVALUATION-P))
 (20 1 (:DEFINITION ONLY-TRUTH-P))
 (17 4 (:LINEAR CONSP-TO-LEN-EXPANDED))
 (15 15 (:REWRITE DEFAULT-+-1))
 (15 2 (:REWRITE LTL-SEMANTICS-IS-DECOMPOSED-OVER-CONJUNCTION))
 (14 2 (:REWRITE NEXT-STATES-IN-STATES-CLARIFIED))
 (12 12 (:TYPE-PRESCRIPTION PROPER-SUBSET))
 (12 12 (:REWRITE MODELP-CHARACTERIZATION))
 (12 1 (:DEFINITION EVALUATION-P))
 (9 1 (:DEFINITION TRUTHP-LABEL))
 (7 7 (:TYPE-PRESCRIPTION ALL-TRUTHSP-LABEL))
 (6 6 (:REWRITE SUBSET-IS-TRANSITIVE))
 (6 6 (:REWRITE PROPER-SUBSET-IS-TRANSITIVE))
 (5 5 (:TYPE-PRESCRIPTION TRUTHP-LABEL))
 (5 5 (:TYPE-PRESCRIPTION TRANSITION-SUBSET-P))
 (5 5 (:TYPE-PRESCRIPTION STRICT-EVALUATION-LIST-P))
 (5 5 (:TYPE-PRESCRIPTION ONLY-TRUTH-P))
 (5 5 (:TYPE-PRESCRIPTION ONLY-EVALUATIONS-P))
 (5 5 (:TYPE-PRESCRIPTION ONLY-ALL-TRUTHS-P))
 (5 5 (:TYPE-PRESCRIPTION NEXT-STATES-IN-STATES))
 (5 5 (:TYPE-PRESCRIPTION LABEL-SUBSET-VARS))
 (5 5 (:TYPE-PRESCRIPTION EVALUATION-P))
 (4 4 (:TYPE-PRESCRIPTION CONE-VARIABLES))
 (4 2 (:REWRITE CREATE-KRIPKE-PRODUCES-CIRCUIT-MODEL))
 (3 3 (:REWRITE ALL-TRUTHS-P-FROM-ONLY-ALL-TRUTHS-P))
 (2 2 (:TYPE-PRESCRIPTION CREATE-RESTRICTED-VAR-SET))
 (2 2 (:TYPE-PRESCRIPTION CIRCUIT-MODELP))
 (2 2 (:TYPE-PRESCRIPTION ALL-EVALUATIONS-P))
 (2 2 (:REWRITE EVALUATIONP-FOR-SUBSET))
 (2 2 (:REWRITE EVALUATION-P-ONLY-EVALUATIONS-REDUCTION))
 (2 2 (:REWRITE COMPATIBLE-PATHS-HAVE-ONLY-STATES))
 (1 1 (:TYPE-PRESCRIPTION BOOLEANP))
 (1 1 (:REWRITE TRUTHP-LABEL-FROM-ONLY-TRUTHP))
 (1 1 (:REWRITE LABEL-SUBSET-SUBSET-REDUCTION))
 )
(REDUCE-PROBLEM-CONE-REDUCTION
 (22 1 (:DEFINITION SUBSET))
 (8 2 (:REWRITE PROPER-SUBSET-IS-STRONGER-THAN-SUBSET))
 (7 1 (:DEFINITION MEMBERP))
 (4 4 (:TYPE-PRESCRIPTION PROPER-SUBSET))
 (2 2 (:TYPE-PRESCRIPTION CREATE-RESTRICTED-VAR-SET))
 (2 2 (:REWRITE TRUTHP-LABEL-TO-SUBSET))
 (2 2 (:REWRITE TRANSITION-SUBSET-P-EXPANDED))
 (2 2 (:REWRITE SUBSET-IS-TRANSITIVE))
 (2 2 (:REWRITE PROPER-SUBSET-IS-TRANSITIVE))
 (2 2 (:REWRITE ONLY-TRUTHSP-AND-SUBSET-TO-SUBSET))
 (2 2 (:REWRITE DEFAULT-CDR))
 (2 2 (:REWRITE DEFAULT-CAR))
 (2 2 (:REWRITE ALL-TRUTHSP-LABEL-EXPANDED))
 (1 1 (:TYPE-PRESCRIPTION MEMBERP))
 (1 1 (:REWRITE VARIABLES-IN-LABEL-ARE-T-IN-Q))
 (1 1 (:REWRITE STRICT-EVALUATION-P-EXPANDED))
 (1 1 (:REWRITE EVALUATION-EQ-VARS-REDUCTION))
 )
(WELL-FORMED-PROBLEMS-P)
(REDUCE-PROBLEM-CONE*-REDUCTION
 (142 138 (:REWRITE DEFAULT-CAR))
 (132 6 (:DEFINITION SUBSET))
 (52 51 (:REWRITE DEFAULT-CDR))
 (48 12 (:REWRITE PROPER-SUBSET-IS-STRONGER-THAN-SUBSET))
 (42 6 (:DEFINITION MEMBERP))
 (24 24 (:TYPE-PRESCRIPTION PROPER-SUBSET))
 (12 12 (:TYPE-PRESCRIPTION CREATE-RESTRICTED-VAR-SET))
 (12 12 (:REWRITE TRUTHP-LABEL-TO-SUBSET))
 (12 12 (:REWRITE TRANSITION-SUBSET-P-EXPANDED))
 (12 12 (:REWRITE SUBSET-IS-TRANSITIVE))
 (12 12 (:REWRITE PROPER-SUBSET-IS-TRANSITIVE))
 (12 12 (:REWRITE ONLY-TRUTHSP-AND-SUBSET-TO-SUBSET))
 (12 12 (:REWRITE ALL-TRUTHSP-LABEL-EXPANDED))
 (6 6 (:TYPE-PRESCRIPTION MEMBERP))
 (6 6 (:REWRITE VARIABLES-IN-LABEL-ARE-T-IN-Q))
 (6 6 (:REWRITE STRICT-EVALUATION-P-EXPANDED))
 (6 6 (:REWRITE EVALUATION-EQ-VARS-REDUCTION))
 )
(SUBSET-MEMBER-REDUCTION
 (148 37 (:REWRITE PROPER-SUBSET-IS-STRONGER-THAN-SUBSET))
 (130 127 (:REWRITE DEFAULT-CAR))
 (120 120 (:REWRITE TRUTHP-LABEL-TO-SUBSET))
 (120 120 (:REWRITE TRANSITION-SUBSET-P-EXPANDED))
 (120 120 (:REWRITE ONLY-TRUTHSP-AND-SUBSET-TO-SUBSET))
 (120 120 (:REWRITE ALL-TRUTHSP-LABEL-EXPANDED))
 (100 98 (:REWRITE DEFAULT-CDR))
 (74 74 (:TYPE-PRESCRIPTION PROPER-SUBSET))
 (42 42 (:TYPE-PRESCRIPTION SET-UNION))
 (37 37 (:REWRITE SUBSET-IS-TRANSITIVE))
 (37 37 (:REWRITE PROPER-SUBSET-IS-TRANSITIVE))
 )
(SUBSET-MEMBER-REDUCTION-2
 (112 46 (:REWRITE SUBSET-MEMBER-REDUCTION))
 (56 14 (:REWRITE PROPER-SUBSET-IS-STRONGER-THAN-SUBSET))
 (46 46 (:REWRITE TRUTHP-LABEL-TO-SUBSET))
 (46 46 (:REWRITE TRANSITION-SUBSET-P-EXPANDED))
 (46 46 (:REWRITE ONLY-TRUTHSP-AND-SUBSET-TO-SUBSET))
 (46 46 (:REWRITE ALL-TRUTHSP-LABEL-EXPANDED))
 (40 39 (:REWRITE DEFAULT-CAR))
 (35 34 (:REWRITE DEFAULT-CDR))
 (28 28 (:TYPE-PRESCRIPTION PROPER-SUBSET))
 (15 15 (:TYPE-PRESCRIPTION SET-UNION))
 (14 14 (:REWRITE SUBSET-IS-TRANSITIVE))
 (14 14 (:REWRITE PROPER-SUBSET-IS-TRANSITIVE))
 )
(SET-UNION-SUBSET-REDUCTION
 (120 30 (:REWRITE PROPER-SUBSET-IS-STRONGER-THAN-SUBSET))
 (86 83 (:REWRITE DEFAULT-CAR))
 (73 73 (:REWRITE TRUTHP-LABEL-TO-SUBSET))
 (73 73 (:REWRITE TRANSITION-SUBSET-P-EXPANDED))
 (73 73 (:REWRITE ONLY-TRUTHSP-AND-SUBSET-TO-SUBSET))
 (73 73 (:REWRITE ALL-TRUTHSP-LABEL-EXPANDED))
 (67 66 (:REWRITE DEFAULT-CDR))
 (60 60 (:TYPE-PRESCRIPTION PROPER-SUBSET))
 (30 30 (:REWRITE SUBSET-IS-TRANSITIVE))
 (30 30 (:REWRITE PROPER-SUBSET-IS-TRANSITIVE))
 (27 27 (:TYPE-PRESCRIPTION SET-UNION))
 )
(SET-UNION-SUBSET-REDUCTION-2
 (92 38 (:REWRITE SUBSET-MEMBER-REDUCTION-2))
 (74 36 (:REWRITE SUBSET-MEMBER-REDUCTION))
 (72 18 (:REWRITE PROPER-SUBSET-IS-STRONGER-THAN-SUBSET))
 (38 37 (:REWRITE DEFAULT-CAR))
 (36 36 (:TYPE-PRESCRIPTION PROPER-SUBSET))
 (36 36 (:REWRITE TRUTHP-LABEL-TO-SUBSET))
 (36 36 (:REWRITE TRANSITION-SUBSET-P-EXPANDED))
 (36 36 (:REWRITE ONLY-TRUTHSP-AND-SUBSET-TO-SUBSET))
 (36 36 (:REWRITE ALL-TRUTHSP-LABEL-EXPANDED))
 (31 30 (:REWRITE DEFAULT-CDR))
 (18 18 (:REWRITE SUBSET-IS-TRANSITIVE))
 (18 18 (:REWRITE SET-UNION-SUBSET-REDUCTION))
 (18 18 (:REWRITE PROPER-SUBSET-IS-TRANSITIVE))
 (17 17 (:TYPE-PRESCRIPTION SET-UNION))
 )
(CONJUNCTION-HAS-VARIABLES-SUBSET-1
 (47 47 (:REWRITE TRUTHP-LABEL-TO-SUBSET))
 (47 47 (:REWRITE TRANSITION-SUBSET-P-EXPANDED))
 (47 47 (:REWRITE SUBSET-MEMBER-REDUCTION-2))
 (47 47 (:REWRITE SUBSET-MEMBER-REDUCTION))
 (47 47 (:REWRITE ONLY-TRUTHSP-AND-SUBSET-TO-SUBSET))
 (47 47 (:REWRITE ALL-TRUTHSP-LABEL-EXPANDED))
 (39 39 (:REWRITE DEFAULT-CDR))
 (20 10 (:REWRITE DEFAULT-+-2))
 (20 5 (:REWRITE PROPER-SUBSET-IS-STRONGER-THAN-SUBSET))
 (10 10 (:TYPE-PRESCRIPTION PROPER-SUBSET))
 (10 10 (:REWRITE DEFAULT-+-1))
 (6 6 (:REWRITE SET-UNION-SUBSET-REDUCTION-2))
 (5 5 (:REWRITE SUBSET-IS-TRANSITIVE))
 (5 5 (:REWRITE PROPER-SUBSET-IS-TRANSITIVE))
 (4 2 (:TYPE-PRESCRIPTION SET-UNION))
 (2 2 (:TYPE-PRESCRIPTION CREATE-RESTRICTED-VAR-SET))
 (2 2 (:LINEAR CONSP-TO-LEN-EXPANDED))
 )
(CONJUNCTION-HAS-VARIABLES-SUBSET-2
 (1456 4 (:DEFINITION LTL-FORMULAP))
 (1185 75 (:DEFINITION MEMBERP))
 (1158 3 (:REWRITE CONJUNCTION-HAS-VARIABLES-SUBSET-1))
 (522 4 (:DEFINITION LTL-VARIABLEP))
 (333 333 (:REWRITE DEFAULT-CDR))
 (138 138 (:REWRITE TRUTHP-LABEL-TO-SUBSET))
 (138 138 (:REWRITE TRANSITION-SUBSET-P-EXPANDED))
 (138 138 (:REWRITE SUBSET-MEMBER-REDUCTION-2))
 (138 138 (:REWRITE SUBSET-MEMBER-REDUCTION))
 (138 138 (:REWRITE ONLY-TRUTHSP-AND-SUBSET-TO-SUBSET))
 (138 138 (:REWRITE ALL-TRUTHSP-LABEL-EXPANDED))
 (126 63 (:REWRITE DEFAULT-+-2))
 (117 117 (:REWRITE DEFAULT-CAR))
 (93 93 (:TYPE-PRESCRIPTION MEMBERP))
 (92 3 (:DEFINITION SUBSET))
 (63 63 (:REWRITE DEFAULT-+-1))
 (46 7 (:LINEAR CONSP-TO-LEN-EXPANDED))
 (24 6 (:REWRITE PROPER-SUBSET-IS-STRONGER-THAN-SUBSET))
 (12 12 (:TYPE-PRESCRIPTION PROPER-SUBSET))
 (10 10 (:DEFINITION LTL-CONSTANTP))
 (8 8 (:TYPE-PRESCRIPTION CREATE-RESTRICTED-VAR-SET))
 (6 6 (:REWRITE SUBSET-IS-TRANSITIVE))
 (6 6 (:REWRITE SET-UNION-SUBSET-REDUCTION))
 (6 6 (:REWRITE PROPER-SUBSET-IS-TRANSITIVE))
 (4 2 (:TYPE-PRESCRIPTION SET-UNION))
 )
(WELL-FORMED-APPEND-REDUCTION
 (336 12 (:DEFINITION SUBSET))
 (143 131 (:REWRITE DEFAULT-CAR))
 (108 12 (:DEFINITION MEMBERP))
 (104 26 (:REWRITE PROPER-SUBSET-IS-STRONGER-THAN-SUBSET))
 (66 63 (:REWRITE DEFAULT-CDR))
 (51 51 (:TYPE-PRESCRIPTION PROPER-SUBSET))
 (39 13 (:REWRITE CONJUNCTION-HAS-VARIABLES-SUBSET-1))
 (26 26 (:REWRITE SET-UNION-SUBSET-REDUCTION-2))
 (26 26 (:REWRITE SET-UNION-SUBSET-REDUCTION))
 (26 26 (:REWRITE PROPER-SUBSET-IS-TRANSITIVE))
 (24 24 (:TYPE-PRESCRIPTION CREATE-RESTRICTED-VAR-SET))
 (24 24 (:REWRITE TRUTHP-LABEL-TO-SUBSET))
 (24 24 (:REWRITE TRANSITION-SUBSET-P-EXPANDED))
 (24 24 (:REWRITE SUBSET-MEMBER-REDUCTION-2))
 (24 24 (:REWRITE SUBSET-MEMBER-REDUCTION))
 (24 24 (:REWRITE ONLY-TRUTHSP-AND-SUBSET-TO-SUBSET))
 (24 24 (:REWRITE ALL-TRUTHSP-LABEL-EXPANDED))
 (24 12 (:TYPE-PRESCRIPTION TRUE-LISTP-APPEND))
 (13 13 (:REWRITE VARIABLES-IN-LABEL-ARE-T-IN-Q))
 (13 13 (:REWRITE STRICT-EVALUATION-P-EXPANDED))
 (13 13 (:REWRITE EVALUATION-EQ-VARS-REDUCTION))
 (12 12 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (12 12 (:TYPE-PRESCRIPTION MEMBERP))
 (12 12 (:TYPE-PRESCRIPTION BINARY-APPEND))
 (1 1 (:REWRITE PROPER-SUBSET-IS-IRREFLEXIVE))
 )
(CONJUNCTION-PRODUCES-WELL-FORMED-PROBLEMS
 (2819 203 (:DEFINITION MEMBERP))
 (1982 887 (:REWRITE DEFAULT-CAR))
 (1464 51 (:DEFINITION SUBSET))
 (1393 901 (:REWRITE DEFAULT-CDR))
 (1016 8 (:DEFINITION LTL-VARIABLEP))
 (720 240 (:TYPE-PRESCRIPTION TRUE-LISTP-APPEND))
 (444 222 (:REWRITE DEFAULT-+-2))
 (432 108 (:REWRITE PROPER-SUBSET-IS-STRONGER-THAN-SUBSET))
 (382 382 (:REWRITE TRUTHP-LABEL-TO-SUBSET))
 (382 382 (:REWRITE TRANSITION-SUBSET-P-EXPANDED))
 (382 382 (:REWRITE SUBSET-MEMBER-REDUCTION-2))
 (382 382 (:REWRITE SUBSET-MEMBER-REDUCTION))
 (382 382 (:REWRITE ONLY-TRUTHSP-AND-SUBSET-TO-SUBSET))
 (382 382 (:REWRITE ALL-TRUTHSP-LABEL-EXPANDED))
 (240 240 (:TYPE-PRESCRIPTION BINARY-APPEND))
 (222 222 (:REWRITE DEFAULT-+-1))
 (213 213 (:TYPE-PRESCRIPTION PROPER-SUBSET))
 (138 23 (:DEFINITION BINARY-APPEND))
 (126 126 (:TYPE-PRESCRIPTION CREATE-RESTRICTED-VAR-SET))
 (108 108 (:REWRITE SET-UNION-SUBSET-REDUCTION-2))
 (108 108 (:REWRITE SET-UNION-SUBSET-REDUCTION))
 (108 108 (:REWRITE PROPER-SUBSET-IS-TRANSITIVE))
 (67 67 (:TYPE-PRESCRIPTION MEMBERP))
 (59 59 (:REWRITE VARIABLES-IN-LABEL-ARE-T-IN-Q))
 (59 59 (:REWRITE STRICT-EVALUATION-P-EXPANDED))
 (59 59 (:REWRITE EVALUATION-EQ-VARS-REDUCTION))
 (23 23 (:LINEAR CONSP-TO-LEN-EXPANDED))
 (8 8 (:DEFINITION LTL-CONSTANTP))
 (3 3 (:REWRITE PROPER-SUBSET-IS-IRREFLEXIVE))
 )
(COMPOSITIONAL-REDUCTION-IS-SOUND
 (28 1 (:DEFINITION SUBSET))
 (23 1 (:DEFINITION REDUCE-PROBLEM-CONE*))
 (22 12 (:REWRITE DEFAULT-CAR))
 (20 1 (:DEFINITION REDUCE-PROBLEM-CONJUNCTION))
 (17 17 (:TYPE-PRESCRIPTION REDUCE-PROBLEM-CONJUNCTION))
 (14 9 (:REWRITE DEFAULT-CDR))
 (9 1 (:DEFINITION MEMBERP))
 (8 2 (:REWRITE PROPER-SUBSET-IS-STRONGER-THAN-SUBSET))
 (6 1 (:DEFINITION BINARY-APPEND))
 (5 1 (:DEFINITION LEN))
 (4 4 (:TYPE-PRESCRIPTION PROPER-SUBSET))
 (3 3 (:TYPE-PRESCRIPTION LEN))
 (2 2 (:TYPE-PRESCRIPTION CREATE-RESTRICTED-VAR-SET))
 (2 2 (:REWRITE TRUTHP-LABEL-TO-SUBSET))
 (2 2 (:REWRITE TRANSITION-SUBSET-P-EXPANDED))
 (2 2 (:REWRITE SUBSET-MEMBER-REDUCTION-2))
 (2 2 (:REWRITE SUBSET-MEMBER-REDUCTION))
 (2 2 (:REWRITE SUBSET-IS-TRANSITIVE))
 (2 2 (:REWRITE SET-UNION-SUBSET-REDUCTION-2))
 (2 2 (:REWRITE SET-UNION-SUBSET-REDUCTION))
 (2 2 (:REWRITE PROPER-SUBSET-IS-TRANSITIVE))
 (2 2 (:REWRITE ONLY-TRUTHSP-AND-SUBSET-TO-SUBSET))
 (2 2 (:REWRITE ALL-TRUTHSP-LABEL-EXPANDED))
 (2 1 (:REWRITE DEFAULT-+-2))
 (1 1 (:TYPE-PRESCRIPTION MEMBERP))
 (1 1 (:REWRITE VARIABLES-IN-LABEL-ARE-T-IN-Q))
 (1 1 (:REWRITE STRICT-EVALUATION-P-EXPANDED))
 (1 1 (:REWRITE EVALUATION-EQ-VARS-REDUCTION))
 (1 1 (:REWRITE DEFAULT-+-1))
 )
