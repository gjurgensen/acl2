(LOGIOR-ASH-LOGHEAD-LOGTAIL
 (4693 138 (:DEFINITION UNSIGNED-BYTE-P**))
 (3620 1744 (:TYPE-PRESCRIPTION BITOPS::LOGCDR-NATP))
 (2851 26 (:REWRITE LOGHEAD-IDENTITY))
 (2359 276 (:REWRITE UNSIGNED-BYTE-P-PLUS))
 (2350 24 (:REWRITE LOGTAIL-IDENTITY))
 (1658 170 (:REWRITE BITOPS::LOGCDR-OF-BIT))
 (776 23 (:REWRITE ASH-0))
 (572 22 (:REWRITE BITOPS::ASH-<-0))
 (547 146 (:REWRITE IFIX-WHEN-NOT-INTEGERP))
 (510 14 (:LINEAR BITOPS::LOGIOR-<-0-LINEAR-2))
 (423 332 (:REWRITE DEFAULT-<-1))
 (420 420 (:TYPE-PRESCRIPTION BITP))
 (370 370 (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR))
 (332 332 (:REWRITE DEFAULT-<-2))
 (300 48 (:REWRITE BITOPS::LOGCAR-OF-BIT))
 (246 82 (:REWRITE ZP-WHEN-GT-0))
 (239 239 (:REWRITE DEFAULT-+-2))
 (239 239 (:REWRITE DEFAULT-+-1))
 (233 14 (:LINEAR BITOPS::LOGIOR-<-0-LINEAR-1))
 (134 134 (:LINEAR BITOPS::LOGCDR-<=-LOGCDR))
 (130 130 (:TYPE-PRESCRIPTION POSP))
 (130 25 (:REWRITE NATP-WHEN-INTEGERP))
 (75 25 (:REWRITE NATP-WHEN-GTE-0))
 (66 66 (:TYPE-PRESCRIPTION BIT->BOOL$INLINE))
 (55 5 (:REWRITE BITOPS::LOGCAR-OF-LOGHEAD))
 (32 32 (:REWRITE-QUOTED-CONSTANT IFIX-UNDER-INT-EQUIV))
 (30 5 (:REWRITE BITOPS::LOGCDR-OF-LEFT-SHIFT))
 (30 5 (:REWRITE BITOPS::LOGCAR-OF-LEFT-SHIFT))
 (23 3 (:REWRITE BFIX-WHEN-NOT-1))
 (20 20 (:REWRITE-QUOTED-CONSTANT NFIX-UNDER-NAT-EQUIV))
 (20 20 (:REWRITE-QUOTED-CONSTANT BFIX-UNDER-BIT-EQUIV))
 (6 3 (:REWRITE BFIX-WHEN-NOT-BITP))
 (6 3 (:REWRITE BFIX-WHEN-NOT-BIT->BOOL))
 (6 3 (:REWRITE BFIX-WHEN-BIT->BOOL))
 (5 5 (:TYPE-PRESCRIPTION ZP))
 (1 1 (:INDUCTION BITOPS::LOGIOR-INDUCT))
 )
(LOGIOR-OF-ASH
 (312 120 (:TYPE-PRESCRIPTION BITOPS::LOGCONS-POSP-2))
 (312 120 (:TYPE-PRESCRIPTION BITOPS::LOGCONS-POSP-1))
 (312 120 (:TYPE-PRESCRIPTION BITOPS::LOGCONS-NATP))
 (264 12 (:REWRITE ASH-0))
 (215 126 (:REWRITE IFIX-WHEN-NOT-INTEGERP))
 (201 17 (:LINEAR BITOPS::LOGIOR->=-0-LINEAR))
 (201 17 (:LINEAR BITOPS::LOGIOR-<-0-LINEAR-2))
 (201 17 (:LINEAR BITOPS::LOGIOR-<-0-LINEAR-1))
 (135 27 (:REWRITE BITOPS::ASH-<-0))
 (120 120 (:TYPE-PRESCRIPTION POSP))
 (81 81 (:REWRITE DEFAULT-<-2))
 (81 81 (:REWRITE DEFAULT-<-1))
 (78 18 (:REWRITE BITOPS::LOGCAR-OF-BIT))
 (56 56 (:TYPE-PRESCRIPTION BITP))
 (54 10 (:REWRITE BITOPS::LOGCDR-OF-BIT))
 (21 6 (:REWRITE BITOPS::LOGCDR-OF-LEFT-SHIFT))
 (21 6 (:REWRITE BITOPS::LOGCAR-OF-LEFT-SHIFT))
 (20 4 (:REWRITE BITOPS::LOGIOR-EQUAL-0))
 (18 18 (:REWRITE-QUOTED-CONSTANT IFIX-UNDER-INT-EQUIV))
 (13 13 (:REWRITE-QUOTED-CONSTANT NFIX-UNDER-NAT-EQUIV))
 (13 13 (:REWRITE-QUOTED-CONSTANT BFIX-UNDER-BIT-EQUIV))
 (12 6 (:TYPE-PRESCRIPTION BITOPS::LOGCDR-NATP))
 (9 3 (:REWRITE NATP-WHEN-GTE-0))
 (6 6 (:REWRITE DEFAULT-+-2))
 (6 6 (:REWRITE DEFAULT-+-1))
 (3 3 (:REWRITE NATP-WHEN-INTEGERP))
 )
(COMBINE16U$INLINE
 (93 6 (:LINEAR BITOPS::LOGIOR-<-0-LINEAR-2))
 (93 6 (:LINEAR BITOPS::LOGIOR-<-0-LINEAR-1))
 (62 30 (:REWRITE IFIX-WHEN-NOT-INTEGERP))
 (58 6 (:REWRITE BITOPS::ASH-<-0))
 (20 12 (:REWRITE DEFAULT-<-1))
 (12 12 (:REWRITE DEFAULT-<-2))
 (9 3 (:REWRITE ASH-0))
 (8 8 (:REWRITE INEQUALITY-WITH-NFIX-HYP-2))
 (5 3 (:REWRITE RIGHT-SHIFT-TO-LOGTAIL))
 (4 4 (:TYPE-PRESCRIPTION ZIP))
 (3 3 (:REWRITE-QUOTED-CONSTANT IFIX-UNDER-INT-EQUIV))
 (2 2 (:REWRITE ZIP-OPEN))
 (2 2 (:REWRITE NFIX-WHEN-NOT-NATP))
 )
(COMBINE16U-UNSIGNED-BYTE
 (4 1 (:REWRITE ASH-0))
 (2 2 (:TYPE-PRESCRIPTION ZIP))
 (2 2 (:REWRITE NFIX-WHEN-NOT-NATP))
 (2 1 (:REWRITE RIGHT-SHIFT-TO-LOGTAIL))
 (1 1 (:REWRITE-QUOTED-CONSTANT IFIX-UNDER-INT-EQUIV))
 (1 1 (:REWRITE ZIP-OPEN))
 )
(COMBINE16U-LOGHEAD-LOGTAIL
 (74 4 (:LINEAR BITOPS::LOGIOR-<-0-LINEAR-2))
 (74 4 (:LINEAR BITOPS::LOGIOR-<-0-LINEAR-1))
 (48 20 (:REWRITE IFIX-WHEN-NOT-INTEGERP))
 (48 4 (:REWRITE BITOPS::ASH-<-0))
 (17 9 (:REWRITE DEFAULT-<-1))
 (11 1 (:REWRITE ASH-0))
 (9 9 (:REWRITE DEFAULT-<-2))
 (8 8 (:REWRITE INEQUALITY-WITH-NFIX-HYP-2))
 (7 1 (:REWRITE ZIP-OPEN))
 (4 2 (:REWRITE NFIX-WHEN-NOT-NATP))
 (4 1 (:REWRITE LOGTAIL-IDENTITY))
 (4 1 (:REWRITE LOGHEAD-IDENTITY))
 (3 3 (:REWRITE-QUOTED-CONSTANT IFIX-UNDER-INT-EQUIV))
 (3 1 (:REWRITE NATP-WHEN-GTE-0))
 (2 2 (:REWRITE-QUOTED-CONSTANT NFIX-UNDER-NAT-EQUIV))
 (2 2 (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR))
 (2 1 (:REWRITE RIGHT-SHIFT-TO-LOGTAIL))
 (1 1 (:TYPE-PRESCRIPTION ZIP))
 (1 1 (:REWRITE NATP-WHEN-INTEGERP))
 )
(COMBINE16S$INLINE
 (54 2 (:LINEAR BITOPS::LOGIOR->=-0-LINEAR))
 (54 2 (:LINEAR BITOPS::LOGIOR-<-0-LINEAR-1))
 (44 4 (:REWRITE BITOPS::ASH-<-0))
 (34 4 (:REWRITE ASH-0))
 (33 5 (:REWRITE LOGEXT-IDENTITY))
 (28 10 (:REWRITE IFIX-WHEN-NOT-INTEGERP))
 (28 10 (:REWRITE IFIX-WHEN-INTEGERP))
 (26 2 (:LINEAR BITOPS::LOGIOR-<-0-LINEAR-2))
 (12 6 (:REWRITE DEFAULT-<-1))
 (10 10 (:REWRITE BITOPS::SIGNED-BYTE-P-WHEN-SIGNED-BYTE-P-SMALLER))
 (10 10 (:REWRITE BITOPS::SIGNED-BYTE-P-MONOTONICITY))
 (9 9 (:REWRITE-QUOTED-CONSTANT IFIX-UNDER-INT-EQUIV))
 (8 8 (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR))
 (7 4 (:REWRITE RIGHT-SHIFT-TO-LOGTAIL))
 (6 6 (:REWRITE DEFAULT-<-2))
 (5 5 (:REWRITE-QUOTED-CONSTANT NFIX-UNDER-NAT-EQUIV))
 (5 5 (:REWRITE BITOPS::SIGNED-BYTE-P-INCR))
 (3 3 (:TYPE-PRESCRIPTION ZIP))
 (2 2 (:REWRITE NFIX-WHEN-NOT-NATP))
 (2 2 (:REWRITE INEQUALITY-WITH-NFIX-HYP-2))
 )
(COMBINE16S-SIGNED-BYTE
 (11 1 (:REWRITE ASH-0))
 (8 1 (:REWRITE LOGEXT-IDENTITY))
 (4 4 (:REWRITE BITOPS::SIGNED-BYTE-P-WHEN-SIGNED-BYTE-P-SMALLER))
 (4 4 (:REWRITE BITOPS::SIGNED-BYTE-P-MONOTONICITY))
 (2 2 (:REWRITE-QUOTED-CONSTANT IFIX-UNDER-INT-EQUIV))
 (2 2 (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR))
 (2 2 (:REWRITE BITOPS::SIGNED-BYTE-P-INCR))
 (2 2 (:REWRITE NFIX-WHEN-NOT-NATP))
 (2 1 (:REWRITE RIGHT-SHIFT-TO-LOGTAIL))
 (1 1 (:TYPE-PRESCRIPTION ZIP))
 (1 1 (:REWRITE-QUOTED-CONSTANT NFIX-UNDER-NAT-EQUIV))
 )
(COMBINE32U$INLINE
 (1757 27 (:LINEAR BITOPS::LOGIOR-<-0-LINEAR-2))
 (462 27 (:LINEAR BITOPS::LOGIOR-<-0-LINEAR-1))
 (409 135 (:REWRITE IFIX-WHEN-NOT-INTEGERP))
 (261 27 (:REWRITE BITOPS::ASH-<-0))
 (155 54 (:REWRITE DEFAULT-<-1))
 (62 62 (:REWRITE BITOPS::LOGIOR-FOLD-CONSTS))
 (54 54 (:REWRITE DEFAULT-<-2))
 (33 12 (:REWRITE ASH-0))
 (26 26 (:REWRITE INEQUALITY-WITH-NFIX-HYP-2))
 (19 12 (:REWRITE RIGHT-SHIFT-TO-LOGTAIL))
 (14 14 (:TYPE-PRESCRIPTION ZIP))
 (12 12 (:REWRITE-QUOTED-CONSTANT IFIX-UNDER-INT-EQUIV))
 (7 7 (:REWRITE ZIP-OPEN))
 (4 4 (:REWRITE NFIX-WHEN-NOT-NATP))
 )
(COMBINE32U-UNSIGNED-BYTE
 (12 3 (:REWRITE ASH-0))
 (6 6 (:TYPE-PRESCRIPTION ZIP))
 (6 6 (:REWRITE BITOPS::LOGIOR-FOLD-CONSTS))
 (6 3 (:REWRITE RIGHT-SHIFT-TO-LOGTAIL))
 (4 4 (:REWRITE NFIX-WHEN-NOT-NATP))
 (3 3 (:REWRITE-QUOTED-CONSTANT IFIX-UNDER-INT-EQUIV))
 (3 3 (:REWRITE ZIP-OPEN))
 )
(COMBINE32U-LOGHEAD-LOGTAIL
 (1069 19 (:LINEAR BITOPS::LOGIOR-<-0-LINEAR-2))
 (336 19 (:LINEAR BITOPS::LOGIOR-<-0-LINEAR-1))
 (310 107 (:REWRITE IFIX-WHEN-NOT-INTEGERP))
 (310 21 (:REWRITE ASH-0))
 (232 20 (:REWRITE BITOPS::ASH-<-0))
 (228 17 (:REWRITE ZIP-OPEN))
 (105 41 (:REWRITE DEFAULT-<-1))
 (101 23 (:REWRITE LOGHEAD-IDENTITY))
 (77 26 (:REWRITE LOGTAIL-IDENTITY))
 (69 69 (:REWRITE-QUOTED-CONSTANT IFIX-UNDER-INT-EQUIV))
 (48 48 (:REWRITE-QUOTED-CONSTANT NFIX-UNDER-NAT-EQUIV))
 (45 9 (:REWRITE UNSIGNED-BYTE-P-OF-LOGTAIL))
 (41 41 (:REWRITE DEFAULT-<-2))
 (38 21 (:REWRITE RIGHT-SHIFT-TO-LOGTAIL))
 (34 34 (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR))
 (27 1 (:REWRITE BITOPS::LOGIOR-EQUAL-0))
 (18 18 (:REWRITE INEQUALITY-WITH-NFIX-HYP-2))
 (17 17 (:TYPE-PRESCRIPTION ZIP))
 (14 7 (:REWRITE NFIX-WHEN-NOT-NATP))
 (11 11 (:REWRITE BITOPS::LOGIOR-FOLD-CONSTS))
 (3 1 (:REWRITE NATP-WHEN-GTE-0))
 (3 1 (:REWRITE BITOPS::LOGHEAD-OF-LOGHEAD-2))
 )
(COMBINE32S$INLINE
 (884 12 (:LINEAR BITOPS::LOGIOR-<-0-LINEAR-2))
 (392 12 (:LINEAR BITOPS::LOGIOR->=-0-LINEAR))
 (250 12 (:LINEAR BITOPS::LOGIOR-<-0-LINEAR-1))
 (188 60 (:REWRITE IFIX-WHEN-NOT-INTEGERP))
 (188 60 (:REWRITE IFIX-WHEN-INTEGERP))
 (164 14 (:REWRITE BITOPS::ASH-<-0))
 (78 26 (:REWRITE DEFAULT-<-1))
 (54 12 (:REWRITE ASH-0))
 (33 5 (:REWRITE LOGEXT-IDENTITY))
 (28 28 (:REWRITE BITOPS::LOGIOR-FOLD-CONSTS))
 (26 26 (:REWRITE DEFAULT-<-2))
 (20 20 (:REWRITE BITOPS::SIGNED-BYTE-P-WHEN-SIGNED-BYTE-P-SMALLER))
 (20 20 (:REWRITE BITOPS::SIGNED-BYTE-P-MONOTONICITY))
 (19 12 (:REWRITE RIGHT-SHIFT-TO-LOGTAIL))
 (17 17 (:REWRITE-QUOTED-CONSTANT IFIX-UNDER-INT-EQUIV))
 (16 16 (:REWRITE INEQUALITY-WITH-NFIX-HYP-2))
 (9 9 (:REWRITE BITOPS::SIGNED-BYTE-P-INCR))
 (5 5 (:REWRITE-QUOTED-CONSTANT NFIX-UNDER-NAT-EQUIV))
 (4 4 (:REWRITE NFIX-WHEN-NOT-NATP))
 )
(COMBINE32S-SIGNED-BYTE
 (19 3 (:REWRITE ASH-0))
 (8 8 (:REWRITE BITOPS::SIGNED-BYTE-P-WHEN-SIGNED-BYTE-P-SMALLER))
 (8 8 (:REWRITE BITOPS::SIGNED-BYTE-P-MONOTONICITY))
 (8 1 (:REWRITE LOGEXT-IDENTITY))
 (6 6 (:REWRITE BITOPS::LOGIOR-FOLD-CONSTS))
 (6 3 (:REWRITE RIGHT-SHIFT-TO-LOGTAIL))
 (4 4 (:REWRITE-QUOTED-CONSTANT IFIX-UNDER-INT-EQUIV))
 (4 4 (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR))
 (4 4 (:REWRITE BITOPS::SIGNED-BYTE-P-INCR))
 (4 4 (:REWRITE NFIX-WHEN-NOT-NATP))
 (1 1 (:REWRITE-QUOTED-CONSTANT NFIX-UNDER-NAT-EQUIV))
 )
(COMBINE64U$INLINE
 (12707 105 (:LINEAR BITOPS::LOGIOR-<-0-LINEAR-2))
 (2443 525 (:REWRITE IFIX-WHEN-NOT-INTEGERP))
 (1932 105 (:LINEAR BITOPS::LOGIOR-<-0-LINEAR-1))
 (1029 210 (:REWRITE DEFAULT-<-1))
 (1015 105 (:REWRITE BITOPS::ASH-<-0))
 (618 618 (:REWRITE BITOPS::LOGIOR-FOLD-CONSTS))
 (210 210 (:REWRITE DEFAULT-<-2))
 (86 86 (:REWRITE INEQUALITY-WITH-NFIX-HYP-2))
 (73 28 (:REWRITE ASH-0))
 (43 28 (:REWRITE RIGHT-SHIFT-TO-LOGTAIL))
 (30 30 (:TYPE-PRESCRIPTION ZIP))
 (28 28 (:REWRITE-QUOTED-CONSTANT IFIX-UNDER-INT-EQUIV))
 (15 15 (:REWRITE ZIP-OPEN))
 (8 8 (:REWRITE NFIX-WHEN-NOT-NATP))
 )
(COMBINE64U-UNSIGNED-BYTE
 (42 42 (:REWRITE BITOPS::LOGIOR-FOLD-CONSTS))
 (28 7 (:REWRITE ASH-0))
 (14 14 (:TYPE-PRESCRIPTION ZIP))
 (14 7 (:REWRITE RIGHT-SHIFT-TO-LOGTAIL))
 (8 8 (:REWRITE NFIX-WHEN-NOT-NATP))
 (7 7 (:REWRITE-QUOTED-CONSTANT IFIX-UNDER-INT-EQUIV))
 (7 7 (:REWRITE ZIP-OPEN))
 )
(COMBINE64S$INLINE
 (7520 56 (:LINEAR BITOPS::LOGIOR-<-0-LINEAR-2))
 (3396 56 (:LINEAR BITOPS::LOGIOR->=-0-LINEAR))
 (1372 280 (:REWRITE IFIX-WHEN-NOT-INTEGERP))
 (1372 280 (:REWRITE IFIX-WHEN-INTEGERP))
 (1218 56 (:LINEAR BITOPS::LOGIOR-<-0-LINEAR-1))
 (692 58 (:REWRITE BITOPS::ASH-<-0))
 (594 114 (:REWRITE DEFAULT-<-1))
 (356 356 (:REWRITE BITOPS::LOGIOR-FOLD-CONSTS))
 (114 114 (:REWRITE DEFAULT-<-2))
 (87 28 (:REWRITE ASH-0))
 (68 68 (:REWRITE INEQUALITY-WITH-NFIX-HYP-2))
 (43 28 (:REWRITE RIGHT-SHIFT-TO-LOGTAIL))
 (34 34 (:REWRITE-QUOTED-CONSTANT IFIX-UNDER-INT-EQUIV))
 (22 22 (:REWRITE BITOPS::SIGNED-BYTE-P-WHEN-SIGNED-BYTE-P-SMALLER))
 (22 22 (:REWRITE BITOPS::SIGNED-BYTE-P-MONOTONICITY))
 (20 6 (:REWRITE LOGEXT-IDENTITY))
 (9 9 (:REWRITE BITOPS::SIGNED-BYTE-P-INCR))
 (8 8 (:REWRITE NFIX-WHEN-NOT-NATP))
 (6 6 (:REWRITE-QUOTED-CONSTANT NFIX-UNDER-NAT-EQUIV))
 )
(COMBINE64S-UNSIGNED-BYTE
 (42 42 (:REWRITE BITOPS::LOGIOR-FOLD-CONSTS))
 (35 7 (:REWRITE ASH-0))
 (16 16 (:REWRITE BITOPS::SIGNED-BYTE-P-WHEN-SIGNED-BYTE-P-SMALLER))
 (16 16 (:REWRITE BITOPS::SIGNED-BYTE-P-MONOTONICITY))
 (14 7 (:REWRITE RIGHT-SHIFT-TO-LOGTAIL))
 (8 8 (:REWRITE-QUOTED-CONSTANT IFIX-UNDER-INT-EQUIV))
 (8 8 (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR))
 (8 8 (:REWRITE BITOPS::SIGNED-BYTE-P-INCR))
 (8 8 (:REWRITE NFIX-WHEN-NOT-NATP))
 (8 1 (:REWRITE LOGEXT-IDENTITY))
 (1 1 (:REWRITE-QUOTED-CONSTANT NFIX-UNDER-NAT-EQUIV))
 )
