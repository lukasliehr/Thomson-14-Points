module

public import N14.Box.Master
public import N14Cert.CapPpr.Tables0
public import N14Cert.CapPpr.Tables1
public import N14Cert.CapPpr.Tables2
public import N14Cert.CapPpr.Cells0
public import N14Cert.CapPpr.Cells1
public import N14Cert.CapPpr.Cells2
public import N14Cert.CapPpr.Cells3
public import N14Cert.CapPpr.Cells4
public import N14Cert.CapPpr.Cells5
public import N14Cert.CapPpr.Cells6
public import N14Cert.CapPpr.Cells7
public import N14Cert.CapPpr.Cells8
public import N14Cert.CapPpr.Cells9
public import N14Cert.CapPpr.Cells10
public import N14Cert.CapPpr.Cells11
public import N14Cert.CapPpr.Cells12
public import N14Cert.CapPpr.Cells13
public import N14Cert.CapPpr.Cells14
public import N14Cert.CapPpr.Cells15
public import N14Cert.CapPpr.Cells16
public import N14Cert.CapPpr.Cells17
public import N14Cert.CapPpr.Cells18
public import N14Cert.CapPpr.Cells19
public import N14Cert.CapPpr.Cells20
import CAP.Transport.Hex

@[expose] public section

namespace N14Cert.CapPpr

open N14.Box

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 100000

/-- The boxes of the groups 0 to 39. -/
noncomputable def boxes_p0 : List Bx :=
  [{ e1 := 1, c1 := 0, e2 := 1, c2 := 0, e3 := 1, c3 := 0 },
    { e1 := 1, c1 := 0, e2 := 1, c2 := 0, e3 := 1, c3 := 1 },
    { e1 := 4, c1 := 0, e2 := 2, c2 := 0, e3 := 1, c3 := 2 },
    { e1 := 4, c1 := 0, e2 := 2, c2 := 1, e3 := 2, c3 := 4 },
    { e1 := 4, c1 := 0, e2 := 3, c2 := 2, e3 := 2, c3 := 5 },
    { e1 := 4, c1 := 0, e2 := 3, c2 := 3, e3 := 3, c3 := 10 },
    { e1 := 4, c1 := 0, e2 := 4, c2 := 6, e3 := 3, c3 := 11 },
    { e1 := 4, c1 := 0, e2 := 4, c2 := 7, e3 := 3, c3 := 11 },
    { e1 := 4, c1 := 0, e2 := 3, c2 := 0, e3 := 2, c3 := 6 },
    { e1 := 4, c1 := 0, e2 := 3, c2 := 1, e3 := 3, c3 := 12 },
    { e1 := 4, c1 := 0, e2 := 3, c2 := 1, e3 := 3, c3 := 13 },
    { e1 := 4, c1 := 0, e2 := 4, c2 := 4, e3 := 4, c3 := 24 },
    { e1 := 4, c1 := 0, e2 := 4, c2 := 4, e3 := 4, c3 := 25 },
    { e1 := 4, c1 := 0, e2 := 4, c2 := 5, e3 := 4, c3 := 24 },
    { e1 := 4, c1 := 0, e2 := 4, c2 := 5, e3 := 4, c3 := 25 },
    { e1 := 4, c1 := 0, e2 := 3, c2 := 2, e3 := 3, c3 := 13 },
    { e1 := 4, c1 := 0, e2 := 4, c2 := 6, e3 := 3, c3 := 12 },
    { e1 := 4, c1 := 0, e2 := 4, c2 := 7, e3 := 4, c3 := 24 },
    { e1 := 4, c1 := 0, e2 := 4, c2 := 7, e3 := 4, c3 := 25 },
    { e1 := 4, c1 := 0, e2 := 4, c2 := 6, e3 := 3, c3 := 13 },
    { e1 := 4, c1 := 0, e2 := 4, c2 := 7, e3 := 3, c3 := 13 },
    { e1 := 4, c1 := 0, e2 := 3, c2 := 0, e3 := 3, c3 := 14 },
    { e1 := 6, c1 := 0, e2 := 6, c2 := 8, e3 := 5, c3 := 56 },
    { e1 := 6, c1 := 0, e2 := 6, c2 := 9, e3 := 5, c3 := 56 },
    { e1 := 6, c1 := 0, e2 := 6, c2 := 8, e3 := 6, c3 := 114 },
    { e1 := 6, c1 := 0, e2 := 6, c2 := 8, e3 := 6, c3 := 115 },
    { e1 := 6, c1 := 0, e2 := 6, c2 := 9, e3 := 5, c3 := 57 },
    { e1 := 5, c1 := 0, e2 := 5, c2 := 5, e3 := 4, c3 := 28 },
    { e1 := 4, c1 := 0, e2 := 4, c2 := 3, e3 := 3, c3 := 14 },
    { e1 := 4, c1 := 0, e2 := 2, c2 := 1, e3 := 3, c3 := 14 },
    { e1 := 1, c1 := 0, e2 := 1, c2 := 1, e3 := 1, c3 := 0 },
    { e1 := 4, c1 := 0, e2 := 2, c2 := 2, e3 := 1, c3 := 1 },
    { e1 := 4, c1 := 0, e2 := 2, c2 := 3, e3 := 2, c3 := 2 },
    { e1 := 4, c1 := 0, e2 := 3, c2 := 6, e3 := 2, c3 := 3 },
    { e1 := 4, c1 := 0, e2 := 3, c2 := 7, e3 := 3, c3 := 6 },
    { e1 := 4, c1 := 0, e2 := 4, c2 := 14, e3 := 4, c3 := 14 },
    { e1 := 5, c1 := 0, e2 := 5, c2 := 28, e3 := 4, c3 := 15 },
    { e1 := 5, c1 := 0, e2 := 5, c2 := 29, e3 := 4, c3 := 15 },
    { e1 := 4, c1 := 0, e2 := 4, c2 := 15, e3 := 3, c3 := 7 },
    { e1 := 4, c1 := 0, e2 := 3, c2 := 4, e3 := 2, c3 := 4 }]

theorem done_p0 : AllDone run boxes_p0 :=
  allDone_cons g0_ok <|
  allDone_cons g1_ok <|
  allDone_cons g2_ok <|
  allDone_cons g3_ok <|
  allDone_cons g4_ok <|
  allDone_cons g5_ok <|
  allDone_cons g6_ok <|
  allDone_cons g7_ok <|
  allDone_cons g8_ok <|
  allDone_cons g9_ok <|
  allDone_cons g10_ok <|
  allDone_cons g11_ok <|
  allDone_cons g12_ok <|
  allDone_cons g13_ok <|
  allDone_cons g14_ok <|
  allDone_cons g15_ok <|
  allDone_cons g16_ok <|
  allDone_cons g17_ok <|
  allDone_cons g18_ok <|
  allDone_cons g19_ok <|
  allDone_cons g20_ok <|
  allDone_cons g21_ok <|
  allDone_cons g22_ok <|
  allDone_cons g23_ok <|
  allDone_cons g24_ok <|
  allDone_cons g25_ok <|
  allDone_cons g26_ok <|
  allDone_cons g27_ok <|
  allDone_cons g28_ok <|
  allDone_cons g29_ok <|
  allDone_cons g30_ok <|
  allDone_cons g31_ok <|
  allDone_cons g32_ok <|
  allDone_cons g33_ok <|
  allDone_cons g34_ok <|
  allDone_cons g35_ok <|
  allDone_cons g36_ok <|
  allDone_cons g37_ok <|
  allDone_cons g38_ok <|
  allDone_cons g39_ok <|
  allDone_nil run

/-- The boxes of the groups 40 to 79. -/
noncomputable def boxes_p1 : List Bx :=
  [{ e1 := 4, c1 := 0, e2 := 3, c2 := 5, e3 := 3, c3 := 8 },
    { e1 := 4, c1 := 0, e2 := 4, c2 := 10, e3 := 4, c3 := 18 },
    { e1 := 5, c1 := 0, e2 := 5, c2 := 20, e3 := 4, c3 := 19 },
    { e1 := 5, c1 := 0, e2 := 5, c2 := 21, e3 := 4, c3 := 19 },
    { e1 := 5, c1 := 0, e2 := 5, c2 := 22, e3 := 4, c3 := 18 },
    { e1 := 5, c1 := 0, e2 := 5, c2 := 23, e3 := 4, c3 := 18 },
    { e1 := 4, c1 := 0, e2 := 4, c2 := 11, e3 := 4, c3 := 19 },
    { e1 := 4, c1 := 0, e2 := 4, c2 := 8, e3 := 4, c3 := 20 },
    { e1 := 5, c1 := 0, e2 := 5, c2 := 16, e3 := 4, c3 := 21 },
    { e1 := 6, c1 := 0, e2 := 6, c2 := 34, e3 := 5, c3 := 42 },
    { e1 := 6, c1 := 0, e2 := 6, c2 := 35, e3 := 5, c3 := 42 },
    { e1 := 5, c1 := 0, e2 := 5, c2 := 17, e3 := 5, c3 := 43 },
    { e1 := 5, c1 := 0, e2 := 5, c2 := 18, e3 := 5, c3 := 40 },
    { e1 := 5, c1 := 0, e2 := 5, c2 := 18, e3 := 5, c3 := 41 },
    { e1 := 5, c1 := 0, e2 := 5, c2 := 19, e3 := 4, c3 := 20 },
    { e1 := 5, c1 := 0, e2 := 5, c2 := 18, e3 := 4, c3 := 21 },
    { e1 := 5, c1 := 0, e2 := 5, c2 := 19, e3 := 4, c3 := 21 },
    { e1 := 4, c1 := 0, e2 := 4, c2 := 8, e3 := 4, c3 := 22 },
    { e1 := 4, c1 := 0, e2 := 4, c2 := 8, e3 := 4, c3 := 23 },
    { e1 := 5, c1 := 0, e2 := 5, c2 := 18, e3 := 4, c3 := 22 },
    { e1 := 5, c1 := 0, e2 := 5, c2 := 19, e3 := 4, c3 := 22 },
    { e1 := 5, c1 := 0, e2 := 5, c2 := 18, e3 := 5, c3 := 46 },
    { e1 := 5, c1 := 0, e2 := 5, c2 := 18, e3 := 5, c3 := 47 },
    { e1 := 6, c1 := 0, e2 := 6, c2 := 38, e3 := 5, c3 := 46 },
    { e1 := 6, c1 := 0, e2 := 6, c2 := 39, e3 := 5, c3 := 46 },
    { e1 := 6, c1 := 0, e2 := 6, c2 := 38, e3 := 5, c3 := 47 },
    { e1 := 6, c1 := 0, e2 := 6, c2 := 39, e3 := 5, c3 := 47 },
    { e1 := 4, c1 := 0, e2 := 4, c2 := 10, e3 := 4, c3 := 20 },
    { e1 := 4, c1 := 0, e2 := 4, c2 := 10, e3 := 4, c3 := 21 },
    { e1 := 4, c1 := 0, e2 := 4, c2 := 11, e3 := 4, c3 := 20 },
    { e1 := 5, c1 := 0, e2 := 5, c2 := 22, e3 := 4, c3 := 21 },
    { e1 := 5, c1 := 0, e2 := 5, c2 := 23, e3 := 5, c3 := 42 },
    { e1 := 5, c1 := 0, e2 := 5, c2 := 23, e3 := 5, c3 := 43 },
    { e1 := 5, c1 := 0, e2 := 5, c2 := 20, e3 := 5, c3 := 44 },
    { e1 := 5, c1 := 0, e2 := 5, c2 := 20, e3 := 5, c3 := 45 },
    { e1 := 5, c1 := 0, e2 := 5, c2 := 21, e3 := 5, c3 := 44 },
    { e1 := 6, c1 := 0, e2 := 6, c2 := 42, e3 := 5, c3 := 45 },
    { e1 := 6, c1 := 0, e2 := 6, c2 := 43, e3 := 5, c3 := 45 },
    { e1 := 6, c1 := 0, e2 := 6, c2 := 40, e3 := 5, c3 := 46 },
    { e1 := 6, c1 := 0, e2 := 6, c2 := 41, e3 := 5, c3 := 46 }]

theorem done_p1 : AllDone run boxes_p1 :=
  allDone_cons g40_ok <|
  allDone_cons g41_ok <|
  allDone_cons g42_ok <|
  allDone_cons g43_ok <|
  allDone_cons g44_ok <|
  allDone_cons g45_ok <|
  allDone_cons g46_ok <|
  allDone_cons g47_ok <|
  allDone_cons g48_ok <|
  allDone_cons g49_ok <|
  allDone_cons g50_ok <|
  allDone_cons g51_ok <|
  allDone_cons g52_ok <|
  allDone_cons g53_ok <|
  allDone_cons g54_ok <|
  allDone_cons g55_ok <|
  allDone_cons g56_ok <|
  allDone_cons g57_ok <|
  allDone_cons g58_ok <|
  allDone_cons g59_ok <|
  allDone_cons g60_ok <|
  allDone_cons g61_ok <|
  allDone_cons g62_ok <|
  allDone_cons g63_ok <|
  allDone_cons g64_ok <|
  allDone_cons g65_ok <|
  allDone_cons g66_ok <|
  allDone_cons g67_ok <|
  allDone_cons g68_ok <|
  allDone_cons g69_ok <|
  allDone_cons g70_ok <|
  allDone_cons g71_ok <|
  allDone_cons g72_ok <|
  allDone_cons g73_ok <|
  allDone_cons g74_ok <|
  allDone_cons g75_ok <|
  allDone_cons g76_ok <|
  allDone_cons g77_ok <|
  allDone_cons g78_ok <|
  allDone_cons g79_ok <|
  allDone_nil run

/-- The boxes of the groups 80 to 119. -/
noncomputable def boxes_p2 : List Bx :=
  [{ e1 := 6, c1 := 0, e2 := 6, c2 := 40, e3 := 5, c3 := 47 },
    { e1 := 6, c1 := 0, e2 := 6, c2 := 41, e3 := 5, c3 := 47 },
    { e1 := 6, c1 := 0, e2 := 6, c2 := 42, e3 := 5, c3 := 46 },
    { e1 := 6, c1 := 0, e2 := 6, c2 := 43, e3 := 5, c3 := 46 },
    { e1 := 5, c1 := 0, e2 := 5, c2 := 21, e3 := 5, c3 := 47 },
    { e1 := 6, c1 := 0, e2 := 6, c2 := 44, e3 := 5, c3 := 44 },
    { e1 := 6, c1 := 0, e2 := 6, c2 := 45, e3 := 5, c3 := 44 },
    { e1 := 5, c1 := 0, e2 := 5, c2 := 22, e3 := 5, c3 := 45 },
    { e1 := 5, c1 := 0, e2 := 5, c2 := 23, e3 := 5, c3 := 44 },
    { e1 := 5, c1 := 0, e2 := 5, c2 := 23, e3 := 5, c3 := 45 },
    { e1 := 4, c1 := 0, e2 := 4, c2 := 11, e3 := 4, c3 := 23 },
    { e1 := 4, c1 := 0, e2 := 4, c2 := 12, e3 := 4, c3 := 16 },
    { e1 := 5, c1 := 0, e2 := 5, c2 := 24, e3 := 5, c3 := 34 },
    { e1 := 5, c1 := 0, e2 := 5, c2 := 24, e3 := 5, c3 := 35 },
    { e1 := 5, c1 := 0, e2 := 5, c2 := 25, e3 := 4, c3 := 17 },
    { e1 := 5, c1 := 0, e2 := 5, c2 := 26, e3 := 5, c3 := 32 },
    { e1 := 5, c1 := 0, e2 := 5, c2 := 26, e3 := 5, c3 := 33 },
    { e1 := 5, c1 := 0, e2 := 5, c2 := 27, e3 := 4, c3 := 16 },
    { e1 := 4, c1 := 0, e2 := 4, c2 := 13, e3 := 4, c3 := 17 },
    { e1 := 4, c1 := 0, e2 := 4, c2 := 12, e3 := 3, c3 := 9 },
    { e1 := 4, c1 := 0, e2 := 4, c2 := 13, e3 := 3, c3 := 9 },
    { e1 := 4, c1 := 0, e2 := 3, c2 := 7, e3 := 3, c3 := 8 },
    { e1 := 4, c1 := 0, e2 := 4, c2 := 14, e3 := 4, c3 := 18 },
    { e1 := 5, c1 := 0, e2 := 5, c2 := 28, e3 := 4, c3 := 19 },
    { e1 := 5, c1 := 0, e2 := 5, c2 := 29, e3 := 4, c3 := 19 },
    { e1 := 4, c1 := 0, e2 := 4, c2 := 15, e3 := 4, c3 := 18 },
    { e1 := 4, c1 := 0, e2 := 4, c2 := 15, e3 := 4, c3 := 19 },
    { e1 := 4, c1 := 0, e2 := 4, c2 := 12, e3 := 4, c3 := 20 },
    { e1 := 5, c1 := 0, e2 := 5, c2 := 24, e3 := 5, c3 := 42 },
    { e1 := 5, c1 := 0, e2 := 5, c2 := 24, e3 := 5, c3 := 43 },
    { e1 := 5, c1 := 0, e2 := 5, c2 := 25, e3 := 4, c3 := 21 },
    { e1 := 5, c1 := 0, e2 := 5, c2 := 26, e3 := 4, c3 := 20 },
    { e1 := 5, c1 := 0, e2 := 5, c2 := 27, e3 := 4, c3 := 20 },
    { e1 := 4, c1 := 0, e2 := 4, c2 := 13, e3 := 4, c3 := 21 },
    { e1 := 4, c1 := 0, e2 := 3, c2 := 6, e3 := 3, c3 := 11 },
    { e1 := 4, c1 := 0, e2 := 3, c2 := 7, e3 := 2, c3 := 5 },
    { e1 := 4, c1 := 0, e2 := 4, c2 := 8, e3 := 4, c3 := 24 },
    { e1 := 4, c1 := 0, e2 := 4, c2 := 8, e3 := 4, c3 := 25 },
    { e1 := 5, c1 := 0, e2 := 5, c2 := 18, e3 := 5, c3 := 48 },
    { e1 := 5, c1 := 0, e2 := 5, c2 := 18, e3 := 5, c3 := 49 }]

theorem done_p2 : AllDone run boxes_p2 :=
  allDone_cons g80_ok <|
  allDone_cons g81_ok <|
  allDone_cons g82_ok <|
  allDone_cons g83_ok <|
  allDone_cons g84_ok <|
  allDone_cons g85_ok <|
  allDone_cons g86_ok <|
  allDone_cons g87_ok <|
  allDone_cons g88_ok <|
  allDone_cons g89_ok <|
  allDone_cons g90_ok <|
  allDone_cons g91_ok <|
  allDone_cons g92_ok <|
  allDone_cons g93_ok <|
  allDone_cons g94_ok <|
  allDone_cons g95_ok <|
  allDone_cons g96_ok <|
  allDone_cons g97_ok <|
  allDone_cons g98_ok <|
  allDone_cons g99_ok <|
  allDone_cons g100_ok <|
  allDone_cons g101_ok <|
  allDone_cons g102_ok <|
  allDone_cons g103_ok <|
  allDone_cons g104_ok <|
  allDone_cons g105_ok <|
  allDone_cons g106_ok <|
  allDone_cons g107_ok <|
  allDone_cons g108_ok <|
  allDone_cons g109_ok <|
  allDone_cons g110_ok <|
  allDone_cons g111_ok <|
  allDone_cons g112_ok <|
  allDone_cons g113_ok <|
  allDone_cons g114_ok <|
  allDone_cons g115_ok <|
  allDone_cons g116_ok <|
  allDone_cons g117_ok <|
  allDone_cons g118_ok <|
  allDone_cons g119_ok <|
  allDone_nil run

/-- The boxes of the groups 120 to 137. -/
noncomputable def boxes_p3 : List Bx :=
  [{ e1 := 6, c1 := 0, e2 := 6, c2 := 38, e3 := 5, c3 := 48 },
    { e1 := 6, c1 := 0, e2 := 6, c2 := 39, e3 := 5, c3 := 48 },
    { e1 := 5, c1 := 0, e2 := 5, c2 := 19, e3 := 5, c3 := 49 },
    { e1 := 4, c1 := 0, e2 := 4, c2 := 9, e3 := 4, c3 := 25 },
    { e1 := 4, c1 := 0, e2 := 3, c2 := 4, e3 := 3, c3 := 13 },
    { e1 := 4, c1 := 0, e2 := 3, c2 := 5, e3 := 2, c3 := 6 },
    { e1 := 4, c1 := 0, e2 := 2, c2 := 3, e3 := 2, c3 := 6 },
    { e1 := 2, c1 := 0, e2 := 1, c2 := 1, e3 := 2, c3 := 7 },
    { e1 := 1, c1 := 0, e2 := 1, c2 := 2, e3 := 1, c3 := 1 },
    { e1 := 4, c1 := 0, e2 := 4, c2 := 16, e3 := 3, c3 := 8 },
    { e1 := 4, c1 := 0, e2 := 4, c2 := 17, e3 := 3, c3 := 8 },
    { e1 := 4, c1 := 0, e2 := 3, c2 := 8, e3 := 3, c3 := 9 },
    { e1 := 4, c1 := 0, e2 := 3, c2 := 9, e3 := 2, c3 := 4 },
    { e1 := 4, c1 := 0, e2 := 2, c2 := 4, e3 := 2, c3 := 5 },
    { e1 := 4, c1 := 0, e2 := 2, c2 := 5, e3 := 1, c3 := 2 },
    { e1 := 1, c1 := 0, e2 := 1, c2 := 2, e3 := 1, c3 := 3 },
    { e1 := 1, c1 := 0, e2 := 1, c2 := 3, e3 := 1, c3 := 2 },
    { e1 := 1, c1 := 0, e2 := 1, c2 := 3, e3 := 1, c3 := 3 }]

theorem done_p3 : AllDone run boxes_p3 :=
  allDone_cons g120_ok <|
  allDone_cons g121_ok <|
  allDone_cons g122_ok <|
  allDone_cons g123_ok <|
  allDone_cons g124_ok <|
  allDone_cons g125_ok <|
  allDone_cons g126_ok <|
  allDone_cons g127_ok <|
  allDone_cons g128_ok <|
  allDone_cons g129_ok <|
  allDone_cons g130_ok <|
  allDone_cons g131_ok <|
  allDone_cons g132_ok <|
  allDone_cons g133_ok <|
  allDone_cons g134_ok <|
  allDone_cons g135_ok <|
  allDone_cons g136_ok <|
  allDone_cons g137_ok <|
  allDone_nil run

noncomputable def boxes_q0_0 : List Bx :=
  boxes_p0 ++ (boxes_p1 ++ (boxes_p2 ++ (boxes_p3)))

theorem done_q0_0 : AllDone run boxes_q0_0 :=
  allDone_append done_p0 <| allDone_append done_p1 <| allDone_append done_p2 <| done_p3

/-- **The master tree**: the boxes of the groups, and boxes on which a cut fails, are the leaves of
trees of bisections of the boxes of the grid of the level 1. -/
theorem master_ok : masterOk run 1 (hex% "fffffffffffffffffffffffffffffff6640fffffffd2f92f99423ffff4bfe4e67efd39ef7ff92ff9399bfeff492ffd2fd3f493fd3be49fed3be6ff4fd2f93f4be7f4ff92ffd2d399ff4bf4e7b640fffd39eded03ffffffe4fd249d48ff7edbfbe67ed423ff7b7b40f") boxes_q0_0 = true := by
  decide +kernel

/-- **The slack of the run is nonnegative on its domain**: at the points of `[-1, 1)³` at which the Gram
polynomial, the functions of the cuts and the polynomial constraints of the run are nonnegative. The slack
is the polynomial of the numeral `run.PpM` plus the functions of one variable of the tables, in the units
of the run. -/
theorem slack_nonneg (x1 x2 x3 : ℝ) (h1 : -1 ≤ x1) (h2 : -1 ≤ x2) (h3 : -1 ≤ x3) (hD : Dom run x1 x2 x3) :
    0 ≤ slackFn run tab0 tab1 tab2 x1 x2 x3 :=
  run_sound_master run run_ok tab0 tab1 tab2 ⟨rfl, rfl⟩ ⟨rfl, rfl⟩ ⟨rfl, rfl⟩
    table0_ok table1_ok table2_ok 1 _ boxes_q0_0 master_ok done_q0_0
    x1 x2 x3 h1 h2 h3 hD

/-- info: 'N14Cert.CapPpr.slack_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms slack_nonneg

end N14Cert.CapPpr
