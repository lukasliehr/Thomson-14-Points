module

public import N14.Box.Master
public import N14Cert.Case2Prr.Tables0
public import N14Cert.Case2Prr.Tables1
public import N14Cert.Case2Prr.Cells0
public import N14Cert.Case2Prr.Cells1
public import N14Cert.Case2Prr.Cells2
public import N14Cert.Case2Prr.Cells3
public import N14Cert.Case2Prr.Cells4
public import N14Cert.Case2Prr.Cells5
public import N14Cert.Case2Prr.Cells6
public import N14Cert.Case2Prr.Cells7
public import N14Cert.Case2Prr.Cells8
public import N14Cert.Case2Prr.Cells9
public import N14Cert.Case2Prr.Cells10
public import N14Cert.Case2Prr.Cells11
public import N14Cert.Case2Prr.Cells12
public import N14Cert.Case2Prr.Cells13
public import N14Cert.Case2Prr.Cells14
public import N14Cert.Case2Prr.Cells15
public import N14Cert.Case2Prr.Cells16
public import N14Cert.Case2Prr.Cells17
public import N14Cert.Case2Prr.Cells18
public import N14Cert.Case2Prr.Cells19
import CAP.Transport.Hex

@[expose] public section

namespace N14Cert.Case2Prr

open N14.Box

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 100000

/-- The boxes of the groups 0 to 39. -/
noncomputable def boxes_p0 : List Bx :=
  [{ e1 := 1, c1 := 0, e2 := 1, c2 := 0, e3 := 1, c3 := 0 },
    { e1 := 2, c1 := 0, e2 := 1, c2 := 0, e3 := 1, c3 := 1 },
    { e1 := 2, c1 := 1, e2 := 2, c2 := 0, e3 := 1, c3 := 1 },
    { e1 := 3, c1 := 2, e2 := 2, c2 := 1, e3 := 2, c3 := 2 },
    { e1 := 3, c1 := 3, e2 := 3, c2 := 2, e3 := 2, c3 := 2 },
    { e1 := 3, c1 := 3, e2 := 3, c2 := 3, e3 := 3, c3 := 4 },
    { e1 := 3, c1 := 3, e2 := 3, c2 := 3, e3 := 3, c3 := 5 },
    { e1 := 3, c1 := 2, e2 := 2, c2 := 1, e3 := 2, c3 := 3 },
    { e1 := 3, c1 := 3, e2 := 2, c2 := 1, e3 := 2, c3 := 3 },
    { e1 := 2, c1 := 0, e2 := 1, c2 := 0, e3 := 1, c3 := 2 },
    { e1 := 2, c1 := 1, e2 := 1, c2 := 0, e3 := 1, c3 := 2 },
    { e1 := 1, c1 := 0, e2 := 1, c2 := 0, e3 := 1, c3 := 3 },
    { e1 := 1, c1 := 0, e2 := 1, c2 := 1, e3 := 1, c3 := 0 },
    { e1 := 2, c1 := 0, e2 := 1, c2 := 1, e3 := 1, c3 := 1 },
    { e1 := 3, c1 := 2, e2 := 3, c2 := 4, e3 := 3, c3 := 4 },
    { e1 := 3, c1 := 2, e2 := 3, c2 := 4, e3 := 3, c3 := 5 },
    { e1 := 3, c1 := 2, e2 := 3, c2 := 5, e3 := 2, c3 := 2 },
    { e1 := 3, c1 := 3, e2 := 2, c2 := 2, e3 := 2, c3 := 2 },
    { e1 := 2, c1 := 1, e2 := 2, c2 := 2, e3 := 2, c3 := 3 },
    { e1 := 2, c1 := 1, e2 := 2, c2 := 3, e3 := 1, c3 := 1 },
    { e1 := 1, c1 := 0, e2 := 1, c2 := 1, e3 := 1, c3 := 2 },
    { e1 := 1, c1 := 0, e2 := 1, c2 := 1, e3 := 2, c3 := 6 },
    { e1 := 1, c1 := 0, e2 := 1, c2 := 1, e3 := 2, c3 := 7 },
    { e1 := 1, c1 := 0, e2 := 1, c2 := 2, e3 := 1, c3 := 0 },
    { e1 := 1, c1 := 0, e2 := 1, c2 := 2, e3 := 1, c3 := 1 },
    { e1 := 1, c1 := 0, e2 := 1, c2 := 2, e3 := 1, c3 := 2 },
    { e1 := 2, c1 := 0, e2 := 1, c2 := 2, e3 := 2, c3 := 6 },
    { e1 := 2, c1 := 1, e2 := 1, c2 := 2, e3 := 2, c3 := 6 },
    { e1 := 1, c1 := 0, e2 := 1, c2 := 2, e3 := 2, c3 := 7 },
    { e1 := 2, c1 := 0, e2 := 2, c2 := 6, e3 := 1, c3 := 0 },
    { e1 := 3, c1 := 2, e2 := 2, c2 := 6, e3 := 2, c3 := 0 },
    { e1 := 3, c1 := 3, e2 := 2, c2 := 6, e3 := 2, c3 := 0 },
    { e1 := 2, c1 := 1, e2 := 2, c2 := 6, e3 := 2, c3 := 1 },
    { e1 := 1, c1 := 0, e2 := 2, c2 := 7, e3 := 1, c3 := 0 },
    { e1 := 1, c1 := 0, e2 := 1, c2 := 3, e3 := 1, c3 := 1 },
    { e1 := 2, c1 := 0, e2 := 2, c2 := 6, e3 := 1, c3 := 2 },
    { e1 := 2, c1 := 1, e2 := 2, c2 := 6, e3 := 1, c3 := 2 },
    { e1 := 1, c1 := 0, e2 := 2, c2 := 7, e3 := 1, c3 := 2 },
    { e1 := 1, c1 := 0, e2 := 2, c2 := 6, e3 := 1, c3 := 3 },
    { e1 := 1, c1 := 0, e2 := 2, c2 := 7, e3 := 2, c3 := 6 }]

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
  [{ e1 := 1, c1 := 0, e2 := 3, c2 := 14, e3 := 2, c3 := 7 },
    { e1 := 1, c1 := 0, e2 := 3, c2 := 15, e3 := 2, c3 := 7 },
    { e1 := 1, c1 := 1, e2 := 1, c2 := 0, e3 := 1, c3 := 0 },
    { e1 := 1, c1 := 1, e2 := 1, c2 := 0, e3 := 1, c3 := 1 },
    { e1 := 1, c1 := 1, e2 := 1, c2 := 0, e3 := 1, c3 := 2 },
    { e1 := 1, c1 := 1, e2 := 1, c2 := 0, e3 := 1, c3 := 3 },
    { e1 := 2, c1 := 2, e2 := 2, c2 := 2, e3 := 1, c3 := 0 },
    { e1 := 2, c1 := 2, e2 := 2, c2 := 3, e3 := 1, c3 := 0 },
    { e1 := 2, c1 := 3, e2 := 1, c2 := 1, e3 := 1, c3 := 0 },
    { e1 := 1, c1 := 1, e2 := 1, c2 := 1, e3 := 1, c3 := 1 },
    { e1 := 1, c1 := 1, e2 := 1, c2 := 1, e3 := 1, c3 := 2 },
    { e1 := 1, c1 := 1, e2 := 1, c2 := 1, e3 := 1, c3 := 3 },
    { e1 := 2, c1 := 2, e2 := 2, c2 := 4, e3 := 1, c3 := 0 },
    { e1 := 3, c1 := 4, e2 := 2, c2 := 5, e3 := 2, c3 := 0 },
    { e1 := 3, c1 := 5, e2 := 2, c2 := 5, e3 := 2, c3 := 0 },
    { e1 := 2, c1 := 2, e2 := 2, c2 := 5, e3 := 2, c3 := 1 },
    { e1 := 3, c1 := 6, e2 := 2, c2 := 4, e3 := 2, c3 := 0 },
    { e1 := 3, c1 := 7, e2 := 2, c2 := 4, e3 := 2, c3 := 0 },
    { e1 := 2, c1 := 3, e2 := 2, c2 := 4, e3 := 2, c3 := 1 },
    { e1 := 2, c1 := 3, e2 := 2, c2 := 5, e3 := 1, c3 := 0 },
    { e1 := 1, c1 := 1, e2 := 1, c2 := 2, e3 := 1, c3 := 1 },
    { e1 := 1, c1 := 1, e2 := 1, c2 := 2, e3 := 1, c3 := 2 },
    { e1 := 1, c1 := 1, e2 := 1, c2 := 2, e3 := 1, c3 := 3 },
    { e1 := 3, c1 := 4, e2 := 2, c2 := 6, e3 := 2, c3 := 0 },
    { e1 := 3, c1 := 5, e2 := 2, c2 := 6, e3 := 2, c3 := 0 },
    { e1 := 2, c1 := 2, e2 := 2, c2 := 6, e3 := 2, c3 := 1 },
    { e1 := 3, c1 := 6, e2 := 2, c2 := 6, e3 := 2, c3 := 0 },
    { e1 := 3, c1 := 7, e2 := 2, c2 := 6, e3 := 2, c3 := 0 },
    { e1 := 2, c1 := 3, e2 := 2, c2 := 6, e3 := 2, c3 := 1 },
    { e1 := 1, c1 := 1, e2 := 2, c2 := 7, e3 := 1, c3 := 0 },
    { e1 := 1, c1 := 1, e2 := 1, c2 := 3, e3 := 1, c3 := 1 },
    { e1 := 1, c1 := 1, e2 := 1, c2 := 3, e3 := 1, c3 := 2 },
    { e1 := 2, c1 := 2, e2 := 2, c2 := 6, e3 := 2, c3 := 6 },
    { e1 := 2, c1 := 3, e2 := 2, c2 := 6, e3 := 2, c3 := 6 },
    { e1 := 1, c1 := 1, e2 := 2, c2 := 6, e3 := 2, c3 := 7 },
    { e1 := 1, c1 := 1, e2 := 2, c2 := 7, e3 := 2, c3 := 6 },
    { e1 := 1, c1 := 1, e2 := 3, c2 := 14, e3 := 2, c3 := 7 },
    { e1 := 1, c1 := 1, e2 := 3, c2 := 15, e3 := 2, c3 := 7 },
    { e1 := 1, c1 := 2, e2 := 1, c2 := 1, e3 := 1, c3 := 0 },
    { e1 := 1, c1 := 2, e2 := 1, c2 := 1, e3 := 1, c3 := 1 }]

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
  [{ e1 := 1, c1 := 2, e2 := 1, c2 := 1, e3 := 1, c3 := 2 },
    { e1 := 1, c1 := 2, e2 := 1, c2 := 1, e3 := 1, c3 := 3 },
    { e1 := 3, c1 := 8, e2 := 2, c2 := 4, e3 := 2, c3 := 0 },
    { e1 := 3, c1 := 9, e2 := 2, c2 := 4, e3 := 2, c3 := 0 },
    { e1 := 2, c1 := 4, e2 := 2, c2 := 4, e3 := 2, c3 := 1 },
    { e1 := 2, c1 := 4, e2 := 2, c2 := 5, e3 := 2, c3 := 0 },
    { e1 := 2, c1 := 4, e2 := 2, c2 := 5, e3 := 2, c3 := 1 },
    { e1 := 2, c1 := 5, e2 := 2, c2 := 4, e3 := 1, c3 := 0 },
    { e1 := 2, c1 := 5, e2 := 2, c2 := 5, e3 := 2, c3 := 0 },
    { e1 := 3, c1 := 10, e2 := 2, c2 := 5, e3 := 2, c3 := 1 },
    { e1 := 3, c1 := 11, e2 := 2, c2 := 5, e3 := 2, c3 := 1 },
    { e1 := 1, c1 := 2, e2 := 1, c2 := 2, e3 := 1, c3 := 1 },
    { e1 := 1, c1 := 2, e2 := 1, c2 := 2, e3 := 1, c3 := 2 },
    { e1 := 1, c1 := 2, e2 := 1, c2 := 2, e3 := 1, c3 := 3 },
    { e1 := 3, c1 := 8, e2 := 3, c2 := 12, e3 := 3, c3 := 0 },
    { e1 := 3, c1 := 8, e2 := 3, c2 := 12, e3 := 3, c3 := 1 },
    { e1 := 3, c1 := 8, e2 := 3, c2 := 13, e3 := 2, c3 := 0 },
    { e1 := 3, c1 := 9, e2 := 2, c2 := 6, e3 := 2, c3 := 0 },
    { e1 := 3, c1 := 8, e2 := 2, c2 := 6, e3 := 2, c3 := 1 },
    { e1 := 3, c1 := 9, e2 := 3, c2 := 12, e3 := 2, c3 := 1 },
    { e1 := 3, c1 := 9, e2 := 3, c2 := 13, e3 := 2, c3 := 1 },
    { e1 := 2, c1 := 5, e2 := 2, c2 := 6, e3 := 1, c3 := 0 },
    { e1 := 1, c1 := 2, e2 := 2, c2 := 7, e3 := 1, c3 := 0 },
    { e1 := 1, c1 := 2, e2 := 1, c2 := 3, e3 := 1, c3 := 1 },
    { e1 := 1, c1 := 2, e2 := 1, c2 := 3, e3 := 1, c3 := 2 },
    { e1 := 1, c1 := 2, e2 := 2, c2 := 6, e3 := 1, c3 := 3 },
    { e1 := 1, c1 := 2, e2 := 2, c2 := 7, e3 := 2, c3 := 6 },
    { e1 := 1, c1 := 2, e2 := 3, c2 := 14, e3 := 2, c3 := 7 },
    { e1 := 1, c1 := 2, e2 := 3, c2 := 15, e3 := 2, c3 := 7 },
    { e1 := 1, c1 := 3, e2 := 1, c2 := 2, e3 := 1, c3 := 0 },
    { e1 := 1, c1 := 3, e2 := 1, c2 := 2, e3 := 1, c3 := 1 },
    { e1 := 1, c1 := 3, e2 := 1, c2 := 2, e3 := 1, c3 := 2 },
    { e1 := 1, c1 := 3, e2 := 1, c2 := 2, e3 := 1, c3 := 3 },
    { e1 := 2, c1 := 6, e2 := 1, c2 := 3, e3 := 1, c3 := 0 },
    { e1 := 2, c1 := 7, e2 := 1, c2 := 3, e3 := 1, c3 := 0 },
    { e1 := 2, c1 := 6, e2 := 1, c2 := 3, e3 := 1, c3 := 1 },
    { e1 := 2, c1 := 7, e2 := 1, c2 := 3, e3 := 1, c3 := 1 },
    { e1 := 2, c1 := 6, e2 := 1, c2 := 3, e3 := 1, c3 := 2 },
    { e1 := 2, c1 := 7, e2 := 1, c2 := 3, e3 := 1, c3 := 2 },
    { e1 := 2, c1 := 6, e2 := 2, c2 := 6, e3 := 1, c3 := 3 }]

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

/-- The boxes of the groups 120 to 133. -/
noncomputable def boxes_p3 : List Bx :=
  [{ e1 := 2, c1 := 6, e2 := 2, c2 := 7, e3 := 2, c3 := 6 },
    { e1 := 2, c1 := 6, e2 := 3, c2 := 14, e3 := 2, c3 := 7 },
    { e1 := 2, c1 := 6, e2 := 3, c2 := 15, e3 := 2, c3 := 7 },
    { e1 := 2, c1 := 7, e2 := 2, c2 := 6, e3 := 1, c3 := 3 },
    { e1 := 2, c1 := 7, e2 := 2, c2 := 7, e3 := 2, c3 := 6 },
    { e1 := 3, c1 := 14, e2 := 3, c2 := 14, e3 := 2, c3 := 7 },
    { e1 := 3, c1 := 14, e2 := 3, c2 := 15, e3 := 2, c3 := 7 },
    { e1 := 3, c1 := 15, e2 := 3, c2 := 14, e3 := 2, c3 := 7 },
    { e1 := 3, c1 := 15, e2 := 3, c2 := 15, e3 := 3, c3 := 14 },
    { e1 := 4, c1 := 30, e2 := 3, c2 := 15, e3 := 3, c3 := 15 },
    { e1 := 4, c1 := 31, e2 := 4, c2 := 30, e3 := 3, c3 := 15 },
    { e1 := 4, c1 := 31, e2 := 4, c2 := 31, e3 := 4, c3 := 30 },
    { e1 := 5, c1 := 62, e2 := 4, c2 := 31, e3 := 4, c3 := 31 },
    { e1 := 5, c1 := 63, e2 := 4, c2 := 31, e3 := 4, c3 := 31 }]

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
  allDone_nil run

noncomputable def boxes_q0_0 : List Bx :=
  boxes_p0 ++ (boxes_p1 ++ (boxes_p2 ++ (boxes_p3)))

theorem done_q0_0 : AllDone run boxes_q0_0 :=
  allDone_append done_p0 <| allDone_append done_p1 <| allDone_append done_p2 <| done_p3

/-- **The master tree**: the boxes of the groups, and boxes on which a cut fails, are the leaves of
trees of bisections of the boxes of the grid of the level 1. -/
theorem master_ok : masterOk run 1 (hex% "f3b73b7d3b7ded3cf3cfffffff7b7ffdcff921ffcedfbf24fffff7bf27ffcbf21fffc9fcb4fff4fff7b7f1ffcb1fcbffbfff9273fcf3edcb73") boxes_q0_0 = true := by
  decide +kernel

/-- **The slack of the run is nonnegative on its domain**: at the points of `[-1, 1)³` at which the Gram
polynomial, the functions of the cuts and the polynomial constraints of the run are nonnegative. The slack
is the polynomial of the numeral `run.PpM` plus the functions of one variable of the tables, in the units
of the run. -/
theorem slack_nonneg (x1 x2 x3 : ℝ) (h1 : -1 ≤ x1) (h2 : -1 ≤ x2) (h3 : -1 ≤ x3) (hD : Dom run x1 x2 x3) :
    0 ≤ slackFn run tab0 tab0 tab1 x1 x2 x3 :=
  run_sound_master run run_ok tab0 tab0 tab1 ⟨rfl, rfl⟩ ⟨rfl, rfl⟩ ⟨rfl, rfl⟩
    table0_ok table0_ok table1_ok 1 _ boxes_q0_0 master_ok done_q0_0
    x1 x2 x3 h1 h2 h3 hD

/-- info: 'N14Cert.Case2Prr.slack_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms slack_nonneg

end N14Cert.Case2Prr
