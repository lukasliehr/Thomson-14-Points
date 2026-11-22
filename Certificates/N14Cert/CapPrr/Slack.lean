module

public import N14.Box.Master
public import N14Cert.CapPrr.Tables0
public import N14Cert.CapPrr.Tables1
public import N14Cert.CapPrr.Tables2
public import N14Cert.CapPrr.Cells0
public import N14Cert.CapPrr.Cells1
public import N14Cert.CapPrr.Cells2
public import N14Cert.CapPrr.Cells3
public import N14Cert.CapPrr.Cells4
public import N14Cert.CapPrr.Cells5
public import N14Cert.CapPrr.Cells6
public import N14Cert.CapPrr.Cells7
public import N14Cert.CapPrr.Cells8
public import N14Cert.CapPrr.Cells9
public import N14Cert.CapPrr.Cells10
public import N14Cert.CapPrr.Cells11
public import N14Cert.CapPrr.Cells12
public import N14Cert.CapPrr.Cells13
public import N14Cert.CapPrr.Cells14
public import N14Cert.CapPrr.Cells15
public import N14Cert.CapPrr.Cells16
public import N14Cert.CapPrr.Cells17
public import N14Cert.CapPrr.Cells18
public import N14Cert.CapPrr.Cells19
public import N14Cert.CapPrr.Cells20
public import N14Cert.CapPrr.Cells21
public import N14Cert.CapPrr.Cells22
public import N14Cert.CapPrr.Cells23
public import N14Cert.CapPrr.Cells24
public import N14Cert.CapPrr.Cells25
public import N14Cert.CapPrr.Cells26
public import N14Cert.CapPrr.Cells27
public import N14Cert.CapPrr.Cells28
import CAP.Transport.Hex

@[expose] public section

namespace N14Cert.CapPrr

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
    { e1 := 3, c1 := 3, e2 := 3, c2 := 3, e3 := 2, c3 := 2 },
    { e1 := 2, c1 := 1, e2 := 2, c2 := 1, e3 := 2, c3 := 3 },
    { e1 := 1, c1 := 0, e2 := 1, c2 := 0, e3 := 1, c3 := 2 },
    { e1 := 1, c1 := 0, e2 := 1, c2 := 0, e3 := 1, c3 := 3 },
    { e1 := 1, c1 := 0, e2 := 1, c2 := 1, e3 := 1, c3 := 0 },
    { e1 := 2, c1 := 0, e2 := 1, c2 := 1, e3 := 1, c3 := 1 },
    { e1 := 3, c1 := 2, e2 := 2, c2 := 2, e3 := 2, c3 := 2 },
    { e1 := 3, c1 := 3, e2 := 2, c2 := 2, e3 := 2, c3 := 2 },
    { e1 := 2, c1 := 1, e2 := 2, c2 := 2, e3 := 2, c3 := 3 },
    { e1 := 2, c1 := 1, e2 := 2, c2 := 3, e3 := 1, c3 := 1 },
    { e1 := 1, c1 := 0, e2 := 1, c2 := 1, e3 := 1, c3 := 2 },
    { e1 := 1, c1 := 0, e2 := 1, c2 := 1, e3 := 2, c3 := 6 },
    { e1 := 1, c1 := 0, e2 := 1, c2 := 1, e3 := 2, c3 := 7 },
    { e1 := 2, c1 := 0, e2 := 1, c2 := 2, e3 := 1, c3 := 0 },
    { e1 := 2, c1 := 1, e2 := 1, c2 := 2, e3 := 1, c3 := 0 },
    { e1 := 1, c1 := 0, e2 := 1, c2 := 2, e3 := 1, c3 := 1 },
    { e1 := 1, c1 := 0, e2 := 1, c2 := 2, e3 := 1, c3 := 2 },
    { e1 := 2, c1 := 0, e2 := 1, c2 := 2, e3 := 2, c3 := 6 },
    { e1 := 3, c1 := 2, e2 := 3, c2 := 8, e3 := 2, c3 := 6 },
    { e1 := 3, c1 := 2, e2 := 3, c2 := 9, e3 := 2, c3 := 6 },
    { e1 := 3, c1 := 3, e2 := 2, c2 := 4, e3 := 2, c3 := 6 },
    { e1 := 2, c1 := 1, e2 := 2, c2 := 5, e3 := 2, c3 := 6 },
    { e1 := 1, c1 := 0, e2 := 1, c2 := 2, e3 := 2, c3 := 7 },
    { e1 := 2, c1 := 0, e2 := 2, c2 := 6, e3 := 1, c3 := 0 },
    { e1 := 2, c1 := 1, e2 := 2, c2 := 6, e3 := 1, c3 := 0 },
    { e1 := 1, c1 := 0, e2 := 2, c2 := 7, e3 := 1, c3 := 0 },
    { e1 := 1, c1 := 0, e2 := 2, c2 := 6, e3 := 1, c3 := 1 },
    { e1 := 1, c1 := 0, e2 := 2, c2 := 7, e3 := 1, c3 := 1 },
    { e1 := 2, c1 := 0, e2 := 2, c2 := 6, e3 := 1, c3 := 2 },
    { e1 := 3, c1 := 2, e2 := 3, c2 := 12, e3 := 3, c3 := 8 },
    { e1 := 4, c1 := 4, e2 := 3, c2 := 12, e3 := 3, c3 := 9 },
    { e1 := 4, c1 := 5, e2 := 4, c2 := 24, e3 := 3, c3 := 9 },
    { e1 := 4, c1 := 5, e2 := 4, c2 := 25, e3 := 4, c3 := 18 },
    { e1 := 4, c1 := 5, e2 := 4, c2 := 25, e3 := 4, c3 := 19 },
    { e1 := 3, c1 := 2, e2 := 3, c2 := 13, e3 := 2, c3 := 4 }]

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
  [{ e1 := 3, c1 := 3, e2 := 2, c2 := 6, e3 := 2, c3 := 4 },
    { e1 := 3, c1 := 2, e2 := 2, c2 := 6, e3 := 2, c3 := 5 },
    { e1 := 3, c1 := 3, e2 := 3, c2 := 12, e3 := 2, c3 := 5 },
    { e1 := 3, c1 := 3, e2 := 3, c2 := 13, e3 := 2, c3 := 5 },
    { e1 := 1, c1 := 0, e2 := 2, c2 := 7, e3 := 1, c3 := 2 },
    { e1 := 1, c1 := 0, e2 := 1, c2 := 3, e3 := 1, c3 := 3 },
    { e1 := 1, c1 := 1, e2 := 1, c2 := 0, e3 := 1, c3 := 0 },
    { e1 := 1, c1 := 1, e2 := 1, c2 := 0, e3 := 1, c3 := 1 },
    { e1 := 1, c1 := 1, e2 := 1, c2 := 0, e3 := 1, c3 := 2 },
    { e1 := 1, c1 := 1, e2 := 1, c2 := 0, e3 := 1, c3 := 3 },
    { e1 := 2, c1 := 2, e2 := 2, c2 := 2, e3 := 2, c3 := 0 },
    { e1 := 4, c1 := 8, e2 := 3, c2 := 4, e3 := 3, c3 := 2 },
    { e1 := 4, c1 := 9, e2 := 4, c2 := 8, e3 := 3, c3 := 2 },
    { e1 := 4, c1 := 9, e2 := 4, c2 := 9, e3 := 3, c3 := 2 },
    { e1 := 5, c1 := 16, e2 := 4, c2 := 8, e3 := 4, c3 := 6 },
    { e1 := 5, c1 := 17, e2 := 5, c2 := 16, e3 := 4, c3 := 6 },
    { e1 := 5, c1 := 17, e2 := 5, c2 := 17, e3 := 5, c3 := 12 },
    { e1 := 6, c1 := 34, e2 := 6, c2 := 34, e3 := 5, c3 := 13 },
    { e1 := 6, c1 := 34, e2 := 6, c2 := 35, e3 := 5, c3 := 13 },
    { e1 := 6, c1 := 35, e2 := 5, c2 := 17, e3 := 5, c3 := 13 },
    { e1 := 4, c1 := 8, e2 := 4, c2 := 8, e3 := 4, c3 := 7 },
    { e1 := 4, c1 := 8, e2 := 4, c2 := 9, e3 := 3, c3 := 3 },
    { e1 := 4, c1 := 9, e2 := 3, c2 := 4, e3 := 3, c3 := 3 },
    { e1 := 3, c1 := 4, e2 := 3, c2 := 5, e3 := 2, c3 := 1 },
    { e1 := 3, c1 := 5, e2 := 2, c2 := 2, e3 := 2, c3 := 1 },
    { e1 := 2, c1 := 2, e2 := 2, c2 := 3, e3 := 1, c3 := 0 },
    { e1 := 2, c1 := 3, e2 := 1, c2 := 1, e3 := 1, c3 := 0 },
    { e1 := 2, c1 := 2, e2 := 2, c2 := 2, e3 := 2, c3 := 2 },
    { e1 := 2, c1 := 2, e2 := 2, c2 := 2, e3 := 2, c3 := 3 },
    { e1 := 2, c1 := 2, e2 := 2, c2 := 3, e3 := 1, c3 := 1 },
    { e1 := 2, c1 := 3, e2 := 1, c2 := 1, e3 := 1, c3 := 1 },
    { e1 := 1, c1 := 1, e2 := 1, c2 := 1, e3 := 1, c3 := 2 },
    { e1 := 1, c1 := 1, e2 := 1, c2 := 1, e3 := 2, c3 := 6 },
    { e1 := 1, c1 := 1, e2 := 1, c2 := 1, e3 := 2, c3 := 7 },
    { e1 := 2, c1 := 2, e2 := 2, c2 := 4, e3 := 1, c3 := 0 },
    { e1 := 3, c1 := 4, e2 := 2, c2 := 5, e3 := 2, c3 := 0 },
    { e1 := 3, c1 := 5, e2 := 2, c2 := 5, e3 := 2, c3 := 0 },
    { e1 := 2, c1 := 2, e2 := 2, c2 := 5, e3 := 2, c3 := 1 },
    { e1 := 2, c1 := 3, e2 := 1, c2 := 2, e3 := 1, c3 := 0 },
    { e1 := 2, c1 := 2, e2 := 2, c2 := 4, e3 := 1, c3 := 1 }]

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
  [{ e1 := 2, c1 := 2, e2 := 2, c2 := 5, e3 := 2, c3 := 2 },
    { e1 := 3, c1 := 4, e2 := 3, c2 := 10, e3 := 2, c3 := 3 },
    { e1 := 3, c1 := 4, e2 := 3, c2 := 11, e3 := 3, c3 := 6 },
    { e1 := 3, c1 := 4, e2 := 3, c2 := 11, e3 := 3, c3 := 7 },
    { e1 := 3, c1 := 5, e2 := 2, c2 := 5, e3 := 2, c3 := 3 },
    { e1 := 2, c1 := 3, e2 := 1, c2 := 2, e3 := 1, c3 := 1 },
    { e1 := 1, c1 := 1, e2 := 1, c2 := 2, e3 := 1, c3 := 2 },
    { e1 := 1, c1 := 1, e2 := 1, c2 := 2, e3 := 1, c3 := 3 },
    { e1 := 4, c1 := 8, e2 := 4, c2 := 24, e3 := 3, c3 := 0 },
    { e1 := 4, c1 := 8, e2 := 4, c2 := 25, e3 := 3, c3 := 0 },
    { e1 := 4, c1 := 9, e2 := 4, c2 := 24, e3 := 3, c3 := 0 },
    { e1 := 5, c1 := 18, e2 := 4, c2 := 25, e3 := 4, c3 := 0 },
    { e1 := 5, c1 := 19, e2 := 4, c2 := 25, e3 := 4, c3 := 0 },
    { e1 := 4, c1 := 9, e2 := 4, c2 := 25, e3 := 4, c3 := 1 },
    { e1 := 3, c1 := 4, e2 := 3, c2 := 12, e3 := 3, c3 := 1 },
    { e1 := 3, c1 := 4, e2 := 3, c2 := 13, e3 := 2, c3 := 0 },
    { e1 := 3, c1 := 5, e2 := 3, c2 := 12, e3 := 2, c3 := 0 },
    { e1 := 3, c1 := 5, e2 := 3, c2 := 13, e3 := 2, c3 := 0 },
    { e1 := 2, c1 := 2, e2 := 2, c2 := 6, e3 := 2, c3 := 1 },
    { e1 := 3, c1 := 6, e2 := 3, c2 := 12, e3 := 3, c3 := 0 },
    { e1 := 3, c1 := 6, e2 := 3, c2 := 12, e3 := 3, c3 := 1 },
    { e1 := 3, c1 := 6, e2 := 3, c2 := 13, e3 := 2, c3 := 0 },
    { e1 := 4, c1 := 14, e2 := 4, c2 := 24, e3 := 4, c3 := 0 },
    { e1 := 5, c1 := 28, e2 := 4, c2 := 24, e3 := 4, c3 := 1 },
    { e1 := 5, c1 := 29, e2 := 4, c2 := 24, e3 := 4, c3 := 1 },
    { e1 := 4, c1 := 14, e2 := 4, c2 := 25, e3 := 3, c3 := 0 },
    { e1 := 4, c1 := 15, e2 := 3, c2 := 12, e3 := 3, c3 := 0 },
    { e1 := 3, c1 := 7, e2 := 3, c2 := 12, e3 := 3, c3 := 1 },
    { e1 := 3, c1 := 7, e2 := 3, c2 := 13, e3 := 2, c3 := 0 },
    { e1 := 2, c1 := 3, e2 := 2, c2 := 6, e3 := 2, c3 := 1 },
    { e1 := 1, c1 := 1, e2 := 2, c2 := 7, e3 := 1, c3 := 0 },
    { e1 := 1, c1 := 1, e2 := 1, c2 := 3, e3 := 1, c3 := 1 },
    { e1 := 1, c1 := 1, e2 := 1, c2 := 3, e3 := 1, c3 := 2 },
    { e1 := 1, c1 := 1, e2 := 2, c2 := 6, e3 := 2, c3 := 6 },
    { e1 := 1, c1 := 1, e2 := 2, c2 := 6, e3 := 2, c3 := 7 },
    { e1 := 1, c1 := 1, e2 := 2, c2 := 7, e3 := 1, c3 := 3 },
    { e1 := 1, c1 := 2, e2 := 1, c2 := 1, e3 := 1, c3 := 0 },
    { e1 := 1, c1 := 2, e2 := 1, c2 := 1, e3 := 1, c3 := 1 },
    { e1 := 1, c1 := 2, e2 := 1, c2 := 1, e3 := 1, c3 := 2 },
    { e1 := 1, c1 := 2, e2 := 1, c2 := 1, e3 := 1, c3 := 3 }]

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

/-- The boxes of the groups 120 to 159. -/
noncomputable def boxes_p3 : List Bx :=
  [{ e1 := 3, c1 := 8, e2 := 2, c2 := 4, e3 := 2, c3 := 0 },
    { e1 := 3, c1 := 9, e2 := 2, c2 := 4, e3 := 2, c3 := 0 },
    { e1 := 2, c1 := 4, e2 := 2, c2 := 4, e3 := 2, c3 := 1 },
    { e1 := 3, c1 := 8, e2 := 2, c2 := 5, e3 := 2, c3 := 0 },
    { e1 := 3, c1 := 9, e2 := 3, c2 := 10, e3 := 2, c3 := 0 },
    { e1 := 3, c1 := 9, e2 := 3, c2 := 11, e3 := 2, c3 := 0 },
    { e1 := 3, c1 := 8, e2 := 2, c2 := 5, e3 := 2, c3 := 1 },
    { e1 := 3, c1 := 9, e2 := 3, c2 := 10, e3 := 2, c3 := 1 },
    { e1 := 4, c1 := 18, e2 := 3, c2 := 11, e3 := 3, c3 := 2 },
    { e1 := 4, c1 := 19, e2 := 4, c2 := 22, e3 := 3, c3 := 2 },
    { e1 := 5, c1 := 38, e2 := 4, c2 := 23, e3 := 4, c3 := 4 },
    { e1 := 5, c1 := 39, e2 := 5, c2 := 46, e3 := 4, c3 := 4 },
    { e1 := 6, c1 := 78, e2 := 5, c2 := 47, e3 := 5, c3 := 8 },
    { e1 := 6, c1 := 79, e2 := 5, c2 := 47, e3 := 5, c3 := 8 },
    { e1 := 5, c1 := 39, e2 := 5, c2 := 47, e3 := 5, c3 := 9 },
    { e1 := 4, c1 := 19, e2 := 4, c2 := 23, e3 := 4, c3 := 5 },
    { e1 := 3, c1 := 9, e2 := 3, c2 := 11, e3 := 3, c3 := 3 },
    { e1 := 2, c1 := 5, e2 := 2, c2 := 4, e3 := 1, c3 := 0 },
    { e1 := 2, c1 := 5, e2 := 2, c2 := 5, e3 := 2, c3 := 0 },
    { e1 := 3, c1 := 10, e2 := 3, c2 := 10, e3 := 2, c3 := 1 },
    { e1 := 4, c1 := 20, e2 := 4, c2 := 22, e3 := 3, c3 := 2 },
    { e1 := 5, c1 := 40, e2 := 5, c2 := 46, e3 := 5, c3 := 8 },
    { e1 := 5, c1 := 40, e2 := 5, c2 := 46, e3 := 5, c3 := 9 },
    { e1 := 5, c1 := 40, e2 := 5, c2 := 47, e3 := 5, c3 := 8 },
    { e1 := 5, c1 := 40, e2 := 5, c2 := 47, e3 := 5, c3 := 9 },
    { e1 := 5, c1 := 41, e2 := 5, c2 := 46, e3 := 5, c3 := 8 },
    { e1 := 5, c1 := 41, e2 := 5, c2 := 46, e3 := 5, c3 := 9 },
    { e1 := 5, c1 := 41, e2 := 5, c2 := 47, e3 := 4, c3 := 4 },
    { e1 := 4, c1 := 20, e2 := 4, c2 := 23, e3 := 4, c3 := 5 },
    { e1 := 5, c1 := 42, e2 := 4, c2 := 22, e3 := 4, c3 := 4 },
    { e1 := 5, c1 := 43, e2 := 4, c2 := 22, e3 := 4, c3 := 4 },
    { e1 := 4, c1 := 21, e2 := 4, c2 := 22, e3 := 4, c3 := 5 },
    { e1 := 5, c1 := 42, e2 := 4, c2 := 23, e3 := 4, c3 := 4 },
    { e1 := 5, c1 := 43, e2 := 4, c2 := 23, e3 := 4, c3 := 4 },
    { e1 := 5, c1 := 42, e2 := 4, c2 := 23, e3 := 4, c3 := 5 },
    { e1 := 5, c1 := 43, e2 := 4, c2 := 23, e3 := 4, c3 := 5 },
    { e1 := 3, c1 := 10, e2 := 3, c2 := 11, e3 := 3, c3 := 3 },
    { e1 := 3, c1 := 11, e2 := 3, c2 := 10, e3 := 2, c3 := 1 },
    { e1 := 4, c1 := 22, e2 := 4, c2 := 22, e3 := 4, c3 := 4 },
    { e1 := 5, c1 := 44, e2 := 4, c2 := 22, e3 := 4, c3 := 5 }]

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
  allDone_cons g138_ok <|
  allDone_cons g139_ok <|
  allDone_cons g140_ok <|
  allDone_cons g141_ok <|
  allDone_cons g142_ok <|
  allDone_cons g143_ok <|
  allDone_cons g144_ok <|
  allDone_cons g145_ok <|
  allDone_cons g146_ok <|
  allDone_cons g147_ok <|
  allDone_cons g148_ok <|
  allDone_cons g149_ok <|
  allDone_cons g150_ok <|
  allDone_cons g151_ok <|
  allDone_cons g152_ok <|
  allDone_cons g153_ok <|
  allDone_cons g154_ok <|
  allDone_cons g155_ok <|
  allDone_cons g156_ok <|
  allDone_cons g157_ok <|
  allDone_cons g158_ok <|
  allDone_cons g159_ok <|
  allDone_nil run

/-- The boxes of the groups 160 to 199. -/
noncomputable def boxes_p4 : List Bx :=
  [{ e1 := 5, c1 := 45, e2 := 4, c2 := 22, e3 := 4, c3 := 5 },
    { e1 := 4, c1 := 22, e2 := 4, c2 := 23, e3 := 3, c3 := 2 },
    { e1 := 4, c1 := 23, e2 := 3, c2 := 11, e3 := 3, c3 := 2 },
    { e1 := 4, c1 := 22, e2 := 3, c2 := 11, e3 := 3, c3 := 3 },
    { e1 := 4, c1 := 23, e2 := 4, c2 := 22, e3 := 3, c3 := 3 },
    { e1 := 4, c1 := 23, e2 := 4, c2 := 23, e3 := 4, c3 := 6 },
    { e1 := 4, c1 := 23, e2 := 4, c2 := 23, e3 := 4, c3 := 7 },
    { e1 := 2, c1 := 4, e2 := 1, c2 := 2, e3 := 1, c3 := 1 },
    { e1 := 2, c1 := 5, e2 := 2, c2 := 4, e3 := 1, c3 := 1 },
    { e1 := 2, c1 := 5, e2 := 2, c2 := 5, e3 := 2, c3 := 2 },
    { e1 := 3, c1 := 10, e2 := 2, c2 := 5, e3 := 2, c3 := 3 },
    { e1 := 3, c1 := 11, e2 := 3, c2 := 10, e3 := 2, c3 := 3 },
    { e1 := 4, c1 := 22, e2 := 3, c2 := 11, e3 := 3, c3 := 6 },
    { e1 := 4, c1 := 23, e2 := 4, c2 := 22, e3 := 3, c3 := 6 },
    { e1 := 4, c1 := 23, e2 := 4, c2 := 23, e3 := 4, c3 := 12 },
    { e1 := 4, c1 := 23, e2 := 4, c2 := 23, e3 := 4, c3 := 13 },
    { e1 := 3, c1 := 11, e2 := 3, c2 := 11, e3 := 3, c3 := 7 },
    { e1 := 1, c1 := 2, e2 := 1, c2 := 2, e3 := 1, c3 := 2 },
    { e1 := 2, c1 := 4, e2 := 1, c2 := 2, e3 := 2, c3 := 6 },
    { e1 := 2, c1 := 5, e2 := 2, c2 := 4, e3 := 2, c3 := 6 },
    { e1 := 2, c1 := 5, e2 := 2, c2 := 5, e3 := 2, c3 := 6 },
    { e1 := 1, c1 := 2, e2 := 1, c2 := 2, e3 := 2, c3 := 7 },
    { e1 := 3, c1 := 8, e2 := 3, c2 := 12, e3 := 3, c3 := 0 },
    { e1 := 4, c1 := 16, e2 := 3, c2 := 12, e3 := 3, c3 := 1 },
    { e1 := 4, c1 := 17, e2 := 4, c2 := 24, e3 := 4, c3 := 2 },
    { e1 := 5, c1 := 34, e2 := 4, c2 := 24, e3 := 4, c3 := 3 },
    { e1 := 5, c1 := 35, e2 := 4, c2 := 24, e3 := 4, c3 := 3 },
    { e1 := 4, c1 := 17, e2 := 4, c2 := 25, e3 := 3, c3 := 1 },
    { e1 := 3, c1 := 8, e2 := 3, c2 := 13, e3 := 2, c3 := 0 },
    { e1 := 3, c1 := 9, e2 := 3, c2 := 12, e3 := 3, c3 := 0 },
    { e1 := 4, c1 := 18, e2 := 4, c2 := 24, e3 := 4, c3 := 2 },
    { e1 := 5, c1 := 36, e2 := 5, c2 := 48, e3 := 4, c3 := 3 },
    { e1 := 5, c1 := 36, e2 := 5, c2 := 49, e3 := 4, c3 := 3 },
    { e1 := 5, c1 := 37, e2 := 4, c2 := 24, e3 := 4, c3 := 3 },
    { e1 := 4, c1 := 18, e2 := 4, c2 := 25, e3 := 3, c3 := 1 },
    { e1 := 4, c1 := 19, e2 := 3, c2 := 12, e3 := 3, c3 := 1 },
    { e1 := 3, c1 := 9, e2 := 3, c2 := 13, e3 := 2, c3 := 0 },
    { e1 := 4, c1 := 16, e2 := 3, c2 := 12, e3 := 3, c3 := 2 },
    { e1 := 4, c1 := 17, e2 := 4, c2 := 24, e3 := 3, c3 := 2 },
    { e1 := 5, c1 := 34, e2 := 4, c2 := 25, e3 := 4, c3 := 4 }]

theorem done_p4 : AllDone run boxes_p4 :=
  allDone_cons g160_ok <|
  allDone_cons g161_ok <|
  allDone_cons g162_ok <|
  allDone_cons g163_ok <|
  allDone_cons g164_ok <|
  allDone_cons g165_ok <|
  allDone_cons g166_ok <|
  allDone_cons g167_ok <|
  allDone_cons g168_ok <|
  allDone_cons g169_ok <|
  allDone_cons g170_ok <|
  allDone_cons g171_ok <|
  allDone_cons g172_ok <|
  allDone_cons g173_ok <|
  allDone_cons g174_ok <|
  allDone_cons g175_ok <|
  allDone_cons g176_ok <|
  allDone_cons g177_ok <|
  allDone_cons g178_ok <|
  allDone_cons g179_ok <|
  allDone_cons g180_ok <|
  allDone_cons g181_ok <|
  allDone_cons g182_ok <|
  allDone_cons g183_ok <|
  allDone_cons g184_ok <|
  allDone_cons g185_ok <|
  allDone_cons g186_ok <|
  allDone_cons g187_ok <|
  allDone_cons g188_ok <|
  allDone_cons g189_ok <|
  allDone_cons g190_ok <|
  allDone_cons g191_ok <|
  allDone_cons g192_ok <|
  allDone_cons g193_ok <|
  allDone_cons g194_ok <|
  allDone_cons g195_ok <|
  allDone_cons g196_ok <|
  allDone_cons g197_ok <|
  allDone_cons g198_ok <|
  allDone_cons g199_ok <|
  allDone_nil run

/-- The boxes of the groups 200 to 239. -/
noncomputable def boxes_p5 : List Bx :=
  [{ e1 := 5, c1 := 35, e2 := 5, c2 := 50, e3 := 4, c3 := 4 },
    { e1 := 5, c1 := 35, e2 := 5, c2 := 51, e3 := 4, c3 := 4 },
    { e1 := 4, c1 := 17, e2 := 4, c2 := 25, e3 := 4, c3 := 5 },
    { e1 := 3, c1 := 8, e2 := 3, c2 := 12, e3 := 3, c3 := 3 },
    { e1 := 3, c1 := 8, e2 := 3, c2 := 13, e3 := 2, c3 := 1 },
    { e1 := 5, c1 := 36, e2 := 5, c2 := 48, e3 := 4, c3 := 4 },
    { e1 := 6, c1 := 72, e2 := 5, c2 := 49, e3 := 5, c3 := 8 },
    { e1 := 6, c1 := 73, e2 := 5, c2 := 49, e3 := 5, c3 := 8 },
    { e1 := 5, c1 := 36, e2 := 5, c2 := 49, e3 := 5, c3 := 9 },
    { e1 := 5, c1 := 37, e2 := 5, c2 := 48, e3 := 4, c3 := 4 },
    { e1 := 6, c1 := 74, e2 := 5, c2 := 49, e3 := 5, c3 := 8 },
    { e1 := 6, c1 := 75, e2 := 5, c2 := 49, e3 := 5, c3 := 8 },
    { e1 := 5, c1 := 37, e2 := 5, c2 := 49, e3 := 5, c3 := 9 },
    { e1 := 4, c1 := 18, e2 := 4, c2 := 24, e3 := 4, c3 := 5 },
    { e1 := 6, c1 := 72, e2 := 5, c2 := 50, e3 := 5, c3 := 8 },
    { e1 := 6, c1 := 73, e2 := 5, c2 := 50, e3 := 5, c3 := 8 },
    { e1 := 5, c1 := 36, e2 := 5, c2 := 50, e3 := 5, c3 := 9 },
    { e1 := 5, c1 := 36, e2 := 5, c2 := 51, e3 := 5, c3 := 8 },
    { e1 := 5, c1 := 36, e2 := 5, c2 := 51, e3 := 5, c3 := 9 },
    { e1 := 5, c1 := 37, e2 := 4, c2 := 25, e3 := 4, c3 := 4 },
    { e1 := 5, c1 := 36, e2 := 4, c2 := 25, e3 := 4, c3 := 5 },
    { e1 := 5, c1 := 37, e2 := 4, c2 := 25, e3 := 4, c3 := 5 },
    { e1 := 5, c1 := 38, e2 := 5, c2 := 48, e3 := 5, c3 := 8 },
    { e1 := 5, c1 := 38, e2 := 5, c2 := 48, e3 := 5, c3 := 9 },
    { e1 := 5, c1 := 38, e2 := 5, c2 := 49, e3 := 4, c3 := 4 },
    { e1 := 5, c1 := 39, e2 := 4, c2 := 24, e3 := 4, c3 := 4 },
    { e1 := 4, c1 := 19, e2 := 4, c2 := 24, e3 := 4, c3 := 5 },
    { e1 := 4, c1 := 19, e2 := 4, c2 := 25, e3 := 3, c3 := 2 },
    { e1 := 3, c1 := 9, e2 := 3, c2 := 12, e3 := 3, c3 := 3 },
    { e1 := 4, c1 := 18, e2 := 4, c2 := 26, e3 := 4, c3 := 4 },
    { e1 := 5, c1 := 36, e2 := 4, c2 := 26, e3 := 4, c3 := 5 },
    { e1 := 5, c1 := 37, e2 := 4, c2 := 26, e3 := 4, c3 := 5 },
    { e1 := 4, c1 := 18, e2 := 4, c2 := 27, e3 := 3, c3 := 2 },
    { e1 := 4, c1 := 19, e2 := 3, c2 := 13, e3 := 3, c3 := 2 },
    { e1 := 3, c1 := 9, e2 := 3, c2 := 13, e3 := 3, c3 := 3 },
    { e1 := 2, c1 := 5, e2 := 2, c2 := 6, e3 := 2, c3 := 0 },
    { e1 := 4, c1 := 20, e2 := 3, c2 := 12, e3 := 3, c3 := 2 },
    { e1 := 4, c1 := 21, e2 := 3, c2 := 12, e3 := 3, c3 := 2 },
    { e1 := 3, c1 := 10, e2 := 3, c2 := 12, e3 := 3, c3 := 3 },
    { e1 := 3, c1 := 10, e2 := 3, c2 := 13, e3 := 2, c3 := 1 }]

theorem done_p5 : AllDone run boxes_p5 :=
  allDone_cons g200_ok <|
  allDone_cons g201_ok <|
  allDone_cons g202_ok <|
  allDone_cons g203_ok <|
  allDone_cons g204_ok <|
  allDone_cons g205_ok <|
  allDone_cons g206_ok <|
  allDone_cons g207_ok <|
  allDone_cons g208_ok <|
  allDone_cons g209_ok <|
  allDone_cons g210_ok <|
  allDone_cons g211_ok <|
  allDone_cons g212_ok <|
  allDone_cons g213_ok <|
  allDone_cons g214_ok <|
  allDone_cons g215_ok <|
  allDone_cons g216_ok <|
  allDone_cons g217_ok <|
  allDone_cons g218_ok <|
  allDone_cons g219_ok <|
  allDone_cons g220_ok <|
  allDone_cons g221_ok <|
  allDone_cons g222_ok <|
  allDone_cons g223_ok <|
  allDone_cons g224_ok <|
  allDone_cons g225_ok <|
  allDone_cons g226_ok <|
  allDone_cons g227_ok <|
  allDone_cons g228_ok <|
  allDone_cons g229_ok <|
  allDone_cons g230_ok <|
  allDone_cons g231_ok <|
  allDone_cons g232_ok <|
  allDone_cons g233_ok <|
  allDone_cons g234_ok <|
  allDone_cons g235_ok <|
  allDone_cons g236_ok <|
  allDone_cons g237_ok <|
  allDone_cons g238_ok <|
  allDone_cons g239_ok <|
  allDone_nil run

/-- The boxes of the groups 240 to 259. -/
noncomputable def boxes_p6 : List Bx :=
  [{ e1 := 3, c1 := 11, e2 := 2, c2 := 6, e3 := 2, c3 := 1 },
    { e1 := 1, c1 := 2, e2 := 2, c2 := 7, e3 := 1, c3 := 0 },
    { e1 := 1, c1 := 2, e2 := 2, c2 := 6, e3 := 1, c3 := 1 },
    { e1 := 1, c1 := 2, e2 := 2, c2 := 7, e3 := 1, c3 := 1 },
    { e1 := 1, c1 := 2, e2 := 1, c2 := 3, e3 := 1, c3 := 2 },
    { e1 := 1, c1 := 2, e2 := 2, c2 := 6, e3 := 2, c3 := 6 },
    { e1 := 1, c1 := 2, e2 := 2, c2 := 6, e3 := 2, c3 := 7 },
    { e1 := 1, c1 := 2, e2 := 2, c2 := 7, e3 := 1, c3 := 3 },
    { e1 := 1, c1 := 3, e2 := 1, c2 := 2, e3 := 1, c3 := 0 },
    { e1 := 1, c1 := 3, e2 := 1, c2 := 2, e3 := 1, c3 := 1 },
    { e1 := 1, c1 := 3, e2 := 1, c2 := 2, e3 := 1, c3 := 2 },
    { e1 := 1, c1 := 3, e2 := 1, c2 := 2, e3 := 1, c3 := 3 },
    { e1 := 1, c1 := 3, e2 := 1, c2 := 3, e3 := 1, c3 := 0 },
    { e1 := 2, c1 := 6, e2 := 1, c2 := 3, e3 := 1, c3 := 1 },
    { e1 := 2, c1 := 7, e2 := 1, c2 := 3, e3 := 1, c3 := 1 },
    { e1 := 2, c1 := 6, e2 := 1, c2 := 3, e3 := 1, c3 := 2 },
    { e1 := 2, c1 := 7, e2 := 1, c2 := 3, e3 := 1, c3 := 2 },
    { e1 := 2, c1 := 6, e2 := 1, c2 := 3, e3 := 1, c3 := 3 },
    { e1 := 2, c1 := 7, e2 := 2, c2 := 6, e3 := 1, c3 := 3 },
    { e1 := 2, c1 := 7, e2 := 2, c2 := 7, e3 := 1, c3 := 3 }]

theorem done_p6 : AllDone run boxes_p6 :=
  allDone_cons g240_ok <|
  allDone_cons g241_ok <|
  allDone_cons g242_ok <|
  allDone_cons g243_ok <|
  allDone_cons g244_ok <|
  allDone_cons g245_ok <|
  allDone_cons g246_ok <|
  allDone_cons g247_ok <|
  allDone_cons g248_ok <|
  allDone_cons g249_ok <|
  allDone_cons g250_ok <|
  allDone_cons g251_ok <|
  allDone_cons g252_ok <|
  allDone_cons g253_ok <|
  allDone_cons g254_ok <|
  allDone_cons g255_ok <|
  allDone_cons g256_ok <|
  allDone_cons g257_ok <|
  allDone_cons g258_ok <|
  allDone_cons g259_ok <|
  allDone_nil run

noncomputable def boxes_q0_0 : List Bx :=
  boxes_p0 ++ (boxes_p1 ++ (boxes_p2 ++ (boxes_p3 ++ (boxes_p4 ++ (boxes_p5 ++ (boxes_p6))))))

theorem done_q0_0 : AllDone run boxes_q0_0 :=
  allDone_append done_p0 <| allDone_append done_p1 <| allDone_append done_p2 <| allDone_append done_p3 <| allDone_append done_p4 <| allDone_append done_p5 <| done_p6

/-- **The master tree**: the boxes of the groups, and boxes on which a cut fails, are the leaves of
trees of bisections of the boxes of the grid of the level 1. -/
theorem master_ok : masterOk run 1 (hex% "f73cf3fffffffe7f7ffc93bff392fffe49f3fbf24bfcb7f2d249ffdcb724fff4e4e7fce73921fdcbfedcb73b73edcff392dfcf2fc9ff9fbe4b4b4edffcb72dcb73dcbf24fffffe7ffffce49fe4bf7ff2df4921fffb4ed3fcb4fbff93ffffd3b724f724e4ffff73fedce4b1f7f1ffd1cbfcfbff273ffdcb73") boxes_q0_0 = true := by
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

/-- info: 'N14Cert.CapPrr.slack_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms slack_nonneg

end N14Cert.CapPrr
