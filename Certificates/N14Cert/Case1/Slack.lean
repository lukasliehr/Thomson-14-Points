module

public import N14.Box.Master
public import N14Cert.Case1.Tables0
public import N14Cert.Case1.Tables1
public import N14Cert.Case1.Cells0
public import N14Cert.Case1.Cells1
public import N14Cert.Case1.Cells2
public import N14Cert.Case1.Cells3
public import N14Cert.Case1.Cells4
public import N14Cert.Case1.Cells5
public import N14Cert.Case1.Cells6
public import N14Cert.Case1.Cells7
public import N14Cert.Case1.Cells8
public import N14Cert.Case1.Cells9
public import N14Cert.Case1.Cells10
public import N14Cert.Case1.Cells11
public import N14Cert.Case1.Cells12
public import N14Cert.Case1.Cells13
public import N14Cert.Case1.Cells14
public import N14Cert.Case1.Cells15
public import N14Cert.Case1.Cells16
public import N14Cert.Case1.Cells17
public import N14Cert.Case1.Cells18
public import N14Cert.Case1.Cells19
public import N14Cert.Case1.Cells20
public import N14Cert.Case1.Cells21
public import N14Cert.Case1.Cells22
public import N14Cert.Case1.Cells23
public import N14Cert.Case1.Cells24
public import N14Cert.Case1.Cells25
public import N14Cert.Case1.Cells26
public import N14Cert.Case1.Cells27
public import N14Cert.Case1.Cells28
public import N14Cert.Case1.Cells29
public import N14Cert.Case1.Cells30
public import N14Cert.Case1.Cells31
public import N14Cert.Case1.Cells32
public import N14Cert.Case1.Cells33
public import N14Cert.Case1.Cells34
public import N14Cert.Case1.Cells35
public import N14Cert.Case1.Cells36
public import N14Cert.Case1.Cells37
public import N14Cert.Case1.Cells38
public import N14Cert.Case1.Cells39
public import N14Cert.Case1.Cells40
public import N14Cert.Case1.Cells41
public import N14Cert.Case1.Cells42
public import N14Cert.Case1.Cells43
public import N14Cert.Case1.Cells44
public import N14Cert.Case1.Cells45
public import N14Cert.Case1.Cells46
public import N14Cert.Case1.Cells47
public import N14Cert.Case1.Cells48
public import N14Cert.Case1.Cells49
public import N14Cert.Case1.Cells50
public import N14Cert.Case1.Cells51
public import N14Cert.Case1.Cells52
public import N14Cert.Case1.Cells53
public import N14Cert.Case1.Cells54
public import N14Cert.Case1.Cells55
public import N14Cert.Case1.Cells56
import CAP.Transport.Hex

@[expose] public section

namespace N14Cert.Case1

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
    { e1 := 2, c1 := 1, e2 := 2, c2 := 1, e3 := 2, c3 := 3 },
    { e1 := 2, c1 := 0, e2 := 2, c2 := 0, e3 := 1, c3 := 2 },
    { e1 := 2, c1 := 0, e2 := 2, c2 := 1, e3 := 2, c3 := 4 },
    { e1 := 3, c1 := 0, e2 := 3, c2 := 2, e3 := 2, c3 := 5 },
    { e1 := 3, c1 := 0, e2 := 3, c2 := 3, e3 := 3, c3 := 10 },
    { e1 := 4, c1 := 0, e2 := 4, c2 := 6, e3 := 3, c3 := 11 },
    { e1 := 4, c1 := 0, e2 := 4, c2 := 7, e3 := 3, c3 := 11 },
    { e1 := 4, c1 := 1, e2 := 3, c2 := 3, e3 := 3, c3 := 11 },
    { e1 := 3, c1 := 1, e2 := 2, c2 := 1, e3 := 2, c3 := 5 },
    { e1 := 2, c1 := 1, e2 := 1, c2 := 0, e3 := 1, c3 := 2 },
    { e1 := 4, c1 := 0, e2 := 3, c2 := 0, e3 := 3, c3 := 12 },
    { e1 := 4, c1 := 1, e2 := 4, c2 := 0, e3 := 3, c3 := 12 },
    { e1 := 4, c1 := 1, e2 := 4, c2 := 1, e3 := 3, c3 := 12 },
    { e1 := 3, c1 := 0, e2 := 3, c2 := 0, e3 := 3, c3 := 13 },
    { e1 := 4, c1 := 0, e2 := 4, c2 := 2, e3 := 3, c3 := 12 },
    { e1 := 4, c1 := 0, e2 := 4, c2 := 3, e3 := 4, c3 := 24 },
    { e1 := 5, c1 := 0, e2 := 5, c2 := 6, e3 := 4, c3 := 25 },
    { e1 := 5, c1 := 0, e2 := 5, c2 := 7, e3 := 4, c3 := 25 },
    { e1 := 5, c1 := 1, e2 := 4, c2 := 3, e3 := 4, c3 := 25 },
    { e1 := 4, c1 := 1, e2 := 3, c2 := 1, e3 := 3, c3 := 12 },
    { e1 := 4, c1 := 0, e2 := 4, c2 := 2, e3 := 4, c3 := 26 },
    { e1 := 4, c1 := 0, e2 := 4, c2 := 2, e3 := 4, c3 := 27 },
    { e1 := 4, c1 := 0, e2 := 4, c2 := 3, e3 := 4, c3 := 26 },
    { e1 := 4, c1 := 0, e2 := 4, c2 := 3, e3 := 4, c3 := 27 },
    { e1 := 4, c1 := 1, e2 := 3, c2 := 1, e3 := 3, c3 := 13 },
    { e1 := 3, c1 := 1, e2 := 3, c2 := 0, e3 := 2, c3 := 6 },
    { e1 := 3, c1 := 1, e2 := 3, c2 := 1, e3 := 2, c3 := 6 },
    { e1 := 4, c1 := 0, e2 := 4, c2 := 4, e3 := 4, c3 := 24 },
    { e1 := 6, c1 := 1, e2 := 6, c2 := 16, e3 := 5, c3 := 50 },
    { e1 := 6, c1 := 1, e2 := 6, c2 := 17, e3 := 5, c3 := 50 },
    { e1 := 5, c1 := 0, e2 := 5, c2 := 8, e3 := 5, c3 := 51 },
    { e1 := 5, c1 := 0, e2 := 5, c2 := 9, e3 := 4, c3 := 25 },
    { e1 := 5, c1 := 1, e2 := 4, c2 := 4, e3 := 4, c3 := 25 }]

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
  [{ e1 := 4, c1 := 0, e2 := 4, c2 := 5, e3 := 3, c3 := 12 },
    { e1 := 4, c1 := 1, e2 := 3, c2 := 2, e3 := 3, c3 := 12 },
    { e1 := 3, c1 := 0, e2 := 3, c2 := 2, e3 := 3, c3 := 13 },
    { e1 := 3, c1 := 0, e2 := 3, c2 := 3, e3 := 2, c3 := 6 },
    { e1 := 3, c1 := 1, e2 := 2, c2 := 1, e3 := 2, c3 := 6 },
    { e1 := 2, c1 := 1, e2 := 1, c2 := 0, e3 := 2, c3 := 6 },
    { e1 := 1, c1 := 0, e2 := 1, c2 := 0, e3 := 3, c3 := 14 },
    { e1 := 1, c1 := 0, e2 := 1, c2 := 0, e3 := 4, c3 := 30 },
    { e1 := 1, c1 := 0, e2 := 1, c2 := 0, e3 := 5, c3 := 62 },
    { e1 := 1, c1 := 0, e2 := 1, c2 := 0, e3 := 5, c3 := 63 },
    { e1 := 1, c1 := 0, e2 := 1, c2 := 1, e3 := 1, c3 := 0 },
    { e1 := 3, c1 := 0, e2 := 2, c2 := 2, e3 := 2, c3 := 2 },
    { e1 := 3, c1 := 1, e2 := 3, c2 := 4, e3 := 3, c3 := 4 },
    { e1 := 4, c1 := 2, e2 := 3, c2 := 4, e3 := 3, c3 := 5 },
    { e1 := 4, c1 := 3, e2 := 4, c2 := 8, e3 := 3, c3 := 5 },
    { e1 := 4, c1 := 3, e2 := 4, c2 := 9, e3 := 4, c3 := 10 },
    { e1 := 4, c1 := 3, e2 := 4, c2 := 9, e3 := 4, c3 := 11 },
    { e1 := 3, c1 := 1, e2 := 3, c2 := 5, e3 := 3, c3 := 4 },
    { e1 := 4, c1 := 2, e2 := 3, c2 := 5, e3 := 3, c3 := 5 },
    { e1 := 4, c1 := 3, e2 := 4, c2 := 10, e3 := 4, c3 := 10 },
    { e1 := 4, c1 := 3, e2 := 4, c2 := 10, e3 := 4, c3 := 11 },
    { e1 := 4, c1 := 3, e2 := 4, c2 := 11, e3 := 3, c3 := 5 },
    { e1 := 3, c1 := 0, e2 := 3, c2 := 4, e3 := 2, c3 := 3 },
    { e1 := 4, c1 := 0, e2 := 3, c2 := 5, e3 := 3, c3 := 6 },
    { e1 := 4, c1 := 1, e2 := 4, c2 := 10, e3 := 3, c3 := 6 },
    { e1 := 4, c1 := 1, e2 := 4, c2 := 11, e3 := 4, c3 := 12 },
    { e1 := 4, c1 := 1, e2 := 4, c2 := 11, e3 := 4, c3 := 13 },
    { e1 := 3, c1 := 0, e2 := 3, c2 := 5, e3 := 3, c3 := 7 },
    { e1 := 3, c1 := 1, e2 := 3, c2 := 4, e3 := 2, c3 := 3 },
    { e1 := 3, c1 := 1, e2 := 3, c2 := 5, e3 := 2, c3 := 3 },
    { e1 := 2, c1 := 0, e2 := 2, c2 := 3, e3 := 2, c3 := 2 },
    { e1 := 3, c1 := 0, e2 := 3, c2 := 6, e3 := 3, c3 := 6 },
    { e1 := 3, c1 := 0, e2 := 3, c2 := 6, e3 := 3, c3 := 7 },
    { e1 := 3, c1 := 0, e2 := 3, c2 := 7, e3 := 2, c3 := 3 },
    { e1 := 3, c1 := 1, e2 := 2, c2 := 3, e3 := 2, c3 := 3 },
    { e1 := 3, c1 := 2, e2 := 3, c2 := 4, e3 := 3, c3 := 4 },
    { e1 := 4, c1 := 4, e2 := 4, c2 := 8, e3 := 3, c3 := 5 },
    { e1 := 4, c1 := 4, e2 := 4, c2 := 9, e3 := 4, c3 := 10 },
    { e1 := 4, c1 := 4, e2 := 4, c2 := 9, e3 := 4, c3 := 11 },
    { e1 := 4, c1 := 5, e2 := 3, c2 := 4, e3 := 3, c3 := 5 }]

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
  [{ e1 := 3, c1 := 2, e2 := 3, c2 := 5, e3 := 2, c3 := 2 },
    { e1 := 3, c1 := 3, e2 := 3, c2 := 4, e3 := 3, c3 := 4 },
    { e1 := 3, c1 := 3, e2 := 3, c2 := 4, e3 := 3, c3 := 5 },
    { e1 := 3, c1 := 3, e2 := 3, c2 := 5, e3 := 2, c3 := 2 },
    { e1 := 2, c1 := 1, e2 := 2, c2 := 2, e3 := 2, c3 := 3 },
    { e1 := 2, c1 := 1, e2 := 2, c2 := 3, e3 := 1, c3 := 1 },
    { e1 := 3, c1 := 0, e2 := 3, c2 := 4, e3 := 2, c3 := 4 },
    { e1 := 4, c1 := 0, e2 := 4, c2 := 10, e3 := 3, c3 := 8 },
    { e1 := 4, c1 := 0, e2 := 4, c2 := 11, e3 := 4, c3 := 16 },
    { e1 := 4, c1 := 0, e2 := 4, c2 := 11, e3 := 4, c3 := 17 },
    { e1 := 4, c1 := 1, e2 := 3, c2 := 5, e3 := 3, c3 := 8 },
    { e1 := 4, c1 := 0, e2 := 4, c2 := 10, e3 := 3, c3 := 9 },
    { e1 := 4, c1 := 0, e2 := 4, c2 := 11, e3 := 3, c3 := 9 },
    { e1 := 4, c1 := 1, e2 := 3, c2 := 5, e3 := 3, c3 := 9 },
    { e1 := 3, c1 := 1, e2 := 2, c2 := 2, e3 := 2, c3 := 4 },
    { e1 := 4, c1 := 0, e2 := 4, c2 := 8, e3 := 3, c3 := 10 },
    { e1 := 4, c1 := 0, e2 := 4, c2 := 9, e3 := 3, c3 := 10 },
    { e1 := 4, c1 := 1, e2 := 3, c2 := 4, e3 := 3, c3 := 10 },
    { e1 := 4, c1 := 0, e2 := 4, c2 := 8, e3 := 3, c3 := 11 },
    { e1 := 4, c1 := 0, e2 := 4, c2 := 9, e3 := 3, c3 := 11 },
    { e1 := 4, c1 := 1, e2 := 3, c2 := 4, e3 := 3, c3 := 11 },
    { e1 := 3, c1 := 0, e2 := 3, c2 := 5, e3 := 2, c3 := 5 },
    { e1 := 3, c1 := 1, e2 := 2, c2 := 2, e3 := 2, c3 := 5 },
    { e1 := 3, c1 := 0, e2 := 3, c2 := 6, e3 := 3, c3 := 8 },
    { e1 := 3, c1 := 0, e2 := 3, c2 := 6, e3 := 3, c3 := 9 },
    { e1 := 3, c1 := 0, e2 := 3, c2 := 7, e3 := 2, c3 := 4 },
    { e1 := 3, c1 := 1, e2 := 2, c2 := 3, e3 := 2, c3 := 4 },
    { e1 := 3, c1 := 0, e2 := 3, c2 := 6, e3 := 3, c3 := 10 },
    { e1 := 4, c1 := 0, e2 := 4, c2 := 12, e3 := 3, c3 := 11 },
    { e1 := 4, c1 := 0, e2 := 4, c2 := 13, e3 := 3, c3 := 11 },
    { e1 := 4, c1 := 1, e2 := 3, c2 := 6, e3 := 3, c3 := 11 },
    { e1 := 3, c1 := 0, e2 := 3, c2 := 7, e3 := 3, c3 := 10 },
    { e1 := 4, c1 := 0, e2 := 3, c2 := 7, e3 := 3, c3 := 11 },
    { e1 := 4, c1 := 1, e2 := 4, c2 := 14, e3 := 4, c3 := 22 },
    { e1 := 4, c1 := 1, e2 := 4, c2 := 14, e3 := 4, c3 := 23 },
    { e1 := 4, c1 := 1, e2 := 4, c2 := 15, e3 := 4, c3 := 22 },
    { e1 := 5, c1 := 2, e2 := 4, c2 := 15, e3 := 4, c3 := 23 },
    { e1 := 5, c1 := 3, e2 := 5, c2 := 30, e3 := 4, c3 := 23 },
    { e1 := 5, c1 := 3, e2 := 5, c2 := 31, e3 := 4, c3 := 23 },
    { e1 := 3, c1 := 1, e2 := 2, c2 := 3, e3 := 2, c3 := 5 }]

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
  [{ e1 := 2, c1 := 1, e2 := 1, c2 := 1, e3 := 1, c3 := 2 },
    { e1 := 4, c1 := 0, e2 := 4, c2 := 8, e3 := 3, c3 := 12 },
    { e1 := 4, c1 := 0, e2 := 4, c2 := 9, e3 := 3, c3 := 12 },
    { e1 := 4, c1 := 1, e2 := 3, c2 := 4, e3 := 3, c3 := 12 },
    { e1 := 3, c1 := 0, e2 := 3, c2 := 4, e3 := 3, c3 := 13 },
    { e1 := 4, c1 := 0, e2 := 3, c2 := 5, e3 := 3, c3 := 12 },
    { e1 := 4, c1 := 1, e2 := 3, c2 := 5, e3 := 3, c3 := 12 },
    { e1 := 3, c1 := 0, e2 := 3, c2 := 5, e3 := 3, c3 := 13 },
    { e1 := 3, c1 := 1, e2 := 2, c2 := 2, e3 := 2, c3 := 6 },
    { e1 := 3, c1 := 0, e2 := 3, c2 := 6, e3 := 2, c3 := 6 },
    { e1 := 3, c1 := 0, e2 := 3, c2 := 7, e3 := 2, c3 := 6 },
    { e1 := 3, c1 := 1, e2 := 3, c2 := 6, e3 := 2, c3 := 6 },
    { e1 := 4, c1 := 2, e2 := 4, c2 := 14, e3 := 3, c3 := 12 },
    { e1 := 4, c1 := 2, e2 := 4, c2 := 15, e3 := 4, c3 := 24 },
    { e1 := 4, c1 := 2, e2 := 4, c2 := 15, e3 := 4, c3 := 25 },
    { e1 := 4, c1 := 3, e2 := 3, c2 := 7, e3 := 3, c3 := 12 },
    { e1 := 3, c1 := 1, e2 := 3, c2 := 7, e3 := 3, c3 := 13 },
    { e1 := 2, c1 := 1, e2 := 1, c2 := 1, e3 := 2, c3 := 6 },
    { e1 := 1, c1 := 0, e2 := 1, c2 := 1, e3 := 3, c3 := 14 },
    { e1 := 1, c1 := 0, e2 := 1, c2 := 1, e3 := 3, c3 := 15 },
    { e1 := 1, c1 := 0, e2 := 1, c2 := 2, e3 := 1, c3 := 1 },
    { e1 := 2, c1 := 0, e2 := 2, c2 := 4, e3 := 2, c3 := 4 },
    { e1 := 3, c1 := 0, e2 := 3, c2 := 8, e3 := 3, c3 := 10 },
    { e1 := 4, c1 := 0, e2 := 3, c2 := 8, e3 := 3, c3 := 11 },
    { e1 := 5, c1 := 2, e2 := 4, c2 := 16, e3 := 4, c3 := 22 },
    { e1 := 5, c1 := 3, e2 := 5, c2 := 32, e3 := 4, c3 := 22 },
    { e1 := 5, c1 := 3, e2 := 5, c2 := 33, e3 := 4, c3 := 22 },
    { e1 := 5, c1 := 2, e2 := 4, c2 := 16, e3 := 4, c3 := 23 },
    { e1 := 6, c1 := 6, e2 := 5, c2 := 32, e3 := 5, c3 := 46 },
    { e1 := 6, c1 := 7, e2 := 5, c2 := 32, e3 := 5, c3 := 46 },
    { e1 := 5, c1 := 3, e2 := 5, c2 := 32, e3 := 5, c3 := 47 },
    { e1 := 5, c1 := 3, e2 := 5, c2 := 33, e3 := 4, c3 := 23 },
    { e1 := 4, c1 := 1, e2 := 4, c2 := 17, e3 := 3, c3 := 11 },
    { e1 := 3, c1 := 0, e2 := 3, c2 := 9, e3 := 3, c3 := 10 },
    { e1 := 3, c1 := 0, e2 := 3, c2 := 9, e3 := 3, c3 := 11 },
    { e1 := 3, c1 := 1, e2 := 3, c2 := 8, e3 := 3, c3 := 10 },
    { e1 := 4, c1 := 2, e2 := 4, c2 := 16, e3 := 4, c3 := 22 },
    { e1 := 5, c1 := 4, e2 := 5, c2 := 32, e3 := 5, c3 := 46 },
    { e1 := 6, c1 := 8, e2 := 5, c2 := 32, e3 := 5, c3 := 47 },
    { e1 := 6, c1 := 9, e2 := 5, c2 := 32, e3 := 5, c3 := 47 }]

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
  [{ e1 := 5, c1 := 4, e2 := 5, c2 := 33, e3 := 5, c3 := 46 },
    { e1 := 5, c1 := 4, e2 := 5, c2 := 33, e3 := 5, c3 := 47 },
    { e1 := 5, c1 := 5, e2 := 4, c2 := 16, e3 := 4, c3 := 23 },
    { e1 := 4, c1 := 2, e2 := 4, c2 := 17, e3 := 4, c3 := 22 },
    { e1 := 4, c1 := 2, e2 := 4, c2 := 17, e3 := 4, c3 := 23 },
    { e1 := 4, c1 := 3, e2 := 3, c2 := 8, e3 := 3, c3 := 11 },
    { e1 := 4, c1 := 2, e2 := 4, c2 := 18, e3 := 3, c3 := 10 },
    { e1 := 4, c1 := 2, e2 := 4, c2 := 19, e3 := 3, c3 := 10 },
    { e1 := 4, c1 := 3, e2 := 3, c2 := 9, e3 := 3, c3 := 10 },
    { e1 := 4, c1 := 2, e2 := 4, c2 := 18, e3 := 3, c3 := 11 },
    { e1 := 4, c1 := 2, e2 := 4, c2 := 19, e3 := 3, c3 := 11 },
    { e1 := 4, c1 := 3, e2 := 4, c2 := 18, e3 := 3, c3 := 11 },
    { e1 := 4, c1 := 3, e2 := 4, c2 := 19, e3 := 4, c3 := 22 },
    { e1 := 5, c1 := 6, e2 := 4, c2 := 19, e3 := 4, c3 := 23 },
    { e1 := 5, c1 := 7, e2 := 5, c2 := 38, e3 := 4, c3 := 23 },
    { e1 := 5, c1 := 7, e2 := 5, c2 := 39, e3 := 4, c3 := 23 },
    { e1 := 2, c1 := 0, e2 := 2, c2 := 5, e3 := 2, c3 := 4 },
    { e1 := 3, c1 := 0, e2 := 2, c2 := 5, e3 := 2, c3 := 5 },
    { e1 := 4, c1 := 2, e2 := 4, c2 := 20, e3 := 3, c3 := 10 },
    { e1 := 4, c1 := 2, e2 := 4, c2 := 21, e3 := 3, c3 := 10 },
    { e1 := 4, c1 := 3, e2 := 4, c2 := 20, e3 := 3, c3 := 10 },
    { e1 := 4, c1 := 3, e2 := 4, c2 := 21, e3 := 4, c3 := 20 },
    { e1 := 4, c1 := 3, e2 := 4, c2 := 21, e3 := 4, c3 := 21 },
    { e1 := 4, c1 := 2, e2 := 3, c2 := 10, e3 := 3, c3 := 11 },
    { e1 := 5, c1 := 6, e2 := 4, c2 := 20, e3 := 4, c3 := 22 },
    { e1 := 5, c1 := 7, e2 := 4, c2 := 20, e3 := 4, c3 := 22 },
    { e1 := 4, c1 := 3, e2 := 4, c2 := 20, e3 := 4, c3 := 23 },
    { e1 := 4, c1 := 3, e2 := 4, c2 := 21, e3 := 3, c3 := 11 },
    { e1 := 3, c1 := 1, e2 := 3, c2 := 11, e3 := 2, c3 := 5 },
    { e1 := 2, c1 := 1, e2 := 2, c2 := 4, e3 := 2, c3 := 4 },
    { e1 := 3, c1 := 2, e2 := 3, c2 := 8, e3 := 2, c3 := 5 },
    { e1 := 3, c1 := 2, e2 := 3, c2 := 9, e3 := 3, c3 := 10 },
    { e1 := 4, c1 := 4, e2 := 4, c2 := 18, e3 := 3, c3 := 11 },
    { e1 := 4, c1 := 4, e2 := 4, c2 := 19, e3 := 4, c3 := 22 },
    { e1 := 5, c1 := 8, e2 := 5, c2 := 38, e3 := 4, c3 := 23 },
    { e1 := 5, c1 := 8, e2 := 5, c2 := 39, e3 := 5, c3 := 46 },
    { e1 := 6, c1 := 16, e2 := 5, c2 := 39, e3 := 5, c3 := 47 },
    { e1 := 6, c1 := 17, e2 := 6, c2 := 78, e3 := 5, c3 := 47 },
    { e1 := 6, c1 := 17, e2 := 6, c2 := 79, e3 := 5, c3 := 47 },
    { e1 := 5, c1 := 9, e2 := 4, c2 := 19, e3 := 4, c3 := 23 }]

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
  [{ e1 := 4, c1 := 5, e2 := 3, c2 := 9, e3 := 3, c3 := 11 },
    { e1 := 3, c1 := 3, e2 := 2, c2 := 4, e3 := 2, c3 := 5 },
    { e1 := 2, c1 := 1, e2 := 2, c2 := 5, e3 := 2, c3 := 4 },
    { e1 := 3, c1 := 2, e2 := 3, c2 := 10, e3 := 3, c3 := 10 },
    { e1 := 4, c1 := 4, e2 := 4, c2 := 20, e3 := 4, c3 := 22 },
    { e1 := 5, c1 := 8, e2 := 5, c2 := 40, e3 := 5, c3 := 46 },
    { e1 := 6, c1 := 16, e2 := 5, c2 := 40, e3 := 5, c3 := 47 },
    { e1 := 6, c1 := 17, e2 := 6, c2 := 80, e3 := 5, c3 := 47 },
    { e1 := 6, c1 := 17, e2 := 6, c2 := 81, e3 := 5, c3 := 47 },
    { e1 := 5, c1 := 8, e2 := 5, c2 := 41, e3 := 4, c3 := 23 },
    { e1 := 5, c1 := 9, e2 := 5, c2 := 40, e3 := 5, c3 := 46 },
    { e1 := 6, c1 := 18, e2 := 6, c2 := 80, e3 := 5, c3 := 47 },
    { e1 := 6, c1 := 18, e2 := 6, c2 := 81, e3 := 5, c3 := 47 },
    { e1 := 6, c1 := 19, e2 := 5, c2 := 40, e3 := 5, c3 := 47 },
    { e1 := 6, c1 := 18, e2 := 5, c2 := 41, e3 := 5, c3 := 46 },
    { e1 := 6, c1 := 19, e2 := 5, c2 := 41, e3 := 5, c3 := 46 },
    { e1 := 6, c1 := 18, e2 := 5, c2 := 41, e3 := 5, c3 := 47 },
    { e1 := 6, c1 := 19, e2 := 6, c2 := 82, e3 := 6, c3 := 94 },
    { e1 := 6, c1 := 19, e2 := 6, c2 := 82, e3 := 6, c3 := 95 },
    { e1 := 6, c1 := 19, e2 := 6, c2 := 83, e3 := 5, c3 := 47 },
    { e1 := 5, c1 := 8, e2 := 4, c2 := 21, e3 := 4, c3 := 22 },
    { e1 := 5, c1 := 9, e2 := 5, c2 := 42, e3 := 4, c3 := 22 },
    { e1 := 5, c1 := 9, e2 := 5, c2 := 43, e3 := 5, c3 := 44 },
    { e1 := 6, c1 := 18, e2 := 5, c2 := 43, e3 := 5, c3 := 45 },
    { e1 := 6, c1 := 19, e2 := 5, c2 := 43, e3 := 5, c3 := 45 },
    { e1 := 5, c1 := 8, e2 := 4, c2 := 21, e3 := 4, c3 := 23 },
    { e1 := 6, c1 := 18, e2 := 5, c2 := 42, e3 := 5, c3 := 46 },
    { e1 := 6, c1 := 19, e2 := 6, c2 := 84, e3 := 5, c3 := 46 },
    { e1 := 6, c1 := 19, e2 := 6, c2 := 85, e3 := 5, c3 := 46 },
    { e1 := 5, c1 := 9, e2 := 5, c2 := 42, e3 := 5, c3 := 47 },
    { e1 := 5, c1 := 9, e2 := 5, c2 := 43, e3 := 4, c3 := 23 },
    { e1 := 4, c1 := 5, e2 := 4, c2 := 20, e3 := 4, c3 := 22 },
    { e1 := 5, c1 := 10, e2 := 5, c2 := 40, e3 := 4, c3 := 23 },
    { e1 := 5, c1 := 10, e2 := 5, c2 := 41, e3 := 5, c3 := 46 },
    { e1 := 6, c1 := 20, e2 := 6, c2 := 82, e3 := 5, c3 := 47 },
    { e1 := 6, c1 := 20, e2 := 6, c2 := 83, e3 := 6, c3 := 94 },
    { e1 := 6, c1 := 20, e2 := 6, c2 := 83, e3 := 6, c3 := 95 },
    { e1 := 6, c1 := 21, e2 := 5, c2 := 41, e3 := 5, c3 := 47 },
    { e1 := 5, c1 := 11, e2 := 4, c2 := 20, e3 := 4, c3 := 23 },
    { e1 := 5, c1 := 10, e2 := 4, c2 := 21, e3 := 4, c3 := 22 }]

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

/-- The boxes of the groups 240 to 279. -/
noncomputable def boxes_p6 : List Bx :=
  [{ e1 := 5, c1 := 11, e2 := 4, c2 := 21, e3 := 4, c3 := 22 },
    { e1 := 6, c1 := 20, e2 := 6, c2 := 84, e3 := 5, c3 := 46 },
    { e1 := 6, c1 := 20, e2 := 6, c2 := 85, e3 := 5, c3 := 46 },
    { e1 := 6, c1 := 21, e2 := 5, c2 := 42, e3 := 5, c3 := 46 },
    { e1 := 6, c1 := 20, e2 := 6, c2 := 84, e3 := 6, c3 := 94 },
    { e1 := 6, c1 := 20, e2 := 6, c2 := 84, e3 := 6, c3 := 95 },
    { e1 := 6, c1 := 20, e2 := 6, c2 := 85, e3 := 5, c3 := 47 },
    { e1 := 6, c1 := 21, e2 := 6, c2 := 84, e3 := 5, c3 := 47 },
    { e1 := 6, c1 := 21, e2 := 6, c2 := 85, e3 := 6, c3 := 94 },
    { e1 := 6, c1 := 21, e2 := 6, c2 := 85, e3 := 6, c3 := 95 },
    { e1 := 6, c1 := 20, e2 := 6, c2 := 86, e3 := 5, c3 := 46 },
    { e1 := 6, c1 := 20, e2 := 6, c2 := 87, e3 := 5, c3 := 46 },
    { e1 := 6, c1 := 21, e2 := 6, c2 := 86, e3 := 5, c3 := 46 },
    { e1 := 6, c1 := 21, e2 := 6, c2 := 87, e3 := 6, c3 := 92 },
    { e1 := 6, c1 := 21, e2 := 6, c2 := 87, e3 := 6, c3 := 93 },
    { e1 := 5, c1 := 10, e2 := 5, c2 := 43, e3 := 5, c3 := 47 },
    { e1 := 5, c1 := 11, e2 := 5, c2 := 42, e3 := 4, c3 := 23 },
    { e1 := 5, c1 := 11, e2 := 5, c2 := 43, e3 := 5, c3 := 46 },
    { e1 := 6, c1 := 22, e2 := 6, c2 := 86, e3 := 5, c3 := 47 },
    { e1 := 6, c1 := 22, e2 := 6, c2 := 87, e3 := 5, c3 := 47 },
    { e1 := 6, c1 := 23, e2 := 5, c2 := 43, e3 := 5, c3 := 47 },
    { e1 := 3, c1 := 2, e2 := 3, c2 := 11, e3 := 3, c3 := 10 },
    { e1 := 5, c1 := 8, e2 := 4, c2 := 22, e3 := 4, c3 := 22 },
    { e1 := 5, c1 := 9, e2 := 5, c2 := 44, e3 := 4, c3 := 22 },
    { e1 := 5, c1 := 9, e2 := 5, c2 := 45, e3 := 4, c3 := 22 },
    { e1 := 4, c1 := 4, e2 := 4, c2 := 22, e3 := 4, c3 := 23 },
    { e1 := 4, c1 := 4, e2 := 4, c2 := 23, e3 := 3, c3 := 11 },
    { e1 := 5, c1 := 10, e2 := 5, c2 := 44, e3 := 5, c3 := 44 },
    { e1 := 6, c1 := 20, e2 := 5, c2 := 44, e3 := 5, c3 := 45 },
    { e1 := 6, c1 := 21, e2 := 6, c2 := 88, e3 := 5, c3 := 45 },
    { e1 := 6, c1 := 21, e2 := 6, c2 := 89, e3 := 5, c3 := 45 },
    { e1 := 5, c1 := 10, e2 := 5, c2 := 45, e3 := 4, c3 := 22 },
    { e1 := 5, c1 := 11, e2 := 5, c2 := 44, e3 := 4, c3 := 22 },
    { e1 := 5, c1 := 11, e2 := 5, c2 := 45, e3 := 5, c3 := 44 },
    { e1 := 6, c1 := 22, e2 := 6, c2 := 90, e3 := 6, c3 := 90 },
    { e1 := 6, c1 := 22, e2 := 6, c2 := 90, e3 := 6, c3 := 91 },
    { e1 := 6, c1 := 22, e2 := 6, c2 := 91, e3 := 5, c3 := 45 },
    { e1 := 6, c1 := 23, e2 := 6, c2 := 90, e3 := 5, c3 := 45 },
    { e1 := 6, c1 := 23, e2 := 6, c2 := 91, e3 := 5, c3 := 45 },
    { e1 := 5, c1 := 10, e2 := 4, c2 := 22, e3 := 4, c3 := 23 }]

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
  allDone_cons g260_ok <|
  allDone_cons g261_ok <|
  allDone_cons g262_ok <|
  allDone_cons g263_ok <|
  allDone_cons g264_ok <|
  allDone_cons g265_ok <|
  allDone_cons g266_ok <|
  allDone_cons g267_ok <|
  allDone_cons g268_ok <|
  allDone_cons g269_ok <|
  allDone_cons g270_ok <|
  allDone_cons g271_ok <|
  allDone_cons g272_ok <|
  allDone_cons g273_ok <|
  allDone_cons g274_ok <|
  allDone_cons g275_ok <|
  allDone_cons g276_ok <|
  allDone_cons g277_ok <|
  allDone_cons g278_ok <|
  allDone_cons g279_ok <|
  allDone_nil run

/-- The boxes of the groups 280 to 319. -/
noncomputable def boxes_p7 : List Bx :=
  [{ e1 := 6, c1 := 22, e2 := 6, c2 := 88, e3 := 6, c3 := 92 },
    { e1 := 6, c1 := 22, e2 := 6, c2 := 88, e3 := 6, c3 := 93 },
    { e1 := 6, c1 := 22, e2 := 6, c2 := 89, e3 := 5, c3 := 46 },
    { e1 := 6, c1 := 23, e2 := 6, c2 := 88, e3 := 5, c3 := 46 },
    { e1 := 6, c1 := 23, e2 := 6, c2 := 89, e3 := 5, c3 := 46 },
    { e1 := 5, c1 := 11, e2 := 5, c2 := 44, e3 := 5, c3 := 47 },
    { e1 := 6, c1 := 22, e2 := 5, c2 := 45, e3 := 5, c3 := 46 },
    { e1 := 6, c1 := 23, e2 := 6, c2 := 90, e3 := 5, c3 := 46 },
    { e1 := 6, c1 := 23, e2 := 6, c2 := 91, e3 := 5, c3 := 46 },
    { e1 := 5, c1 := 11, e2 := 5, c2 := 45, e3 := 5, c3 := 47 },
    { e1 := 4, c1 := 5, e2 := 4, c2 := 23, e3 := 3, c3 := 11 },
    { e1 := 3, c1 := 3, e2 := 3, c2 := 10, e3 := 2, c3 := 5 },
    { e1 := 3, c1 := 3, e2 := 3, c2 := 11, e3 := 3, c3 := 10 },
    { e1 := 4, c1 := 6, e2 := 4, c2 := 22, e3 := 4, c3 := 22 },
    { e1 := 5, c1 := 12, e2 := 5, c2 := 44, e3 := 4, c3 := 23 },
    { e1 := 6, c1 := 24, e2 := 5, c2 := 45, e3 := 5, c3 := 46 },
    { e1 := 6, c1 := 25, e2 := 5, c2 := 45, e3 := 5, c3 := 46 },
    { e1 := 5, c1 := 12, e2 := 5, c2 := 45, e3 := 5, c3 := 47 },
    { e1 := 5, c1 := 13, e2 := 4, c2 := 22, e3 := 4, c3 := 23 },
    { e1 := 4, c1 := 6, e2 := 4, c2 := 23, e3 := 4, c3 := 22 },
    { e1 := 5, c1 := 12, e2 := 4, c2 := 23, e3 := 4, c3 := 23 },
    { e1 := 5, c1 := 13, e2 := 4, c2 := 23, e3 := 4, c3 := 23 },
    { e1 := 4, c1 := 7, e2 := 3, c2 := 11, e3 := 3, c3 := 11 },
    { e1 := 3, c1 := 0, e2 := 2, c2 := 4, e3 := 2, c3 := 6 },
    { e1 := 5, c1 := 4, e2 := 5, c2 := 32, e3 := 4, c3 := 24 },
    { e1 := 5, c1 := 4, e2 := 5, c2 := 33, e3 := 4, c3 := 24 },
    { e1 := 5, c1 := 5, e2 := 4, c2 := 16, e3 := 4, c3 := 24 },
    { e1 := 4, c1 := 2, e2 := 4, c2 := 16, e3 := 4, c3 := 25 },
    { e1 := 4, c1 := 2, e2 := 4, c2 := 17, e3 := 3, c3 := 12 },
    { e1 := 4, c1 := 3, e2 := 3, c2 := 8, e3 := 3, c3 := 12 },
    { e1 := 3, c1 := 1, e2 := 3, c2 := 8, e3 := 3, c3 := 13 },
    { e1 := 4, c1 := 2, e2 := 3, c2 := 9, e3 := 3, c3 := 12 },
    { e1 := 5, c1 := 6, e2 := 4, c2 := 18, e3 := 4, c3 := 24 },
    { e1 := 5, c1 := 7, e2 := 4, c2 := 18, e3 := 4, c3 := 24 },
    { e1 := 4, c1 := 3, e2 := 4, c2 := 18, e3 := 4, c3 := 25 },
    { e1 := 4, c1 := 3, e2 := 4, c2 := 19, e3 := 3, c3 := 12 },
    { e1 := 3, c1 := 1, e2 := 3, c2 := 9, e3 := 3, c3 := 13 },
    { e1 := 2, c1 := 0, e2 := 2, c2 := 5, e3 := 2, c3 := 6 },
    { e1 := 3, c1 := 2, e2 := 3, c2 := 8, e3 := 2, c3 := 6 },
    { e1 := 5, c1 := 8, e2 := 5, c2 := 36, e3 := 4, c3 := 24 }]

theorem done_p7 : AllDone run boxes_p7 :=
  allDone_cons g280_ok <|
  allDone_cons g281_ok <|
  allDone_cons g282_ok <|
  allDone_cons g283_ok <|
  allDone_cons g284_ok <|
  allDone_cons g285_ok <|
  allDone_cons g286_ok <|
  allDone_cons g287_ok <|
  allDone_cons g288_ok <|
  allDone_cons g289_ok <|
  allDone_cons g290_ok <|
  allDone_cons g291_ok <|
  allDone_cons g292_ok <|
  allDone_cons g293_ok <|
  allDone_cons g294_ok <|
  allDone_cons g295_ok <|
  allDone_cons g296_ok <|
  allDone_cons g297_ok <|
  allDone_cons g298_ok <|
  allDone_cons g299_ok <|
  allDone_cons g300_ok <|
  allDone_cons g301_ok <|
  allDone_cons g302_ok <|
  allDone_cons g303_ok <|
  allDone_cons g304_ok <|
  allDone_cons g305_ok <|
  allDone_cons g306_ok <|
  allDone_cons g307_ok <|
  allDone_cons g308_ok <|
  allDone_cons g309_ok <|
  allDone_cons g310_ok <|
  allDone_cons g311_ok <|
  allDone_cons g312_ok <|
  allDone_cons g313_ok <|
  allDone_cons g314_ok <|
  allDone_cons g315_ok <|
  allDone_cons g316_ok <|
  allDone_cons g317_ok <|
  allDone_cons g318_ok <|
  allDone_cons g319_ok <|
  allDone_nil run

/-- The boxes of the groups 320 to 359. -/
noncomputable def boxes_p8 : List Bx :=
  [{ e1 := 5, c1 := 8, e2 := 5, c2 := 37, e3 := 4, c3 := 24 },
    { e1 := 5, c1 := 9, e2 := 4, c2 := 18, e3 := 4, c3 := 24 },
    { e1 := 4, c1 := 4, e2 := 4, c2 := 18, e3 := 4, c3 := 25 },
    { e1 := 6, c1 := 16, e2 := 5, c2 := 38, e3 := 5, c3 := 48 },
    { e1 := 6, c1 := 17, e2 := 6, c2 := 76, e3 := 5, c3 := 48 },
    { e1 := 6, c1 := 17, e2 := 6, c2 := 77, e3 := 5, c3 := 48 },
    { e1 := 5, c1 := 8, e2 := 5, c2 := 38, e3 := 5, c3 := 49 },
    { e1 := 6, c1 := 16, e2 := 5, c2 := 39, e3 := 5, c3 := 48 },
    { e1 := 6, c1 := 17, e2 := 6, c2 := 78, e3 := 5, c3 := 48 },
    { e1 := 6, c1 := 17, e2 := 6, c2 := 79, e3 := 5, c3 := 48 },
    { e1 := 5, c1 := 8, e2 := 5, c2 := 39, e3 := 5, c3 := 49 },
    { e1 := 5, c1 := 9, e2 := 5, c2 := 38, e3 := 4, c3 := 24 },
    { e1 := 6, c1 := 18, e2 := 6, c2 := 78, e3 := 5, c3 := 48 },
    { e1 := 6, c1 := 18, e2 := 6, c2 := 79, e3 := 5, c3 := 48 },
    { e1 := 6, c1 := 19, e2 := 5, c2 := 39, e3 := 5, c3 := 48 },
    { e1 := 5, c1 := 9, e2 := 5, c2 := 39, e3 := 5, c3 := 49 },
    { e1 := 4, c1 := 4, e2 := 4, c2 := 19, e3 := 4, c3 := 25 },
    { e1 := 4, c1 := 5, e2 := 4, c2 := 18, e3 := 3, c3 := 12 },
    { e1 := 4, c1 := 5, e2 := 4, c2 := 19, e3 := 3, c3 := 12 },
    { e1 := 3, c1 := 2, e2 := 3, c2 := 9, e3 := 3, c3 := 13 },
    { e1 := 3, c1 := 3, e2 := 2, c2 := 4, e3 := 2, c3 := 6 },
    { e1 := 5, c1 := 8, e2 := 4, c2 := 20, e3 := 4, c3 := 24 },
    { e1 := 6, c1 := 18, e2 := 5, c2 := 40, e3 := 5, c3 := 48 },
    { e1 := 6, c1 := 19, e2 := 6, c2 := 80, e3 := 5, c3 := 48 },
    { e1 := 6, c1 := 19, e2 := 6, c2 := 81, e3 := 5, c3 := 48 },
    { e1 := 5, c1 := 9, e2 := 5, c2 := 40, e3 := 5, c3 := 49 },
    { e1 := 5, c1 := 9, e2 := 5, c2 := 41, e3 := 4, c3 := 24 },
    { e1 := 4, c1 := 4, e2 := 4, c2 := 20, e3 := 4, c3 := 25 },
    { e1 := 4, c1 := 4, e2 := 4, c2 := 21, e3 := 3, c3 := 12 },
    { e1 := 5, c1 := 10, e2 := 5, c2 := 40, e3 := 4, c3 := 24 },
    { e1 := 6, c1 := 20, e2 := 5, c2 := 41, e3 := 5, c3 := 48 },
    { e1 := 6, c1 := 21, e2 := 5, c2 := 41, e3 := 5, c3 := 48 },
    { e1 := 5, c1 := 10, e2 := 5, c2 := 41, e3 := 5, c3 := 49 },
    { e1 := 5, c1 := 11, e2 := 4, c2 := 20, e3 := 4, c3 := 24 },
    { e1 := 4, c1 := 5, e2 := 4, c2 := 20, e3 := 4, c3 := 25 },
    { e1 := 5, c1 := 10, e2 := 4, c2 := 21, e3 := 4, c3 := 24 },
    { e1 := 5, c1 := 11, e2 := 4, c2 := 21, e3 := 4, c3 := 24 },
    { e1 := 4, c1 := 5, e2 := 4, c2 := 21, e3 := 4, c3 := 25 },
    { e1 := 3, c1 := 2, e2 := 3, c2 := 10, e3 := 3, c3 := 13 },
    { e1 := 3, c1 := 2, e2 := 3, c2 := 11, e3 := 2, c3 := 6 }]

theorem done_p8 : AllDone run boxes_p8 :=
  allDone_cons g320_ok <|
  allDone_cons g321_ok <|
  allDone_cons g322_ok <|
  allDone_cons g323_ok <|
  allDone_cons g324_ok <|
  allDone_cons g325_ok <|
  allDone_cons g326_ok <|
  allDone_cons g327_ok <|
  allDone_cons g328_ok <|
  allDone_cons g329_ok <|
  allDone_cons g330_ok <|
  allDone_cons g331_ok <|
  allDone_cons g332_ok <|
  allDone_cons g333_ok <|
  allDone_cons g334_ok <|
  allDone_cons g335_ok <|
  allDone_cons g336_ok <|
  allDone_cons g337_ok <|
  allDone_cons g338_ok <|
  allDone_cons g339_ok <|
  allDone_cons g340_ok <|
  allDone_cons g341_ok <|
  allDone_cons g342_ok <|
  allDone_cons g343_ok <|
  allDone_cons g344_ok <|
  allDone_cons g345_ok <|
  allDone_cons g346_ok <|
  allDone_cons g347_ok <|
  allDone_cons g348_ok <|
  allDone_cons g349_ok <|
  allDone_cons g350_ok <|
  allDone_cons g351_ok <|
  allDone_cons g352_ok <|
  allDone_cons g353_ok <|
  allDone_cons g354_ok <|
  allDone_cons g355_ok <|
  allDone_cons g356_ok <|
  allDone_cons g357_ok <|
  allDone_cons g358_ok <|
  allDone_cons g359_ok <|
  allDone_nil run

/-- The boxes of the groups 360 to 399. -/
noncomputable def boxes_p9 : List Bx :=
  [{ e1 := 4, c1 := 6, e2 := 3, c2 := 10, e3 := 3, c3 := 12 },
    { e1 := 4, c1 := 7, e2 := 3, c2 := 10, e3 := 3, c3 := 12 },
    { e1 := 3, c1 := 3, e2 := 3, c2 := 10, e3 := 3, c3 := 13 },
    { e1 := 3, c1 := 3, e2 := 3, c2 := 11, e3 := 2, c3 := 6 },
    { e1 := 1, c1 := 0, e2 := 1, c2 := 2, e3 := 2, c3 := 7 },
    { e1 := 1, c1 := 0, e2 := 1, c2 := 3, e3 := 1, c3 := 2 },
    { e1 := 1, c1 := 0, e2 := 2, c2 := 6, e3 := 1, c3 := 3 },
    { e1 := 1, c1 := 0, e2 := 2, c2 := 7, e3 := 2, c3 := 6 },
    { e1 := 1, c1 := 0, e2 := 3, c2 := 14, e3 := 2, c3 := 7 },
    { e1 := 1, c1 := 0, e2 := 3, c2 := 15, e3 := 3, c3 := 14 },
    { e1 := 1, c1 := 0, e2 := 4, c2 := 30, e3 := 3, c3 := 15 },
    { e1 := 1, c1 := 0, e2 := 4, c2 := 31, e3 := 3, c3 := 15 },
    { e1 := 1, c1 := 1, e2 := 1, c2 := 0, e3 := 1, c3 := 0 },
    { e1 := 1, c1 := 1, e2 := 1, c2 := 0, e3 := 1, c3 := 1 },
    { e1 := 1, c1 := 1, e2 := 1, c2 := 0, e3 := 1, c3 := 2 },
    { e1 := 1, c1 := 1, e2 := 1, c2 := 0, e3 := 2, c3 := 6 },
    { e1 := 1, c1 := 1, e2 := 1, c2 := 0, e3 := 3, c3 := 14 },
    { e1 := 1, c1 := 1, e2 := 1, c2 := 0, e3 := 3, c3 := 15 },
    { e1 := 1, c1 := 1, e2 := 1, c2 := 1, e3 := 1, c3 := 0 },
    { e1 := 1, c1 := 1, e2 := 1, c2 := 1, e3 := 1, c3 := 1 },
    { e1 := 1, c1 := 1, e2 := 1, c2 := 1, e3 := 1, c3 := 2 },
    { e1 := 1, c1 := 1, e2 := 1, c2 := 1, e3 := 2, c3 := 6 },
    { e1 := 1, c1 := 1, e2 := 1, c2 := 1, e3 := 2, c3 := 7 },
    { e1 := 1, c1 := 1, e2 := 1, c2 := 2, e3 := 1, c3 := 1 },
    { e1 := 1, c1 := 1, e2 := 1, c2 := 2, e3 := 1, c3 := 2 },
    { e1 := 2, c1 := 2, e2 := 1, c2 := 2, e3 := 2, c3 := 6 },
    { e1 := 2, c1 := 3, e2 := 1, c2 := 2, e3 := 2, c3 := 6 },
    { e1 := 1, c1 := 1, e2 := 1, c2 := 2, e3 := 3, c3 := 14 },
    { e1 := 1, c1 := 1, e2 := 1, c2 := 2, e3 := 3, c3 := 15 },
    { e1 := 1, c1 := 1, e2 := 1, c2 := 3, e3 := 1, c3 := 2 },
    { e1 := 1, c1 := 1, e2 := 2, c2 := 6, e3 := 2, c3 := 6 },
    { e1 := 1, c1 := 1, e2 := 2, c2 := 6, e3 := 2, c3 := 7 },
    { e1 := 1, c1 := 1, e2 := 2, c2 := 7, e3 := 2, c3 := 6 },
    { e1 := 1, c1 := 1, e2 := 3, c2 := 14, e3 := 2, c3 := 7 },
    { e1 := 1, c1 := 1, e2 := 3, c2 := 15, e3 := 3, c3 := 14 },
    { e1 := 1, c1 := 1, e2 := 4, c2 := 30, e3 := 3, c3 := 15 },
    { e1 := 1, c1 := 1, e2 := 4, c2 := 31, e3 := 3, c3 := 15 },
    { e1 := 1, c1 := 2, e2 := 1, c2 := 1, e3 := 1, c3 := 0 },
    { e1 := 1, c1 := 2, e2 := 1, c2 := 1, e3 := 1, c3 := 1 },
    { e1 := 1, c1 := 2, e2 := 1, c2 := 1, e3 := 1, c3 := 2 }]

theorem done_p9 : AllDone run boxes_p9 :=
  allDone_cons g360_ok <|
  allDone_cons g361_ok <|
  allDone_cons g362_ok <|
  allDone_cons g363_ok <|
  allDone_cons g364_ok <|
  allDone_cons g365_ok <|
  allDone_cons g366_ok <|
  allDone_cons g367_ok <|
  allDone_cons g368_ok <|
  allDone_cons g369_ok <|
  allDone_cons g370_ok <|
  allDone_cons g371_ok <|
  allDone_cons g372_ok <|
  allDone_cons g373_ok <|
  allDone_cons g374_ok <|
  allDone_cons g375_ok <|
  allDone_cons g376_ok <|
  allDone_cons g377_ok <|
  allDone_cons g378_ok <|
  allDone_cons g379_ok <|
  allDone_cons g380_ok <|
  allDone_cons g381_ok <|
  allDone_cons g382_ok <|
  allDone_cons g383_ok <|
  allDone_cons g384_ok <|
  allDone_cons g385_ok <|
  allDone_cons g386_ok <|
  allDone_cons g387_ok <|
  allDone_cons g388_ok <|
  allDone_cons g389_ok <|
  allDone_cons g390_ok <|
  allDone_cons g391_ok <|
  allDone_cons g392_ok <|
  allDone_cons g393_ok <|
  allDone_cons g394_ok <|
  allDone_cons g395_ok <|
  allDone_cons g396_ok <|
  allDone_cons g397_ok <|
  allDone_cons g398_ok <|
  allDone_cons g399_ok <|
  allDone_nil run

/-- The boxes of the groups 400 to 439. -/
noncomputable def boxes_p10 : List Bx :=
  [{ e1 := 1, c1 := 2, e2 := 1, c2 := 1, e3 := 2, c3 := 6 },
    { e1 := 1, c1 := 2, e2 := 1, c2 := 1, e3 := 3, c3 := 14 },
    { e1 := 1, c1 := 2, e2 := 1, c2 := 1, e3 := 4, c3 := 30 },
    { e1 := 1, c1 := 2, e2 := 1, c2 := 1, e3 := 4, c3 := 31 },
    { e1 := 1, c1 := 2, e2 := 1, c2 := 2, e3 := 1, c3 := 1 },
    { e1 := 1, c1 := 2, e2 := 1, c2 := 2, e3 := 1, c3 := 2 },
    { e1 := 1, c1 := 2, e2 := 1, c2 := 2, e3 := 2, c3 := 6 },
    { e1 := 1, c1 := 2, e2 := 1, c2 := 2, e3 := 3, c3 := 14 },
    { e1 := 1, c1 := 2, e2 := 1, c2 := 2, e3 := 4, c3 := 30 },
    { e1 := 1, c1 := 2, e2 := 1, c2 := 2, e3 := 4, c3 := 31 },
    { e1 := 1, c1 := 2, e2 := 1, c2 := 3, e3 := 1, c3 := 2 },
    { e1 := 1, c1 := 2, e2 := 2, c2 := 6, e3 := 2, c3 := 6 },
    { e1 := 1, c1 := 2, e2 := 2, c2 := 6, e3 := 3, c3 := 14 },
    { e1 := 1, c1 := 2, e2 := 2, c2 := 6, e3 := 4, c3 := 30 },
    { e1 := 1, c1 := 2, e2 := 2, c2 := 6, e3 := 4, c3 := 31 },
    { e1 := 1, c1 := 2, e2 := 2, c2 := 7, e3 := 2, c3 := 6 },
    { e1 := 1, c1 := 2, e2 := 3, c2 := 14, e3 := 3, c3 := 14 },
    { e1 := 1, c1 := 2, e2 := 3, c2 := 14, e3 := 3, c3 := 15 },
    { e1 := 1, c1 := 2, e2 := 3, c2 := 15, e3 := 3, c3 := 14 },
    { e1 := 1, c1 := 2, e2 := 4, c2 := 30, e3 := 3, c3 := 15 },
    { e1 := 1, c1 := 2, e2 := 4, c2 := 31, e3 := 3, c3 := 15 },
    { e1 := 1, c1 := 3, e2 := 1, c2 := 2, e3 := 1, c3 := 1 },
    { e1 := 1, c1 := 3, e2 := 1, c2 := 2, e3 := 1, c3 := 2 },
    { e1 := 2, c1 := 6, e2 := 1, c2 := 2, e3 := 2, c3 := 6 },
    { e1 := 2, c1 := 6, e2 := 1, c2 := 2, e3 := 3, c3 := 14 },
    { e1 := 2, c1 := 6, e2 := 1, c2 := 2, e3 := 4, c3 := 30 },
    { e1 := 2, c1 := 6, e2 := 1, c2 := 2, e3 := 4, c3 := 31 },
    { e1 := 1, c1 := 3, e2 := 1, c2 := 3, e3 := 1, c3 := 2 },
    { e1 := 2, c1 := 6, e2 := 2, c2 := 6, e3 := 1, c3 := 3 },
    { e1 := 2, c1 := 6, e2 := 2, c2 := 7, e3 := 2, c3 := 6 },
    { e1 := 2, c1 := 6, e2 := 3, c2 := 14, e3 := 2, c3 := 7 },
    { e1 := 2, c1 := 6, e2 := 3, c2 := 15, e3 := 3, c3 := 14 },
    { e1 := 2, c1 := 6, e2 := 4, c2 := 30, e3 := 3, c3 := 15 },
    { e1 := 2, c1 := 6, e2 := 4, c2 := 31, e3 := 4, c3 := 30 },
    { e1 := 2, c1 := 6, e2 := 4, c2 := 31, e3 := 4, c3 := 31 },
    { e1 := 2, c1 := 7, e2 := 2, c2 := 6, e3 := 2, c3 := 6 },
    { e1 := 3, c1 := 14, e2 := 2, c2 := 6, e3 := 3, c3 := 14 },
    { e1 := 3, c1 := 14, e2 := 2, c2 := 6, e3 := 4, c3 := 30 },
    { e1 := 3, c1 := 14, e2 := 2, c2 := 6, e3 := 4, c3 := 31 },
    { e1 := 2, c1 := 7, e2 := 2, c2 := 7, e3 := 2, c3 := 6 }]

theorem done_p10 : AllDone run boxes_p10 :=
  allDone_cons g400_ok <|
  allDone_cons g401_ok <|
  allDone_cons g402_ok <|
  allDone_cons g403_ok <|
  allDone_cons g404_ok <|
  allDone_cons g405_ok <|
  allDone_cons g406_ok <|
  allDone_cons g407_ok <|
  allDone_cons g408_ok <|
  allDone_cons g409_ok <|
  allDone_cons g410_ok <|
  allDone_cons g411_ok <|
  allDone_cons g412_ok <|
  allDone_cons g413_ok <|
  allDone_cons g414_ok <|
  allDone_cons g415_ok <|
  allDone_cons g416_ok <|
  allDone_cons g417_ok <|
  allDone_cons g418_ok <|
  allDone_cons g419_ok <|
  allDone_cons g420_ok <|
  allDone_cons g421_ok <|
  allDone_cons g422_ok <|
  allDone_cons g423_ok <|
  allDone_cons g424_ok <|
  allDone_cons g425_ok <|
  allDone_cons g426_ok <|
  allDone_cons g427_ok <|
  allDone_cons g428_ok <|
  allDone_cons g429_ok <|
  allDone_cons g430_ok <|
  allDone_cons g431_ok <|
  allDone_cons g432_ok <|
  allDone_cons g433_ok <|
  allDone_cons g434_ok <|
  allDone_cons g435_ok <|
  allDone_cons g436_ok <|
  allDone_cons g437_ok <|
  allDone_cons g438_ok <|
  allDone_cons g439_ok <|
  allDone_nil run

/-- The boxes of the groups 440 to 454. -/
noncomputable def boxes_p11 : List Bx :=
  [{ e1 := 3, c1 := 14, e2 := 3, c2 := 14, e3 := 2, c3 := 7 },
    { e1 := 3, c1 := 14, e2 := 3, c2 := 15, e3 := 3, c3 := 14 },
    { e1 := 3, c1 := 14, e2 := 4, c2 := 30, e3 := 3, c3 := 15 },
    { e1 := 3, c1 := 14, e2 := 4, c2 := 31, e3 := 4, c3 := 30 },
    { e1 := 3, c1 := 14, e2 := 5, c2 := 62, e3 := 4, c3 := 31 },
    { e1 := 3, c1 := 14, e2 := 5, c2 := 63, e3 := 4, c3 := 31 },
    { e1 := 3, c1 := 15, e2 := 3, c2 := 14, e3 := 2, c3 := 7 },
    { e1 := 3, c1 := 15, e2 := 3, c2 := 15, e3 := 3, c3 := 14 },
    { e1 := 4, c1 := 30, e2 := 4, c2 := 30, e3 := 3, c3 := 15 },
    { e1 := 4, c1 := 30, e2 := 4, c2 := 31, e3 := 3, c3 := 15 },
    { e1 := 4, c1 := 31, e2 := 4, c2 := 30, e3 := 3, c3 := 15 },
    { e1 := 4, c1 := 31, e2 := 4, c2 := 31, e3 := 4, c3 := 30 },
    { e1 := 5, c1 := 62, e2 := 4, c2 := 31, e3 := 4, c3 := 31 },
    { e1 := 5, c1 := 63, e2 := 5, c2 := 62, e3 := 4, c3 := 31 },
    { e1 := 5, c1 := 63, e2 := 5, c2 := 63, e3 := 4, c3 := 31 }]

theorem done_p11 : AllDone run boxes_p11 :=
  allDone_cons g440_ok <|
  allDone_cons g441_ok <|
  allDone_cons g442_ok <|
  allDone_cons g443_ok <|
  allDone_cons g444_ok <|
  allDone_cons g445_ok <|
  allDone_cons g446_ok <|
  allDone_cons g447_ok <|
  allDone_cons g448_ok <|
  allDone_cons g449_ok <|
  allDone_cons g450_ok <|
  allDone_cons g451_ok <|
  allDone_cons g452_ok <|
  allDone_cons g453_ok <|
  allDone_cons g454_ok <|
  allDone_nil run

noncomputable def boxes_q0_0 : List Bx :=
  boxes_p0 ++ (boxes_p1 ++ (boxes_p2 ++ (boxes_p3 ++ (boxes_p4 ++ (boxes_p5 ++ (boxes_p6 ++ (boxes_p7 ++ (boxes_p8 ++ (boxes_p9 ++ (boxes_p10 ++ (boxes_p11)))))))))))

theorem done_q0_0 : AllDone run boxes_q0_0 :=
  allDone_append done_p0 <| allDone_append done_p1 <| allDone_append done_p2 <| allDone_append done_p3 <| allDone_append done_p4 <| allDone_append done_p5 <| allDone_append done_p6 <| allDone_append done_p7 <| allDone_append done_p8 <| allDone_append done_p9 <| allDone_append done_p10 <| done_p11

/-- **The master tree**: the boxes of the groups, and boxes on which a cut fails, are the leaves of
trees of bisections of the boxes of the grid of the level 1. -/
theorem master_ok : masterOk run 1 (hex% "f73b7d3b7deded3bfb8e7ededed3ffeee3ffffff7be7beee7ffbbbffbbbffff7b7be7ffbcbffbffbbff7b7b7fffc9ffcbff2d27ffdc9c924ff7ff4b7f72fdc92ff492d1fff272fffd249c4bf3bfcb4e4edff72fdfe49cf7f93b7f73927fdc93bf4edfedf4bedfe4fd24f2ffb4ed39ff7273cedcbf9cf2fd39fdce4e4e4effdced3b4ed39ffc9cfb7d273bdcedf4fd2fefef393939fbff273dc9ce4e4ffbffb4b7d3fcbfd244bfdcef9cefd393fe4bff4fd24ff4fed2d24ffe7fed3927fe4ef7fb72d3f9cefb739c93fbbbfffff724e493dfef93fd3b4bf7244bff4ed3b4fedcb73") boxes_q0_0 = true := by
  decide +kernel

/-- **The slack of the run is nonnegative on its domain**: at the points of `[-1, 1)³` at which the Gram
polynomial, the functions of the cuts and the polynomial constraints of the run are nonnegative. The slack
is the polynomial of the numeral `run.PpM` plus the functions of one variable of the tables, in the units
of the run. -/
theorem slack_nonneg (x1 x2 x3 : ℝ) (h1 : -1 ≤ x1) (h2 : -1 ≤ x2) (h3 : -1 ≤ x3) (hD : Dom run x1 x2 x3) :
    0 ≤ slackFn run tab0 tab1 tab1 x1 x2 x3 :=
  run_sound_master run run_ok tab0 tab1 tab1 ⟨rfl, rfl⟩ ⟨rfl, rfl⟩ ⟨rfl, rfl⟩
    table0_ok table1_ok table1_ok 1 _ boxes_q0_0 master_ok done_q0_0
    x1 x2 x3 h1 h2 h3 hD

/-- info: 'N14Cert.Case1.slack_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms slack_nonneg

end N14Cert.Case1
