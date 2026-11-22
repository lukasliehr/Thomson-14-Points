module

public import CAP.Core.Packed

/-!
# Jets with an exact polynomial of degree five and a bound of order six: the checker (`Init` only)

Statement 7 of T7 (Proposition 9.1 of the source) needs enclosures of the Taylor coefficients of the 91 pair
energies in the gauge coordinates, on a box. A *jet* of a function `F` of four variables encloses a real
polynomial `p` of degree at most 5 and a number `κ` with `|F(D) - p(D)| ≤ κ m⁶` for all `D` with `|D_k| ≤ m`
and `m` at most the radius of the box (`N14.Jet.Rep`, `N14/Jet/Sem.lean`).

**Data.** The monomial `x₀^a₀ x₁^a₁ x₂^a₂ x₃^a₃` of degree `d ≤ 5` has the slot `216 d + a₁ + 6 a₂ + 36 a₃`;
`idxs` lists the 126 slots. A jet holds three packed numbers `P`, `N`, `R` with slots of width `w`: the
coefficient of a monomial, in units of `2^-s`, lies within `R` of `P - N` (slot by slot; one of `P`, `N` is
zero). `S` holds the sums of `P + N + R` over the monomials of every degree (slots `0, …, 5`) and over all
monomials (above them); `K` is the bound `κ` in units of `2^-s`; `ok` is the conjunction of the tests.

**The product** of two jets takes four products of natural numbers: the slot of a product of two monomials is
the sum of their slots, and a product of total degree at least 6 has a slot of at least `6 * 216`. The test
`(sum of all slots of the first) * (sum of all slots of the second) < 2 ^ w` excludes an overflow of a slot.

**Roots.** `jcomp` forms the jet of `F^(-1/2)` or of `F^(1/2)` from the jet of `F` and from a witness for
`u₀^(-1/2)`, where `u₀` is the constant coefficient: the Taylor polynomial of degree 5 of the root at `u₀`,
applied to `F - u₀`, and an algebraic bound for the rest.

The checker is bit-exact with `N14/py/jetref.py`, which was written first. Soundness: `N14/Jet/Sound.lean`.
-/

@[expose] public section

namespace N14.Jet

open CAP

/-- The parameters: the slot width `w` and the scale `s`. -/
structure Par where
  w : Nat
  s : Nat

/-- The slots of the 126 monomials of degree at most 5, in increasing order. -/
def idxs : List Nat :=
  [0, 216, 217, 222, 252, 432, 433, 434, 438, 439, 444, 468, 469, 474, 504, 648, 649, 650, 651, 654, 655, 
   656, 660, 661, 666, 684, 685, 686, 690, 691, 696, 720, 721, 726, 756, 864, 865, 866, 867, 868, 870, 871, 
   872, 873, 876, 877, 878, 882, 883, 888, 900, 901, 902, 903, 906, 907, 908, 912, 913, 918, 936, 937, 938, 
   942, 943, 948, 972, 973, 978, 1008, 1080, 1081, 1082, 1083, 1084, 1085, 1086, 1087, 1088, 1089, 1090, 
   1092, 1093, 1094, 1095, 1098, 1099, 1100, 1104, 1105, 1110, 1116, 1117, 1118, 1119, 1120, 1122, 1123, 
   1124, 1125, 1128, 1129, 1130, 1134, 1135, 1140, 1152, 1153, 1154, 1155, 1158, 1159, 1160, 1164, 1165, 
   1170, 1188, 1189, 1190, 1194, 1195, 1200, 1224, 1225, 1230, 1260]

/-- The triple of a coefficient: the centre `p - n` and the radius `r`. -/
structure T3 where
  p : Nat
  n : Nat
  r : Nat

/-- A jet. -/
structure Jet where
  P : Nat
  N : Nat
  R : Nat
  S : Nat
  K : Nat
  ok : Bool

/-- One pass over the slots: the packed numbers of the triples `h e`, and their sums. -/
noncomputable def pass (w : Nat) (h : Nat → T3) : List Nat → Jet :=
  List.rec (motive := fun _ => Jet) ⟨0, 0, 0, 0, 0, true⟩
    (fun e _ ih =>
      let t := h e
      let sh := Nat.mul w e
      ⟨Nat.add ih.P (Nat.shiftLeft t.p sh), Nat.add ih.N (Nat.shiftLeft t.n sh),
        Nat.add ih.R (Nat.shiftLeft t.r sh),
        Nat.add ih.S (Nat.mul (Nat.add (Nat.add t.p t.n) t.r)
          (Nat.add (Nat.shiftLeft 1 (Nat.mul w (Nat.div e 216))) (Nat.shiftLeft 1 (Nat.mul w 6)))),
        0, true⟩)

/-- The sum of all slots of a jet (if no sum overflows). -/
def total (w : Nat) (a : Jet) : Nat := Nat.shiftRight a.S (Nat.mul w 6)

/-- The jet of a pass with its bound of order six and its flag; the test excludes an overflow of a slot. -/
def fin (par : Par) (a : Jet) (K : Nat) (ok : Bool) : Jet :=
  ⟨a.P, a.N, a.R, a.S, K, ok && Nat.blt (total par.w a) (Nat.shiftLeft 1 par.w)⟩

/-- `ceil (x / 2 ^ sh)`. -/
def cdiv (x sh : Nat) : Nat := Nat.shiftRight (Nat.add x (Nat.sub (Nat.shiftLeft 1 sh) 1)) sh

/-- `ceil (x / d)`. -/
def cdivn (x d : Nat) : Nat := Nat.div (Nat.add x (Nat.sub d 1)) d

/-- The centre `p - n` in the normal form, with the radius `r`. -/
def norm3 (p n r : Nat) : T3 := ⟨Nat.sub p n, Nat.sub n p, r⟩

/-- A coefficient after a product: the centre `pc - nc` and the radius `rc` in units of `2^(-2s)`, in units
of `2^-s`. The centre is rounded towards zero, the radius up; it grows by one if the centre was rounded. -/
def resc (s pc nc rc : Nat) : T3 :=
  let c := Nat.add (Nat.sub pc nc) (Nat.sub nc pc)
  let q := Nat.shiftRight c s
  let r := Nat.add (cdiv rc s) (Nat.sub 1 (Nat.sub 1 (Nat.sub c (Nat.shiftLeft q s))))
  cond (Nat.ble nc pc) ⟨q, 0, r⟩ ⟨0, q, r⟩

/-- The slot of the variable `k`. -/
def uk (k : Nat) : Nat := cond (Nat.beq k 0) 216 (cond (Nat.beq k 1) 217 (cond (Nat.beq k 2) 222 252))

/-- The jet of a constant with the enclosure `(cp, cn, cr)`. -/
noncomputable def jconst (par : Par) (cp cn cr : Nat) : Jet :=
  fin par (pass par.w (fun e => cond (Nat.beq e 0) ⟨cp, cn, cr⟩ ⟨0, 0, 0⟩) idxs) 0 true

/-- The jet of a natural number. -/
noncomputable def jnat (par : Par) (n : Nat) : Jet := jconst par (Nat.shiftLeft n par.s) 0 0

/-- The jet of `D_k + c` for a constant with the enclosure `(cp, cn, cr)`. -/
noncomputable def jvar (par : Par) (k cp cn cr : Nat) : Jet :=
  fin par (pass par.w (fun e => cond (Nat.beq e 0) ⟨cp, cn, cr⟩
    (cond (Nat.beq e (uk k)) ⟨Nat.shiftLeft 1 par.s, 0, 0⟩ ⟨0, 0, 0⟩)) idxs) 0 true

/-- The sum of two jets. -/
noncomputable def jadd (par : Par) (a b : Jet) : Jet :=
  fin par (pass par.w (fun e => norm3 (Nat.add (slot par.w a.P e) (slot par.w b.P e))
    (Nat.add (slot par.w a.N e) (slot par.w b.N e)) (Nat.add (slot par.w a.R e) (slot par.w b.R e))) idxs)
    (Nat.add a.K b.K) (a.ok && b.ok)

/-- The negative of a jet. -/
def jneg (a : Jet) : Jet := ⟨a.N, a.P, a.R, a.S, a.K, a.ok⟩

/-- The jet of `c F` for a constant with the enclosure `(cp, cn, cr)`. -/
noncomputable def jscale (par : Par) (cp cn cr : Nat) (a : Jet) : Jet :=
  let cs := Nat.add (Nat.add cp cn) cr
  fin par (pass par.w (fun e =>
    let p := slot par.w a.P e
    let n := slot par.w a.N e
    let r := slot par.w a.R e
    resc par.s (Nat.add (Nat.mul p cp) (Nat.mul n cn)) (Nat.add (Nat.mul p cn) (Nat.mul n cp))
      (Nat.add (Nat.mul (Nat.add p n) cr) (Nat.mul r cs))) idxs)
    (cdiv (Nat.mul a.K cs) par.s) a.ok

/-- The sum of `P + N + R` over the monomials of degree `d`. -/
def nd (w : Nat) (a : Jet) (d : Nat) : Nat := slot w a.S d

/-- A bound for the polynomial of a jet on the box: `∑ n_d rb^d` with `rb = 33 / 4096`, rounded up. -/
def pbound (w : Nat) (a : Jet) : Nat :=
  Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (nd w a 0) (cdiv (Nat.mul (nd w a 1) 33) 12))
    (cdiv (Nat.mul (nd w a 2) 1089) 24)) (cdiv (Nat.mul (nd w a 3) 35937) 36))
    (cdiv (Nat.mul (nd w a 4) 1185921) 48)) (cdiv (Nat.mul (nd w a 5) 39135393) 60)

/-- The bound for the terms of degree 6 to 10 of the product of the polynomials of two jets, divided by
`m^6`. -/
def high (w : Nat) (a b : Jet) : Nat :=
  let c6 := Nat.add (Nat.add (Nat.add (Nat.add (Nat.mul (nd w a 1) (nd w b 5)) (Nat.mul (nd w a 2) (nd w b 4)))
    (Nat.mul (nd w a 3) (nd w b 3))) (Nat.mul (nd w a 4) (nd w b 2))) (Nat.mul (nd w a 5) (nd w b 1))
  let c7 := Nat.add (Nat.add (Nat.add (Nat.mul (nd w a 2) (nd w b 5)) (Nat.mul (nd w a 3) (nd w b 4)))
    (Nat.mul (nd w a 4) (nd w b 3))) (Nat.mul (nd w a 5) (nd w b 2))
  let c8 := Nat.add (Nat.add (Nat.mul (nd w a 3) (nd w b 5)) (Nat.mul (nd w a 4) (nd w b 4)))
    (Nat.mul (nd w a 5) (nd w b 3))
  let c9 := Nat.add (Nat.mul (nd w a 4) (nd w b 5)) (Nat.mul (nd w a 5) (nd w b 4))
  let c10 := Nat.mul (nd w a 5) (nd w b 5)
  Nat.add (Nat.add (Nat.add (Nat.add c6 (cdiv (Nat.mul c7 33) 12)) (cdiv (Nat.mul c8 1089) 24))
    (cdiv (Nat.mul c9 35937) 36)) (cdiv (Nat.mul c10 1185921) 48)

/-- The product of two jets. -/
noncomputable def jmul (par : Par) (a b : Jet) : Jet :=
  let w := par.w
  let A1 := Nat.add a.P a.N
  let A2 := Nat.add b.P b.N
  let PP := Nat.mul a.P b.P
  let NN := Nat.mul a.N b.N
  let AA := Nat.mul A1 A2
  let TT := Nat.mul (Nat.add A1 a.R) (Nat.add A2 b.R)
  fin par (pass w (fun e =>
    let pp := Nat.add (slot w PP e) (slot w NN e)
    let aa := slot w AA e
    resc par.s pp (Nat.sub aa pp) (Nat.sub (slot w TT e) aa)) idxs)
    (cdiv (Nat.add (Nat.add (high w a b) (Nat.mul (pbound w a) b.K))
      (Nat.mul a.K (Nat.add (pbound w b) (cdiv (Nat.mul b.K 1291467969) 72)))) par.s)
    (a.ok && b.ok && Nat.blt (Nat.mul (total w a) (total w b)) (Nat.shiftLeft 1 w))

/-- The enclosure of an interval `[lo, hi]` of natural numbers: the centre and the radius. -/
def encC (lo hi : Nat) : Nat := Nat.div (Nat.add lo hi) 2

def encR (lo hi : Nat) : Nat := Nat.sub hi (encC lo hi)

/-- The `j`-th power of the witness, in units of `2^-s`: a lower and an upper bound. -/
def pwLo (s blo j : Nat) : Nat := Nat.shiftRight (Nat.pow blo j) (Nat.mul s (Nat.sub j 1))

def pwHi (s bhi j : Nat) : Nat := cdiv (Nat.pow bhi j) (Nat.mul s (Nat.sub j 1))

/-- The jet of `a_k N^k`: the coefficient `a_k` is the number `nu / 2^sh` times a number between `lo` and
`hi`, with the sign `neg`. -/
noncomputable def term (par : Par) (lo hi nu sh : Nat) (neg : Bool) (b : Jet) : Jet :=
  let l := Nat.shiftRight (Nat.mul lo nu) sh
  let h := cdiv (Nat.mul hi nu) sh
  cond neg (jscale par 0 (encC l h) (encR l h) b) (jscale par (encC l h) 0 (encR l h) b)

/-- The jet of `F^(-1/2)` (`mode = false`) or `F^(1/2)` (`mode = true`) with the witness `blo ≤ u₀^(-1/2) ≤ bhi`
(in units of `2^-s`). -/
noncomputable def jcomp (par : Par) (mode : Bool) (a : Jet) (blo bhi : Nat) : Jet :=
  let w := par.w
  let s := par.s
  let p0 := slot w a.P 0
  let n0 := slot w a.N 0
  let r0 := slot w a.R 0
  let u0lo := Nat.sub (Nat.sub p0 n0) r0
  let u0hi := Nat.add (Nat.sub p0 n0) r0
  let one := Nat.shiftLeft 1 (Nat.mul 3 s)
  let Nj := fin par (pass w (fun e => cond (Nat.beq e 0) ⟨0, 0, 0⟩
    ⟨slot w a.P e, slot w a.N e, slot w a.R e⟩) idxs) a.K a.ok
  let nu := Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (nd w Nj 1) (cdiv (Nat.mul (nd w Nj 2) 33) 12))
    (cdiv (Nat.mul (nd w Nj 3) 1089) 24)) (cdiv (Nat.mul (nd w Nj 4) 35937) 36))
    (cdiv (Nat.mul (nd w Nj 5) 1185921) 48)) (cdiv (Nat.mul a.K 39135393) 60)
  let N2 := jmul par Nj Nj
  let N3 := jmul par N2 Nj
  let N4 := jmul par N2 N2
  let N5 := jmul par N4 Nj
  let ok := a.ok && Nat.blt (Nat.add n0 r0) p0 && Nat.ble 1 blo && Nat.ble blo bhi
    && Nat.ble (Nat.mul (Nat.mul blo blo) u0hi) one && Nat.ble one (Nat.mul (Nat.mul bhi bhi) u0lo)
    && Nat.ble (Nat.mul (Nat.mul (Nat.mul (Nat.mul 8 nu) 33) bhi) bhi) (Nat.shiftLeft 1 (Nat.add 12 (Nat.mul 3 s)))
  let out := cond mode
    (jadd par (jadd par (jadd par (jadd par (jadd par
      (let l := Nat.shiftRight (Nat.mul u0lo blo) s
       let h := cdiv (Nat.mul u0hi bhi) s
       jconst par (encC l h) 0 (encR l h))
      (term par (pwLo s blo 1) (pwHi s bhi 1) 1 1 false Nj))
      (term par (pwLo s blo 3) (pwHi s bhi 3) 1 3 true N2))
      (term par (pwLo s blo 5) (pwHi s bhi 5) 1 4 false N3))
      (term par (pwLo s blo 7) (pwHi s bhi 7) 5 7 true N4))
      (term par (pwLo s blo 9) (pwHi s bhi 9) 7 8 false N5))
    (jadd par (jadd par (jadd par (jadd par (jadd par
      (let l := pwLo s blo 1
       let h := pwHi s bhi 1
       jconst par (encC l h) 0 (encR l h))
      (term par (pwLo s blo 3) (pwHi s bhi 3) 1 1 true Nj))
      (term par (pwLo s blo 5) (pwHi s bhi 5) 3 3 false N2))
      (term par (pwLo s blo 7) (pwHi s bhi 7) 5 4 true N3))
      (term par (pwLo s blo 9) (pwHi s bhi 9) 35 7 false N4))
      (term par (pwLo s blo 11) (pwHi s bhi 11) 63 8 true N5))
  let rem := cond mode
    (cdivn (Nat.mul (Nat.pow bhi 11) (Nat.pow nu 6)) (Nat.shiftLeft 16 (Nat.mul s 16)))
    (cdivn (Nat.mul (Nat.pow bhi 13) (Nat.pow nu 6)) (Nat.shiftLeft 2 (Nat.mul s 18)))
  ⟨out.P, out.N, out.R, out.S, Nat.add out.K rem, out.ok && ok⟩

/-- A coefficient of the trigonometric jet: the triple `(p, n, r)` divided by `d`, with the sign `neg`. -/
def tput (p n r d : Nat) (neg : Bool) : T3 :=
  let r' := Nat.add (cdivn r d) (Nat.sub 1 (Nat.sub 1 (Nat.add (Nat.mod p d) (Nat.mod n d))))
  cond neg ⟨Nat.div n d, Nat.div p d, r'⟩ ⟨Nat.div p d, Nat.div n d, r'⟩

/-- The jet of `c cos D_k - sn sin D_k` for constants with the enclosures `(cp, cn, cr)` and `(sp, sn, sr)`. -/
noncomputable def jtrig (par : Par) (k cp cn cr sp sn sr : Nat) : Jet :=
  let u := uk k
  fin par (pass par.w (fun e =>
    cond (Nat.beq (Nat.mod e u) 0)
      (let j := Nat.div e u
       cond (Nat.beq j 0) (tput cp cn cr 1 false)
        (cond (Nat.beq j 1) (tput sp sn sr 1 true)
        (cond (Nat.beq j 2) (tput cp cn cr 2 true)
        (cond (Nat.beq j 3) (tput sp sn sr 6 false)
        (cond (Nat.beq j 4) (tput cp cn cr 24 false)
        (cond (Nat.beq j 5) (tput sp sn sr 120 true) ⟨0, 0, 0⟩))))))
      ⟨0, 0, 0⟩) idxs)
    (Nat.add (cdivn (Nat.mul (Nat.add (Nat.add cp cn) cr) 7) 4320)
      (cdivn (Nat.mul (Nat.add (Nat.add sp sn) sr) 33) 18063360)) true

/-- The final test of the coefficients of degree 2, 3 and 4: every enclosure lies in the claimed one. -/
noncomputable def leSlots (w : Nat) (a : Jet) (Pc Nc Rc : Nat) : List Nat → Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun e _ ih =>
      let d := Nat.div e 216
      cond (Nat.ble 2 d && Nat.ble d 4)
        (let p := slot w a.P e
         let n := slot w a.N e
         let r := slot w a.R e
         let pc := slot w Pc e
         let nc := slot w Nc e
         let rc := slot w Rc e
         Nat.ble (Nat.add (Nat.add pc n) r) (Nat.add (Nat.add p nc) rc)
           && Nat.ble (Nat.add (Nat.add p nc) r) (Nat.add (Nat.add pc n) rc) && ih)
        ih)

/-- The final test of a jet against the claims: the coefficients of degree 2, 3, 4, the sum of the absolute
values of the coefficients of degree 5, and the bound of order six. -/
noncomputable def jle (par : Par) (a : Jet) (Pc Nc Rc n5c Kc : Nat) : Bool :=
  a.ok && Nat.ble a.K Kc && Nat.ble (nd par.w a 5) n5c && leSlots par.w a Pc Nc Rc idxs

/-- The triple `i` of a table of enclosures of real constants; `(0, 0, 0)` outside the table. -/
noncomputable def tget : List T3 → Nat → T3 :=
  List.rec (motive := fun _ => Nat → T3) (fun _ => ⟨0, 0, 0⟩)
    (fun t _ ih i => Nat.rec (motive := fun _ => T3) t (fun j _ => ih j) i)

/-- An expression. An index `i` names a real constant, enclosed by the triple `i` of a table. -/
inductive JExp where
  | nat (n : Nat)
  | cst (i : Nat)
  | var (k i : Nat)
  | trig (k ic is : Nat)
  | add (a b : JExp)
  | neg (a : JExp)
  | mul (a b : JExp)
  | sqrt (a : JExp) (blo bhi : Nat)
  | isqrt (a : JExp) (blo bhi : Nat)

/-- The jet of an expression, for a table of enclosures of the constants. -/
noncomputable def jeval (par : Par) (tab : List T3) : JExp → Jet :=
  JExp.rec (motive := fun _ => Jet)
    (fun n => jnat par n)
    (fun i => jconst par (tget tab i).p (tget tab i).n (tget tab i).r)
    (fun k i => jvar par k (tget tab i).p (tget tab i).n (tget tab i).r)
    (fun k ic is => jtrig par k (tget tab ic).p (tget tab ic).n (tget tab ic).r
      (tget tab is).p (tget tab is).n (tget tab is).r)
    (fun _ _ ja jb => jadd par ja jb)
    (fun _ ja => jneg ja)
    (fun _ _ ja jb => jmul par ja jb)
    (fun _ blo bhi ja => jcomp par true ja blo bhi)
    (fun _ blo bhi ja => jcomp par false ja blo bhi)

/-- **The checker of a pair**: the jet of the expression passes the final test against the claims. -/
noncomputable def pairOk (par : Par) (tab : List T3) (e : JExp) (Pc Nc Rc n5c Kc : Nat) : Bool :=
  jle par (jeval par tab e) Pc Nc Rc n5c Kc

end N14.Jet
