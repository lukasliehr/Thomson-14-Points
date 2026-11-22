module

public import CAP.Schema.ThreePoint.Kernel
public import N14.Box.Kernel

/-!
# T7, the energy identity of a certificate with slack functions: the checker (`Init` only)

**Setting.** The points of a configuration have one of two types, `0` and `1` (one type in the untyped
certificates). A certificate has, for every type `r` of a root point and every `k = 0, …, K`, a symmetric
matrix `F` whose rows and columns belong to the basis functions `(σ, i)`: the function `u ^ i` on the points of
the type `σ`. The functions of the type `0` come first; there are `n0` of them. The matrix is stored as in
`CAP.PSD`: the upper triangle `X i j`, `i ≤ j`, with `X i i = F i i / 2` and `X i j = F i j`, so that the kernel
`∑ F (σ,i) (σ',j) u ^ i v ^ j Q_k (u, v, t)` is `K (u, v, t) + K (v, u, t)` for

  `K_r (σ, σ') (u, v, t) = ∑ k, φ_k,σσ' (u, v) * Q_k (u, v, t)`,   `φ_k,σσ' = ∑_{(σ,i) ≤ (σ',j)} X (σ,i) (σ',j) u ^ i v ^ j`

(`part`, `kern`; the part `σ = 1, σ' = 0` is zero). `Q_k` are the polynomials of `CAP.ThreePoint`.

**The identity of a run** (`id3Ok`). The slack of a pattern of three types is, up to positive factors, a
polynomial `M` whose coefficients are the slots of the number `PpM` of a run of `N14.Box`, plus functions of one
variable. The checker verifies

  `cM * M (u, v, t) + cK * ∑ terms = B₀ (u) + B₁ (v) + B₂ (t) + c`

for a list of terms, each of which is a kernel `K_r (σ, σ')` with the three variables in some order (the six
kernels that contain the three points of a triple), integers `cM`, `cK`, polynomials `B_a` of one variable and a
constant `c`. So the monomials of `M` in more than one variable are those of the kernels.

**The identity of a pair** (`id1Ok`). For two types, the functions of one variable of the slots that belong to
the pair, weighted with the numbers of third points, plus the kernels with two equal points, are a constant; and
the weights of the Coulomb terms add up as the energy needs.

**Method.** Kronecker substitution, as in `CAP.ThreePoint`: all polynomials are evaluated at a point
`(X ^ a, X ^ b, X ^ c)`, `X = 2 ^ W`, as pairs (positive part, negative part) of natural numbers. For the identity
of a run the point is `(X, X ^ m, X ^ (m * m))` with `m = n + 1` and `W` the slot width of the run, so that the
number `PpM` is the value of `M` plus its bias, and a kernel with permuted variables is the kernel at the
permuted point. The same code at the point `(1, 1, 1)` gives the sums of the coefficients, which bound the
coefficients of both sides. For the identity of a pair the points are `(X, X, 1)`, `(X, 1, X)`, `(1, X, X)`.

The checker is bit-exact with `N14/py/identref.py`.
-/

@[expose] public section

namespace N14.Ident

open CAP CAP.ThreePoint

/-- A block of a kernel: the matrix of order `N` in the layout of `CAP.PSD`, whose first `n0` basis functions
belong to the type `0`. -/
structure Blk where
  N : Nat
  n0 : Nat
  rows : Nat

/-- The number of slots before row `r` of a triangular array of order `N`. -/
noncomputable def triOffK (N : Nat) : Nat → Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun t ih => Nat.add ih (Nat.sub N t))

/-- The loop over the rows `i < n0` of a block. Row `i` has the `n0 - i` entries `(i, j)`, `i ≤ j < n0`, and then
the `N - n0` entries `(i, n0 + j)`. The state is the remaining data, `i`, the two parts of
`∑_{i ≤ j < n0} X i j • u ^ i * v ^ j` and the two parts of `∑_{i < n0, j} X i (n0 + j) • u ^ i * v ^ j`. -/
noncomputable def headGo (P : Params) (pt : Pt) (N n0 : Nat) (cnt : Nat) :
    Nat → Nat → Nat → Nat → Nat → Nat → Nat × Nat × Nat × Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → Nat → Nat → Nat → Nat × Nat × Nat × Nat)
    (fun _ _ a b c d => (a, b, c, d))
    (fun _ ih R i a b c d =>
      ih (Nat.shiftRight R (Nat.mul P.w (Nat.sub N i))) (Nat.succ i)
        (phiRow P.w (mask P.w) (Nat.shiftLeft 1 (Nat.sub P.a 1)) (Nat.mul P.W pt.pv) (Nat.sub n0 i)
          (Nat.land R (mask (Nat.mul P.w (Nat.sub n0 i))))
          (Nat.mul P.W (Nat.mul i (Nat.add pt.pu pt.pv))) a b).1
        (phiRow P.w (mask P.w) (Nat.shiftLeft 1 (Nat.sub P.a 1)) (Nat.mul P.W pt.pv) (Nat.sub n0 i)
          (Nat.land R (mask (Nat.mul P.w (Nat.sub n0 i))))
          (Nat.mul P.W (Nat.mul i (Nat.add pt.pu pt.pv))) a b).2
        (phiRow P.w (mask P.w) (Nat.shiftLeft 1 (Nat.sub P.a 1)) (Nat.mul P.W pt.pv) (Nat.sub N n0)
          (Nat.land (Nat.shiftRight R (Nat.mul P.w (Nat.sub n0 i))) (mask (Nat.mul P.w (Nat.sub N n0))))
          (Nat.mul P.W (Nat.mul i pt.pu)) c d).1
        (phiRow P.w (mask P.w) (Nat.shiftLeft 1 (Nat.sub P.a 1)) (Nat.mul P.W pt.pv) (Nat.sub N n0)
          (Nat.land (Nat.shiftRight R (Nat.mul P.w (Nat.sub n0 i))) (mask (Nat.mul P.w (Nat.sub N n0))))
          (Nat.mul P.W (Nat.mul i pt.pu)) c d).2)
    cnt

/-- The polynomial `φ` of a part of a block at a point, as a pair. `sel = 0`: both basis functions have the
type `0`; `sel = 1`: the first one has the type `0`, the second one the type `1`; every other value: both have
the type `1`. -/
noncomputable def part (P : Params) (pt : Pt) (B : Blk) (sel : Nat) : Nat × Nat :=
  Nat.rec (motive := fun _ => Nat × Nat)
    ((headGo P pt B.N B.n0 B.n0 B.rows 0 0 0 0 0).1, (headGo P pt B.N B.n0 B.n0 B.rows 0 0 0 0 0).2.1)
    (fun s _ => Nat.rec (motive := fun _ => Nat × Nat)
      ((headGo P pt B.N B.n0 B.n0 B.rows 0 0 0 0 0).2.2.1, (headGo P pt B.N B.n0 B.n0 B.rows 0 0 0 0 0).2.2.2)
      (fun _ _ =>
        ((phiEval P pt (Nat.sub B.N B.n0) (Nat.shiftRight B.rows (Nat.mul P.w (triOffK B.N B.n0)))).1,
         (phiEval P pt (Nat.sub B.N B.n0) (Nat.shiftRight B.rows (Nat.mul P.w (triOffK B.N B.n0)))).2.1))
      s)
    sel

/-- The loop over the blocks of a kernel; the state is `k`, `Qₖ`, `Qₖ₋₁` and the two parts of the sum. -/
noncomputable def kernGo (P : Params) (pt : Pt) (sel : Nat) :
    List Blk → Nat → Nat × Nat → Nat × Nat → Nat → Nat → Nat × Nat :=
  List.rec (motive := fun _ => Nat → Nat × Nat → Nat × Nat → Nat → Nat → Nat × Nat)
    (fun _ _ _ Mp Mn => (Mp, Mn))
    (fun B _ ih k cur prev Mp Mn =>
      ih (Nat.succ k)
        (Bool.rec (motive := fun _ => Nat × Nat) (qNext P pt cur prev)
          (mulTerms P pt 2 (tuv P) 1 0 0 0) (Nat.beq k 0))
        cur
        (Nat.add Mp (Nat.add (Nat.mul (part P pt B sel).1 cur.1) (Nat.mul (part P pt B sel).2 cur.2)))
        (Nat.add Mn (Nat.add (Nat.mul (part P pt B sel).1 cur.2) (Nat.mul (part P pt B sel).2 cur.1))))

/-- The kernel `∑ₖ φₖ * Qₖ` of a part at a point, as a pair. -/
noncomputable def kern (P : Params) (pt : Pt) (sel : Nat) (blocks : List Blk) : Nat × Nat :=
  kernGo P pt sel blocks 0 (1, 0) (0, 0) 0 0

/-- The blocks `k, k + 1, …` have basis functions of degree at most `m - 1 - k` in both types, and there are
at most `m - k` of them. -/
noncomputable def blocksOk (m : Nat) : List Blk → Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun k => Nat.ble k m)
    (fun B _ ih k => Nat.ble B.n0 B.N && Nat.ble (Nat.add B.n0 k) m &&
      Nat.ble (Nat.add (Nat.sub B.N B.n0) k) m && ih (Nat.succ k))

/-! ## The identity of a run -/

/-- A term of the identity of a run: the kernel of a part of a list of blocks, in which the variable with the
number `s0` (`0`: `u`, `1`: `v`, every other value: `t`) takes the first place, `s1` the second and `s2` the
third. -/
structure Term where
  blocks : List Blk
  sel : Nat
  s0 : Nat
  s1 : Nat
  s2 : Nat

/-- The exponent of `X` at the place of the variable `s` in the layout of a run with `m = n + 1`. -/
noncomputable def wt (m s : Nat) : Nat := CAP.Bernstein.sel s 1 m (Nat.mul m m)

/-- The point of a term in the layout of a run. -/
noncomputable def tpt (m : Nat) (T : Term) : Pt := ⟨wt m T.s0, wt m T.s1, wt m T.s2⟩

/-- The sum of the kernels of the terms, each at the point that `f` gives, as a pair. -/
noncomputable def termsGo (P : Params) (f : Term → Pt) : List Term → Nat → Nat → Nat × Nat :=
  List.rec (motive := fun _ => Nat → Nat → Nat × Nat) (fun Sp Sn => (Sp, Sn))
    (fun T _ ih Sp Sn =>
      ih (Nat.add Sp (kern P (f T) T.sel T.blocks).1) (Nat.add Sn (kern P (f T) T.sel T.blocks).2))

/-- All terms have blocks of bounded degree (`blocksOk`), and their numbers `s0`, `s1`, `s2` are the numbers
`0`, `1`, `2` in some order. -/
noncomputable def termsOk (m : Nat) : List Term → Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun T _ ih => blocksOk m T.blocks 0 && Nat.ble T.s0 2 && Nat.ble T.s1 2 && Nat.ble T.s2 2 &&
      (Nat.blt T.s0 T.s1 || Nat.blt T.s1 T.s0) && (Nat.blt T.s0 T.s2 || Nat.blt T.s2 T.s0) &&
      (Nat.blt T.s1 T.s2 || Nat.blt T.s2 T.s1) && ih)

/-- The data of the identity of a run. -/
structure Id3 where
  /-- the polynomials have degree at most `n` in each variable -/
  n : Nat
  /-- the slots of `PpM` are the coefficients plus `2 ^ (aH - 1)` -/
  aH : Nat
  /-- the number of the mixed part of the run: `(n + 1) ^ 3` slots of width `P.W` -/
  PpM : Nat
  /-- the factors of the mixed part and of the kernels -/
  cM : Nat
  cK : Nat
  terms : List Term
  /-- slot width and bias exponent of the polynomials of one variable -/
  wB : Nat
  aB : Nat
  /-- the polynomials of `u`, `v`, `t`: `n + 1` slots, coefficient plus `2 ^ (aB - 1)` -/
  B0 : Nat
  B1 : Nat
  B2 : Nat
  /-- the constant is `cp - cn` -/
  cp : Nat
  cn : Nat

/-- The checker of the identity of a run:
`cM * M + cK * ∑ terms = B₀ (u) + B₁ (v) + B₂ (t) + cp - cn`. The numbers `eb`, `cb` of `P` are those of the
term fields of the fixed polynomials `t - u * v` and `(1 - u ^ 2) * (1 - v ^ 2)`. -/
noncomputable def id3Ok (P : Params) (I : Id3) : Bool :=
  Nat.ble 1 P.W && Nat.ble 2 P.eb && Nat.ble 1 P.cb && Nat.ble 1 I.aH && Nat.ble I.aH P.W &&
  Nat.ble 1 I.aB && Nat.ble I.aB I.wB && Nat.ble I.wB P.W && termsOk (Nat.succ I.n) I.terms &&
  -- the numbers of the data have the right numbers of slots, and the slots of `PpM` are below `2 ^ aH`
  Nat.blt I.PpM (Nat.shiftLeft 1 (Nat.mul P.W (CAP.Bernstein.cube I.n))) &&
  Nat.beq (Nat.land I.PpM
    (Nat.mul (Nat.sub (Nat.shiftLeft 1 P.W) (Nat.shiftLeft 1 I.aH)) (ones P.W (CAP.Bernstein.cube I.n)))) 0 &&
  -- the sums of the coefficients of the two sides are below `2 ^ W`
  Nat.blt
    (Nat.add (Nat.add (Nat.add (Nat.mul (Nat.mul I.cM (CAP.Bernstein.cube I.n)) (Nat.shiftLeft 1 I.aH))
      (Nat.mul I.cK (termsGo P (fun _ => ⟨0, 0, 0⟩) I.terms 0 0).1))
      (Nat.mul (Nat.mul 3 (Nat.succ I.n)) (Nat.shiftLeft 1 I.aB))) I.cn)
    (Nat.shiftLeft 1 P.W) &&
  Nat.blt
    (Nat.add (Nat.add (Nat.add (Nat.mul (Nat.mul 3 (Nat.succ I.n)) (Nat.shiftLeft 1 I.wB)) I.cp)
      (Nat.mul (Nat.mul I.cM (CAP.Bernstein.cube I.n)) (Nat.shiftLeft 1 I.aH)))
      (Nat.mul I.cK (termsGo P (fun _ => ⟨0, 0, 0⟩) I.terms 0 0).2))
    (Nat.shiftLeft 1 P.W) &&
  -- the two sides at the point of the layout
  Nat.beq
    (Nat.add (Nat.add (Nat.add (Nat.mul I.cM I.PpM)
        (Nat.mul I.cK (termsGo P (tpt (Nat.succ I.n)) I.terms 0 0).1))
      (Nat.mul (Nat.shiftLeft 1 (Nat.sub I.aB 1))
        (Nat.add (Nat.add (ones P.W (Nat.succ I.n)) (ones (Nat.mul P.W (Nat.succ I.n)) (Nat.succ I.n)))
          (ones (Nat.mul (Nat.mul P.W (Nat.succ I.n)) (Nat.succ I.n)) (Nat.succ I.n)))))
      I.cn)
    (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add
        (N14.Box.place I.wB P.W I.B0 (Nat.succ I.n))
        (N14.Box.place I.wB (Nat.mul P.W (Nat.succ I.n)) I.B1 (Nat.succ I.n)))
        (N14.Box.place I.wB (Nat.mul (Nat.mul P.W (Nat.succ I.n)) (Nat.succ I.n)) I.B2 (Nat.succ I.n)))
        I.cp)
      (Nat.mul (Nat.mul I.cM (Nat.shiftLeft 1 (Nat.sub I.aH 1))) (ones P.W (CAP.Bernstein.cube I.n))))
      (Nat.mul I.cK (termsGo P (tpt (Nat.succ I.n)) I.terms 0 0).2))

/-! ## The identity of a pair -/

/-- A share in the identity of a pair: the function of one variable of a slot of a run,
`cM * (Dn * (2 - 2 s) ^ (-1/2) - Ĥ (s)) / c1 + B (s) + (cp - cn) / 3`, with its multiplicity; `cp - cn` is the
constant of the identity of the run, which is divided among its three slots. `Ĥ` is the polynomial of
the table of the slot: its coefficient `d` is slot `d` of `K` (width `Wt`) minus `2 ^ (aHt - 1)`, for
`d ≤ 2 * Dt`. `B` has `n + 1` slots of width `wB`. -/
structure Share where
  mult : Nat
  Wt : Nat
  aHt : Nat
  Dt : Nat
  K : Nat
  Dn : Nat
  B : Nat
  cp : Nat
  cn : Nat

/-- A term of the identity of a pair: the kernel of a part of a list of blocks at the point `(s, s, 1)`
(`pos = 0`), `(s, 1, s)` (`pos = 1`) or `(1, s, s)` (every other value). -/
structure DTerm where
  blocks : List Blk
  sel : Nat
  pos : Nat

/-- The point of a term of the identity of a pair. -/
noncomputable def dpt (T : DTerm) : Pt :=
  Nat.rec (motive := fun _ => Pt) ⟨1, 1, 0⟩
    (fun k _ => Nat.rec (motive := fun _ => Pt) ⟨1, 0, 1⟩ (fun _ _ => ⟨0, 1, 1⟩) k) T.pos

/-- The sum of the kernels of the terms, each at the point that `f` gives, as a pair. -/
noncomputable def dtermsGo (P : Params) (f : DTerm → Pt) : List DTerm → Nat → Nat → Nat × Nat :=
  List.rec (motive := fun _ => Nat → Nat → Nat × Nat) (fun Sp Sn => (Sp, Sn))
    (fun T _ ih Sp Sn =>
      ih (Nat.add Sp (kern P (f T) T.sel T.blocks).1) (Nat.add Sn (kern P (f T) T.sel T.blocks).2))

/-- All terms have blocks of bounded degree (`blocksOk`). -/
noncomputable def dtermsOk (m : Nat) : List DTerm → Bool :=
  List.rec (motive := fun _ => Bool) true (fun T _ ih => blocksOk m T.blocks 0 && ih)

/-- The data of the identity of a pair. -/
structure Id1 where
  n : Nat
  wB : Nat
  aB : Nat
  cM : Nat
  cK : Nat
  c1 : Nat
  shares : List Share
  terms : List DTerm
  /-- the constant of the identity is `kp - kn` -/
  kp : Nat
  kn : Nat
  /-- the sum of the numerators of the Coulomb terms, with multiplicities -/
  fS : Nat

/-- The two sides of the shares at the point `(X, 1, 1)`, and the sum of the numerators of the Coulomb terms:
the state is (positive part, negative part, sum). -/
noncomputable def sharesGo (P : Params) (I : Id1) : List Share → Nat → Nat → Nat → Nat × Nat × Nat :=
  List.rec (motive := fun _ => Nat → Nat → Nat → Nat × Nat × Nat) (fun p q d => (p, q, d))
    (fun S _ ih p q d =>
      ih
        (Nat.add (Nat.add p (Nat.mul (Nat.mul 3 S.mult)
          (Nat.add
            (Nat.mul (Nat.mul I.cM (Nat.shiftLeft 1 (Nat.sub S.aHt 1))) (ones P.W (Nat.succ (Nat.mul 2 S.Dt))))
            (Nat.mul I.c1 (N14.Box.place I.wB P.W S.B (Nat.succ I.n))))))
          (Nat.mul S.mult (Nat.mul I.c1 S.cp)))
        (Nat.add (Nat.add q (Nat.mul (Nat.mul 3 S.mult)
          (Nat.add
            (Nat.mul I.cM (N14.Box.place S.Wt P.W S.K (Nat.succ (Nat.mul 2 S.Dt))))
            (Nat.mul (Nat.mul I.c1 (Nat.shiftLeft 1 (Nat.sub I.aB 1))) (ones P.W (Nat.succ I.n))))))
          (Nat.mul S.mult (Nat.mul I.c1 S.cn)))
        (Nat.add d (Nat.mul S.mult S.Dn)))

/-- Bounds for the sums of the coefficients of the two sides of the shares: the state is (positive part,
negative part). -/
noncomputable def sharesBd (I : Id1) : List Share → Nat → Nat → Nat × Nat :=
  List.rec (motive := fun _ => Nat → Nat → Nat × Nat) (fun p q => (p, q))
    (fun S _ ih p q =>
      ih
        (Nat.add (Nat.add p (Nat.mul (Nat.mul 3 S.mult)
          (Nat.add (Nat.mul (Nat.mul I.cM (Nat.succ (Nat.mul 2 S.Dt))) (Nat.shiftLeft 1 S.aHt))
            (Nat.mul (Nat.mul I.c1 (Nat.succ I.n)) (Nat.shiftLeft 1 I.wB)))))
          (Nat.mul S.mult (Nat.mul I.c1 S.cp)))
        (Nat.add (Nat.add q (Nat.mul (Nat.mul 3 S.mult)
          (Nat.add (Nat.mul (Nat.mul I.cM (Nat.succ (Nat.mul 2 S.Dt))) (Nat.shiftLeft 1 S.Wt))
            (Nat.mul (Nat.mul I.c1 (Nat.succ I.n)) (Nat.shiftLeft 1 I.aB)))))
          (Nat.mul S.mult (Nat.mul I.c1 S.cn))))

/-- The tests of the parameters of the shares. -/
noncomputable def sharesOk (P : Params) (I : Id1) : List Share → Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun S _ ih => Nat.ble 1 S.aHt && Nat.ble S.aHt S.Wt && Nat.ble S.Wt P.W && Nat.ble S.Dt I.n && ih)

/-- The checker of the identity of a pair: with the polynomials `Ĥ_c`, `B_c` and the constants `c_c` of the
shares and their multiplicities `m_c`,

  `∑ c, m_c * (3 * (- cM * Ĥ_c (s) + c1 * B_c (s)) + c1 * (cp_c - cn_c)) + 6 * c1 * cK * ∑ terms (s) = kp - kn`,

and `∑ c, m_c * Dn_c = fS`. -/
noncomputable def id1Ok (P : Params) (I : Id1) : Bool :=
  Nat.ble 1 P.W && Nat.ble 2 P.eb && Nat.ble 1 P.cb && Nat.beq P.D I.n &&
  Nat.ble 1 I.aB && Nat.ble I.aB I.wB && Nat.ble I.wB P.W &&
  dtermsOk (Nat.succ I.n) I.terms && sharesOk P I I.shares &&
  Nat.blt
    (Nat.add (Nat.add (sharesBd I I.shares 0 0).1
      (Nat.mul (Nat.mul (Nat.mul 6 I.c1) I.cK) (dtermsGo P (fun _ => ⟨0, 0, 0⟩) I.terms 0 0).1)) I.kn)
    (Nat.shiftLeft 1 P.W) &&
  Nat.blt
    (Nat.add (Nat.add (sharesBd I I.shares 0 0).2
      (Nat.mul (Nat.mul (Nat.mul 6 I.c1) I.cK) (dtermsGo P (fun _ => ⟨0, 0, 0⟩) I.terms 0 0).2)) I.kp)
    (Nat.shiftLeft 1 P.W) &&
  Nat.beq
    (Nat.add (Nat.add (sharesGo P I I.shares 0 0 0).1
      (Nat.mul (Nat.mul (Nat.mul 6 I.c1) I.cK) (dtermsGo P dpt I.terms 0 0).1)) I.kn)
    (Nat.add (Nat.add (sharesGo P I I.shares 0 0 0).2.1
      (Nat.mul (Nat.mul (Nat.mul 6 I.c1) I.cK) (dtermsGo P dpt I.terms 0 0).2)) I.kp) &&
  Nat.beq (sharesGo P I I.shares 0 0 0).2.2 I.fS

end N14.Ident
