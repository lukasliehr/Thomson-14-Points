module

public import N14.Box.Cover
public import N14.Box.MasterKernel

/-!
# T7, the slack on a domain: the theorem of a run whose groups cover arbitrary boxes

**Theorem** (`run_sound_master`). Let the parameters of a run and the tables of its three coordinates be
accepted, let the kernel accept the master tree of a list of boxes (`masterOk`), and let every box of the list be
covered by an accepted group (`BoxDone`, i.e. `boxOk`). Then

  `0 ≤ M(x) + U₁(x₁) + U₂(x₂) + U₃(x₃)`

at every point `x` of `[-1, 1)³` in the domain of the run (`Dom`). The statement is that of `run_sound`; only the
packaging of the certificate differs: a group is the cover of an arbitrary box, not a range of boxes of the grid.

`box_sound`: an accepted group gives the statement of the cells at the points of its box (`cover_sound`).
`master_sound`: an accepted master tree of a box gives, at the points of the box, every statement that holds on
the boxes of the list; a leaf that is not in the list violates a cut at all of its points.
`AllDone`, with `allDone_cons` and `allDone_append`: the list of the boxes of a statement module, assembled from
the theorems of the groups.
-/

@[expose] public section

namespace N14.Box

open CAP CAP.Bernstein

/-- The point lies in the box. -/
def InBx (b : Bx) (x1 x2 x3 : ℝ) : Prop := InI b.e1 b.c1 x1 ∧ InI b.e2 b.c2 x2 ∧ InI b.e3 b.c3 x3

/-- The box is covered by a group that the checker accepts. -/
def BoxDone (R : Run) (b : Bx) : Prop := ∃ s l, boxOk R b s l = true

/-- **A group.** A statement that holds on every accepted cell at the points of the domain holds at all points
of the domain in the box of an accepted group. -/
theorem box_sound (R : Run) (hvd : ∀ c ∈ R.cuts, 1 ≤ c.vd) (Q : ℝ → ℝ → ℝ → Prop)
    (hcell : ∀ c : Cell, cellOk R c = true → ∀ x1 x2 x3 : ℝ, InIv (ent R.t1 c.i) x1 → InIv (ent R.t2 c.j) x2 →
      InIv (ent R.t3 c.k) x3 → Dom R x1 x2 x3 → Q x1 x2 x3)
    (b : Bx) (h : BoxDone R b) (x1 x2 x3 : ℝ) (hx : InBx b x1 x2 x3) (hD : Dom R x1 x2 x3) : Q x1 x2 x3 := by
  obtain ⟨s, l, h⟩ := h
  exact (cover_sound R hvd Q hcell R.fuel s b.e1 b.c1 b.e2 b.c2 b.e3 b.c3 l _ h).1 x1 x2 x3 hx.1 hx.2.1 hx.2.2 hD

theorem master_succ (R : Run) (f s e1 c1 e2 c2 e3 c3 : ℕ) (l : List Bx) (k : ℕ → List Bx → Bool) :
    master R (f + 1) s e1 c1 e2 c2 e3 c3 l k =
      Nat.rec (motive := fun _ => Bool)
        (master R f (Nat.shiftRight s 2) (Nat.succ e1) (Nat.mul 2 c1) e2 c2 e3 c3 l
          (fun s' l' => master R f s' (Nat.succ e1) (Nat.succ (Nat.mul 2 c1)) e2 c2 e3 c3 l' k))
        (fun t _ => Nat.rec (motive := fun _ => Bool)
          (master R f (Nat.shiftRight s 2) e1 c1 (Nat.succ e2) (Nat.mul 2 c2) e3 c3 l
            (fun s' l' => master R f s' e1 c1 (Nat.succ e2) (Nat.succ (Nat.mul 2 c2)) e3 c3 l' k))
          (fun t' _ => Nat.rec (motive := fun _ => Bool)
            (master R f (Nat.shiftRight s 2) e1 c1 e2 c2 (Nat.succ e3) (Nat.mul 2 c3) l
              (fun s' l' => master R f s' e1 c1 e2 c2 (Nat.succ e3) (Nat.succ (Nat.mul 2 c3)) l' k))
            (fun _ _ =>
              Bool.rec (motive := fun _ => Bool)
                (List.rec (motive := fun _ => Bool) false
                  (fun b rest _ => bxIs b e1 c1 e2 c2 e3 c3 && k (Nat.shiftRight s 2) rest) l)
                (k (Nat.shiftRight s 2) l)
                (boxOut e1 c1 e2 c2 e3 c3 R.cuts))
            t')
          t)
        (Nat.land s 3) := rfl

/-- **The master tree of a box.** If the checker accepts the master tree of a box for a list of boxes, a
statement that holds on every box of the list at the points of the domain holds at all points of the domain in
the box; the test of the rest is accepted, and the statement holds on the boxes of the rest of the list. -/
theorem master_sound (R : Run) (hvd : ∀ c ∈ R.cuts, 1 ≤ c.vd) (Q : ℝ → ℝ → ℝ → Prop) :
    ∀ (fuel s e1 c1 e2 c2 e3 c3 : ℕ) (l : List Bx) (k : ℕ → List Bx → Bool),
      master R fuel s e1 c1 e2 c2 e3 c3 l k = true →
      (∀ b ∈ l, ∀ x1 x2 x3 : ℝ, InBx b x1 x2 x3 → Dom R x1 x2 x3 → Q x1 x2 x3) →
      (∀ x1 x2 x3 : ℝ, InI e1 c1 x1 → InI e2 c2 x2 → InI e3 c3 x3 → Dom R x1 x2 x3 → Q x1 x2 x3) ∧
        ∃ s' l', k s' l' = true ∧
          ∀ b ∈ l', ∀ x1 x2 x3 : ℝ, InBx b x1 x2 x3 → Dom R x1 x2 x3 → Q x1 x2 x3 := by
  intro fuel
  induction fuel with
  | zero =>
    intro s e1 c1 e2 c2 e3 c3 l k h
    exact absurd (show false = true from h) (by decide)
  | succ f ih =>
    intro s e1 c1 e2 c2 e3 c3 l k h hgood
    rw [master_succ] at h
    generalize Nat.land s 3 = t at h
    rcases t with _ | _ | _ | t
    · have h0 : master R f (Nat.shiftRight s 2) (e1 + 1) (2 * c1) e2 c2 e3 c3 l
          (fun s' l' => master R f s' (e1 + 1) (2 * c1 + 1) e2 c2 e3 c3 l' k) = true := h
      obtain ⟨gl, s1, l1, h1, hg1⟩ := ih _ _ _ _ _ _ _ _ _ h0 hgood
      obtain ⟨gr, s2, l2, h2, hg2⟩ := ih _ _ _ _ _ _ _ _ _ h1 hg1
      refine ⟨fun x1 x2 x3 hx1 hx2 hx3 hD => ?_, s2, l2, h2, hg2⟩
      rcases InI_split e1 c1 x1 hx1 with hL | hR
      · exact gl x1 x2 x3 hL hx2 hx3 hD
      · exact gr x1 x2 x3 hR hx2 hx3 hD
    · have h0 : master R f (Nat.shiftRight s 2) e1 c1 (e2 + 1) (2 * c2) e3 c3 l
          (fun s' l' => master R f s' e1 c1 (e2 + 1) (2 * c2 + 1) e3 c3 l' k) = true := h
      obtain ⟨gl, s1, l1, h1, hg1⟩ := ih _ _ _ _ _ _ _ _ _ h0 hgood
      obtain ⟨gr, s2, l2, h2, hg2⟩ := ih _ _ _ _ _ _ _ _ _ h1 hg1
      refine ⟨fun x1 x2 x3 hx1 hx2 hx3 hD => ?_, s2, l2, h2, hg2⟩
      rcases InI_split e2 c2 x2 hx2 with hL | hR
      · exact gl x1 x2 x3 hx1 hL hx3 hD
      · exact gr x1 x2 x3 hx1 hR hx3 hD
    · have h0 : master R f (Nat.shiftRight s 2) e1 c1 e2 c2 (e3 + 1) (2 * c3) l
          (fun s' l' => master R f s' e1 c1 e2 c2 (e3 + 1) (2 * c3 + 1) l' k) = true := h
      obtain ⟨gl, s1, l1, h1, hg1⟩ := ih _ _ _ _ _ _ _ _ _ h0 hgood
      obtain ⟨gr, s2, l2, h2, hg2⟩ := ih _ _ _ _ _ _ _ _ _ h1 hg1
      refine ⟨fun x1 x2 x3 hx1 hx2 hx3 hD => ?_, s2, l2, h2, hg2⟩
      rcases InI_split e3 c3 x3 hx3 with hL | hR
      · exact gl x1 x2 x3 hx1 hx2 hL hD
      · exact gr x1 x2 x3 hx1 hx2 hR hD
    · have h0 : Bool.rec (motive := fun _ => Bool)
          (List.rec (motive := fun _ => Bool) false
            (fun b rest _ => bxIs b e1 c1 e2 c2 e3 c3 && k (Nat.shiftRight s 2) rest) l)
          (k (Nat.shiftRight s 2) l) (boxOut e1 c1 e2 c2 e3 c3 R.cuts) = true := h
      cases hb : boxOut e1 c1 e2 c2 e3 c3 R.cuts with
      | true =>
        rw [hb] at h0
        refine ⟨fun x1 x2 x3 hx1 hx2 hx3 hD => ?_, _, _, h0, hgood⟩
        obtain ⟨c, hc, hv⟩ := boxOut_sound e1 c1 e2 c2 e3 c3 R.cuts hvd hb x1 x2 x3 hx1 hx2 hx3
        have := hD.2.2.2.2.1 c hc
        linarith
      | false =>
        rw [hb] at h0
        cases l with
        | nil => exact absurd (show false = true from h0) (by decide)
        | cons b rest =>
          have h1 : (bxIs b e1 c1 e2 c2 e3 c3 && k (Nat.shiftRight s 2) rest) = true := h0
          rw [Bool.and_eq_true] at h1
          obtain ⟨his, hk⟩ := h1
          have his' : (Nat.beq b.e1 e1 && Nat.beq b.c1 c1 && Nat.beq b.e2 e2 && Nat.beq b.c2 c2
              && Nat.beq b.e3 e3 && Nat.beq b.c3 c3) = true := his
          simp only [Bool.and_eq_true] at his'
          obtain ⟨⟨⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, a5⟩, a6⟩ := his'
          refine ⟨fun x1 x2 x3 hx1 hx2 hx3 hD => ?_, _, _, hk,
            fun b' hb' => hgood b' (List.mem_cons_of_mem _ hb')⟩
          refine hgood b List.mem_cons_self x1 x2 x3 ⟨?_, ?_, ?_⟩ hD
          · rw [Nat.eq_of_beq_eq_true a1, Nat.eq_of_beq_eq_true a2]
            exact hx1
          · rw [Nat.eq_of_beq_eq_true a3, Nat.eq_of_beq_eq_true a4]
            exact hx2
          · rw [Nat.eq_of_beq_eq_true a5, Nat.eq_of_beq_eq_true a6]
            exact hx3

/-- **The master trees of the boxes of the grid.** -/
theorem masterGo_sound (R : Run) (hvd : ∀ c ∈ R.cuts, 1 ≤ c.vd) (Q : ℝ → ℝ → ℝ → Prop) (lv : ℕ) :
    ∀ (cnt b s : ℕ) (l : List Bx), masterGo R lv cnt b s l = true →
      (∀ bx ∈ l, ∀ x1 x2 x3 : ℝ, InBx bx x1 x2 x3 → Dom R x1 x2 x3 → Q x1 x2 x3) →
      ∀ b', b ≤ b' → b' < b + cnt → ∀ x1 x2 x3 : ℝ, InGrid lv b' x1 x2 x3 → Dom R x1 x2 x3 → Q x1 x2 x3 := by
  intro cnt
  induction cnt with
  | zero =>
    intro b s l _ _ b' h1 h2
    omega
  | succ cnt ih =>
    intro b s l h hgood b' h1 h2 x1 x2 x3 hx hD
    have h0 : master R R.fuel s lv (b / ((2 <<< lv) * (2 <<< lv))) lv (b / (2 <<< lv) % (2 <<< lv)) lv
        (b % (2 <<< lv)) l (fun s' l' => masterGo R lv cnt (b + 1) s' l') = true := h
    obtain ⟨g, s1, l1, hrest, hg1⟩ := master_sound R hvd Q _ _ _ _ _ _ _ _ _ _ h0 hgood
    rcases Nat.eq_or_lt_of_le h1 with rfl | hlt
    · exact g x1 x2 x3 hx.1 hx.2.1 hx.2.2 hD
    · exact ih (b + 1) s1 l1 hrest hg1 b' hlt (by omega) x1 x2 x3 hx hD

/-- All boxes of the list are covered by accepted groups. -/
def AllDone (R : Run) (l : List Bx) : Prop := ∀ b ∈ l, BoxDone R b

theorem allDone_nil (R : Run) : AllDone R [] := fun _ h => absurd h List.not_mem_nil

/-- An accepted group of the box `b` before the boxes of `l`. -/
theorem allDone_cons {R : Run} {b : Bx} {l : List Bx} {s : ℕ} {cells : List Cell}
    (h : boxOk R b s cells = true) (rest : AllDone R l) : AllDone R (b :: l) := by
  intro b' hb'
  rcases List.mem_cons.mp hb' with rfl | hl
  · exact ⟨s, cells, h⟩
  · exact rest b' hl

theorem allDone_append {R : Run} {l1 l2 : List Bx} (h1 : AllDone R l1) (h2 : AllDone R l2) :
    AllDone R (l1 ++ l2) := by
  intro b hb
  rcases List.mem_append.mp hb with h | h
  · exact h1 b h
  · exact h2 b h

/-- **The theorem of a run whose groups cover arbitrary boxes.** -/
theorem run_sound_master (R : Run) (hR : runOk R = true) (U1 U2 U3 : Tab)
    (hU1 : U1.P.W = R.W ∧ U1.n = R.n) (hU2 : U2.P.W = R.W ∧ U2.n = R.n) (hU3 : U3.P.W = R.W ∧ U3.n = R.n)
    (ht1 : tableOk U1 R.t1 = true) (ht2 : tableOk U2 R.t2 = true) (ht3 : tableOk U3 R.t3 = true)
    (lv s : ℕ) (boxes : List Bx) (hm : masterOk R lv s boxes = true) (hdone : AllDone R boxes)
    (x1 x2 x3 : ℝ) (h1 : -1 ≤ x1) (h2 : -1 ≤ x2) (h3 : -1 ≤ x3) (hD : Dom R x1 x2 x3) :
    0 ≤ slackFn R U1 U2 U3 x1 x2 x3 := by
  have hfit := runOk_fit R hR
  have hvd : ∀ c ∈ R.cuts, 1 ≤ c.vd := by
    intro c hc
    have h := hfit.cuts c hc
    have h' : (Nat.ble 1 c.vd
        && Nat.beq ((c.vn * (1 <<< R.sg)) / c.vd * c.vd) (c.vn * (1 <<< R.sg))
        && Nat.ble c.vn (2 * c.vd)) = true := h
    rw [Bool.and_eq_true, Bool.and_eq_true, Nat.ble_eq] at h'
    exact h'.1.1
  obtain ⟨b, hb, hx⟩ := grid3 lv x1 x2 x3 h1 hD.1.le h2 hD.2.1.le h3 hD.2.2.1.le
  have hcell := cell_slack R hfit U1 U2 U3 hU1 hU2 hU3 (table_sound U1 R.t1 ht1) (table_sound U2 R.t2 ht2)
    (table_sound U3 R.t3 ht3)
  have hm' : masterGo R lv ((2 <<< lv) * (2 <<< lv) * (2 <<< lv)) 0 s boxes = true := hm
  exact masterGo_sound R hvd (fun y1 y2 y3 => 0 ≤ slackFn R U1 U2 U3 y1 y2 y3) lv _ 0 s boxes hm'
    (fun bx hbx y1 y2 y3 hy hDy =>
      box_sound R hvd (fun y1 y2 y3 => 0 ≤ slackFn R U1 U2 U3 y1 y2 y3) hcell bx (hdone bx hbx) y1 y2 y3 hy hDy)
    b (Nat.zero_le b) (by omega) x1 x2 x3 hx hD

end N14.Box
