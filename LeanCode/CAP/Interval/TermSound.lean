module

public import CAP.Interval.Sound
public import CAP.Interval.Term

/-!
# E6, interval arithmetic: soundness of the expressions of registers

**Theorem** (`CAP.Interval.agrees_sound`). If `agrees prog env.length t i = true`, then the number
of register `i` of the program for the inputs `env` is the value `t.eval P env` of the tree `t`.

In a statement module the value of a tree is unfolded once by `simp only [Tm.eval]`. The proof by
rewriting with the definitions of `sem` and `den` needs a number of steps that is quadratic in the
length of the program.
-/

@[expose] public section

namespace CAP.Interval

/-- The value of an expression for the inputs `env`. -/
noncomputable def Tm.eval (P : Params) (env : List ℝ) : Tm → ℝ
  | .var i => env.getD i 0
  | .nat n => n
  | .cst b => ((b : ℝ) - 2 ^ (P.W - 1)) / 2 ^ P.p
  | .add a b => a.eval P env + b.eval P env
  | .sub a b => a.eval P env - b.eval P env
  | .mul a b => a.eval P env * b.eval P env
  | .inv a => (a.eval P env)⁻¹
  | .sqrt a => Real.sqrt (a.eval P env)

theorem nth_nil (i : ℕ) : nth i [] = .nat 0 := by cases i <;> rfl

theorem sem_cons (P : Params) (a : Instr) (p : List Instr) (regs : List ℝ) :
    sem P (a :: p) regs = sem P p (regs ++ [den P regs a]) := rfl

/-- A program appends registers. -/
theorem sem_extends (P : Params) : ∀ (p : List Instr) (regs : List ℝ), ∃ l, sem P p regs = regs ++ l
  | [], regs => ⟨[], (List.append_nil regs).symm⟩
  | a :: p, regs => by
    obtain ⟨l, hl⟩ := sem_extends P p (regs ++ [den P regs a])
    exact ⟨den P regs a :: l, by rw [sem_cons, hl, List.append_assoc]; rfl⟩

theorem getD_take_lt (l : List ℝ) (i j : ℕ) (h : j < i) : (l.take i).getD j 0 = l.getD j 0 := by
  simp [List.getD_eq_getElem?_getD, h]

/-- Register `regs.length + i` is defined by instruction `i` and the registers before it. -/
theorem sem_getD (P : Params) : ∀ (p : List Instr) (regs : List ℝ) (i : ℕ),
    (sem P p regs).getD (regs.length + i) 0 =
      den P ((sem P p regs).take (regs.length + i)) (nth i p)
  | [], regs, i => by
    rw [nth_nil]
    show regs.getD (regs.length + i) 0 = ((0 : ℕ) : ℝ)
    simp [List.getD_eq_getElem?_getD]
  | a :: p, regs, 0 => by
    obtain ⟨l, hl⟩ := sem_extends P p (regs ++ [den P regs a])
    have e : ((regs ++ [den P regs a]) ++ l).take regs.length = regs := by
      rw [List.append_assoc]
      simp
    show (sem P p (regs ++ [den P regs a])).getD (regs.length + 0) 0 =
      den P ((sem P p (regs ++ [den P regs a])).take (regs.length + 0)) a
    rw [hl, Nat.add_zero, e, getD_append_lt _ _ _ _ (by simp), getD_append_length]
  | a :: p, regs, i + 1 => by
    have h := sem_getD P p (regs ++ [den P regs a]) i
    rw [List.length_append, List.length_singleton, Nat.add_assoc, Nat.add_comm 1 i] at h
    exact h

theorem isNat_true {n : ℕ} {ins : Instr} (h : isNat n ins = true) : ins = .nat n := by
  cases ins with
  | nat m => exact congrArg Instr.nat (Nat.eq_of_beq_eq_true h)
  | _ => exact Bool.noConfusion h

theorem isCst_true {b : ℕ} {ins : Instr} (h : isCst b ins = true) : ins = .cst b := by
  cases ins with
  | cst c => exact congrArg Instr.cst (Nat.eq_of_beq_eq_true h)
  | _ => exact Bool.noConfusion h

theorem isAdd_true {f : ℕ → ℕ → Bool} {ins : Instr} (h : isAdd f ins = true) :
    ∃ j k, ins = .add j k ∧ f j k = true := by
  cases ins with
  | add j k => exact ⟨j, k, rfl, h⟩
  | _ => exact Bool.noConfusion h

theorem isSub_true {f : ℕ → ℕ → Bool} {ins : Instr} (h : isSub f ins = true) :
    ∃ j k, ins = .sub j k ∧ f j k = true := by
  cases ins with
  | sub j k => exact ⟨j, k, rfl, h⟩
  | _ => exact Bool.noConfusion h

theorem isMul_true {f : ℕ → ℕ → Bool} {ins : Instr} (h : isMul f ins = true) :
    ∃ j k, ins = .mul j k ∧ f j k = true := by
  cases ins with
  | mul j k => exact ⟨j, k, rfl, h⟩
  | _ => exact Bool.noConfusion h

theorem isInv_true {f : ℕ → Bool} {ins : Instr} (h : isInv f ins = true) :
    ∃ j, ins = .inv j ∧ f j = true := by
  cases ins with
  | inv j => exact ⟨j, rfl, h⟩
  | _ => exact Bool.noConfusion h

theorem isSqrt_true {f : ℕ → Bool} {ins : Instr} (h : isSqrt f ins = true) :
    ∃ j, ins = .sqrt j ∧ f j = true := by
  cases ins with
  | sqrt j => exact ⟨j, rfl, h⟩
  | _ => exact Bool.noConfusion h

theorem both_true {fa fb : ℕ → Bool} {i j k : ℕ} (h : both fa fb i j k = true) :
    j < i ∧ k < i ∧ fa j = true ∧ fb k = true := by
  have h' : (Nat.blt j i && (Nat.blt k i && (fa j && fb k))) = true := h
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Nat.blt_eq, Nat.blt_eq] at h'
  exact h'

theorem one_true {fa : ℕ → Bool} {i j : ℕ} (h : one fa i j = true) : j < i ∧ fa j = true := by
  have h' : (Nat.blt j i && fa j) = true := h
  rw [Bool.and_eq_true, Nat.blt_eq] at h'
  exact h'

/-- **Soundness of the expressions.** -/
theorem agrees_sound (P : Params) (prog : List Instr) (env : List ℝ) : ∀ (t : Tm) (i : ℕ),
    agrees prog env.length t i = true → (sem P prog env).getD i 0 = t.eval P env := by
  have key : ∀ i, env.length ≤ i → (sem P prog env).getD i 0 =
      den P ((sem P prog env).take i) (nth (i - env.length) prog) := by
    intro i hi
    have h := sem_getD P prog env (i - env.length)
    rwa [Nat.add_sub_cancel' hi] at h
  have opnd : ∀ {i j : ℕ}, j < i → ((sem P prog env).take i).getD j 0 = (sem P prog env).getD j 0 :=
    fun h => getD_take_lt _ _ _ h
  intro t
  induction t with
  | var k =>
    intro i h
    have h' : (Nat.beq i k && Nat.blt k env.length) = true := h
    rw [Bool.and_eq_true, Nat.blt_eq] at h'
    obtain ⟨hik, hk⟩ := h'
    have e : i = k := Nat.eq_of_beq_eq_true hik
    subst e
    obtain ⟨l, hl⟩ := sem_extends P prog env
    rw [hl, getD_append_lt _ _ _ _ hk]
    rfl
  | nat n =>
    intro i h
    have h' : (Nat.ble env.length i && isNat n (nth (i - env.length) prog)) = true := h
    rw [Bool.and_eq_true, Nat.ble_eq] at h'
    rw [key i h'.1, isNat_true h'.2]
    rfl
  | cst b =>
    intro i h
    have h' : (Nat.ble env.length i && isCst b (nth (i - env.length) prog)) = true := h
    rw [Bool.and_eq_true, Nat.ble_eq] at h'
    rw [key i h'.1, isCst_true h'.2]
    rfl
  | add a b iha ihb =>
    intro i h
    have h' : (Nat.ble env.length i && isAdd (both (agrees prog env.length a) (agrees prog env.length b) i)
      (nth (i - env.length) prog)) = true := h
    rw [Bool.and_eq_true, Nat.ble_eq] at h'
    obtain ⟨j, k, hins, hjk⟩ := isAdd_true h'.2
    obtain ⟨hj, hk, ha, hb⟩ := both_true hjk
    rw [key i h'.1, hins]
    show ((sem P prog env).take i).getD j 0 + ((sem P prog env).take i).getD k 0 = a.eval P env + b.eval P env
    rw [opnd hj, opnd hk, iha j ha, ihb k hb]
  | sub a b iha ihb =>
    intro i h
    have h' : (Nat.ble env.length i && isSub (both (agrees prog env.length a) (agrees prog env.length b) i)
      (nth (i - env.length) prog)) = true := h
    rw [Bool.and_eq_true, Nat.ble_eq] at h'
    obtain ⟨j, k, hins, hjk⟩ := isSub_true h'.2
    obtain ⟨hj, hk, ha, hb⟩ := both_true hjk
    rw [key i h'.1, hins]
    show ((sem P prog env).take i).getD j 0 - ((sem P prog env).take i).getD k 0 = a.eval P env - b.eval P env
    rw [opnd hj, opnd hk, iha j ha, ihb k hb]
  | mul a b iha ihb =>
    intro i h
    have h' : (Nat.ble env.length i && isMul (both (agrees prog env.length a) (agrees prog env.length b) i)
      (nth (i - env.length) prog)) = true := h
    rw [Bool.and_eq_true, Nat.ble_eq] at h'
    obtain ⟨j, k, hins, hjk⟩ := isMul_true h'.2
    obtain ⟨hj, hk, ha, hb⟩ := both_true hjk
    rw [key i h'.1, hins]
    show ((sem P prog env).take i).getD j 0 * ((sem P prog env).take i).getD k 0 = a.eval P env * b.eval P env
    rw [opnd hj, opnd hk, iha j ha, ihb k hb]
  | inv a iha =>
    intro i h
    have h' : (Nat.ble env.length i && isInv (one (agrees prog env.length a) i)
      (nth (i - env.length) prog)) = true := h
    rw [Bool.and_eq_true, Nat.ble_eq] at h'
    obtain ⟨j, hins, hj'⟩ := isInv_true h'.2
    obtain ⟨hj, ha⟩ := one_true hj'
    rw [key i h'.1, hins]
    show (((sem P prog env).take i).getD j 0)⁻¹ = (a.eval P env)⁻¹
    rw [opnd hj, iha j ha]
  | sqrt a iha =>
    intro i h
    have h' : (Nat.ble env.length i && isSqrt (one (agrees prog env.length a) i)
      (nth (i - env.length) prog)) = true := h
    rw [Bool.and_eq_true, Nat.ble_eq] at h'
    obtain ⟨j, hins, hj'⟩ := isSqrt_true h'.2
    obtain ⟨hj, ha⟩ := one_true hj'
    rw [key i h'.1, hins]
    show Real.sqrt (((sem P prog env).take i).getD j 0) = Real.sqrt (a.eval P env)
    rw [opnd hj, iha j ha]

end CAP.Interval
