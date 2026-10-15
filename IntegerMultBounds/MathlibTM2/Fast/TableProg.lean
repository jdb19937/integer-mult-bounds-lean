module

public import IntegerMultBounds.MathlibTM2.Fast.TableVM

/-!
# Reasoning about table programs

`TblDo A W w c st Post K`: from the state `st`, the program `c` terminates (`TblBig`) in a state
satisfying `Post` after at most `K` atoms.

## Rules

* `TblDo.ins`, `TblDo.seq`, `TblDo.iteT`, `TblDo.iteF`, `TblDo.mono`;
* `TblDo.loop`: a `while` loop with an invariant `Inv j` before iteration `j < N`, at most `Kb`
  atoms per iteration, `N (Kb + 2) + 2` atoms in all; `TblDo.for` for the counting loop
  `tblFor i nv body`, `1 + N (Kb + 3) + 2` atoms;
* straight-line code: `tblStraight`, `tblRunList`, `TblDo.straight`. Without overflow
  (`TblIns.fits`, `tblFitsList`) the instructions act in exact natural arithmetic
  (`TblIns.exact`, `tblExactList`, `TblIns.run_eq_exact`, `tblRunList_eq_exact`), which gives
  `TblDo.straightX`, `TblDo.insX` and `TblDo.block` for `tblBlock n l i` (the list `l`, then `i`);
* renaming: `TblCode.rename f` runs a program on the variables `f` of a larger state, and
  `TblDo.rename` transfers its contract, every other variable unchanged.

## Macros

* `tblConstL c k`: `c := k` by `k` increments (`tblExactList_const`, `tblFitsList_const`);
* `tblPow2 c e i`: `c := 2 ^ e` by doublings (`tblPow2_do`, `4 e + 5` atoms);
* `tblSignedL`: a natural number `tblSignedVal w neg mg` congruent to `±mg` modulo `2 ^ w`
  (`tblSignedVal_cast`), for emitting signed coefficients.

## The host

`TblDo.host`: a terminating program runs on the host within `K · tblC W w` steps
(`tblCompile_runs`). `tblHost rg c out` is `tblCompile rg c` followed by moving `acc` onto the
output register `out`; `tblHost_runs`: `out` gains the emitted symbols in emission order, within
`K · tblC W w + 2 |acc| + 2` steps.
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Fast.TableVM

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Layer

set_option linter.unusedSimpArgs false

/-! ### The rules -/

section Rules

variable {n A W w : ℕ}

/-- From `st`, `c` terminates in a state satisfying `Post` within `K` atoms. -/
def TblDo (A W w : ℕ) (c : TblCode n) (st : TblSt n A) (Post : TblSt n A → Prop) (K : ℕ) :
    Prop :=
  ∃ st' k, TblBig A W w c st st' k ∧ Post st' ∧ k ≤ K

theorem TblDo.mono {c : TblCode n} {st : TblSt n A} {P P' : TblSt n A → Prop} {K K' : ℕ}
    (h : TblDo A W w c st P K) (hP : ∀ s, P s → P' s) (hK : K ≤ K') : TblDo A W w c st P' K' := by
  obtain ⟨st', k, hb, hp, hk⟩ := h
  exact ⟨st', k, hb, hP _ hp, hk.trans hK⟩

theorem TblDo.ins (i : TblIns n) {st : TblSt n A} {P : TblSt n A → Prop}
    (h : P (i.run A W w st)) : TblDo A W w (.ins i) st P 1 :=
  ⟨_, 1, .ins i st, h, le_rfl⟩

theorem TblDo.seq {c d : TblCode n} {st : TblSt n A} {P₁ P₂ : TblSt n A → Prop} {K₁ K₂ : ℕ}
    (h₁ : TblDo A W w c st P₁ K₁) (h₂ : ∀ s, P₁ s → TblDo A W w d s P₂ K₂) :
    TblDo A W w (.seq c d) st P₂ (K₁ + K₂) := by
  obtain ⟨s₁, k₁, hb₁, hp₁, hk₁⟩ := h₁
  obtain ⟨s₂, k₂, hb₂, hp₂, hk₂⟩ := h₂ s₁ hp₁
  exact ⟨s₂, k₁ + k₂, .seq hb₁ hb₂, hp₂, by omega⟩

theorem TblDo.iteT {a b : Fin n} {c d : TblCode n} {st : TblSt n A} {P : TblSt n A → Prop}
    {K : ℕ} (hlt : st.val a < st.val b) (h : TblDo A W w c st P K) :
    TblDo A W w (.ite a b c d) st P (K + 1) := by
  obtain ⟨s, k, hb, hp, hk⟩ := h
  exact ⟨s, k + 1, .iteT hlt hb, hp, by omega⟩

theorem TblDo.iteF {a b : Fin n} {c d : TblCode n} {st : TblSt n A} {P : TblSt n A → Prop}
    {K : ℕ} (hlt : ¬ st.val a < st.val b) (h : TblDo A W w d st P K) :
    TblDo A W w (.ite a b c d) st P (K + 1) := by
  obtain ⟨s, k, hb, hp, hk⟩ := h
  exact ⟨s, k + 1, .iteF hlt hb, hp, by omega⟩

/-- A `while` loop with an invariant `Inv j` before iteration `j`. -/
theorem TblDo.loop {a b : Fin n} {c : TblCode n} {st : TblSt n A} {P : TblSt n A → Prop}
    (Inv : ℕ → TblSt n A → Prop) (N Kb : ℕ) (h0 : Inv 0 st)
    (hstep : ∀ j < N, ∀ s, Inv j s → s.val a < s.val b ∧ TblDo A W w c s (Inv (j + 1)) Kb)
    (hend : ∀ s, Inv N s → ¬ s.val a < s.val b ∧ P s) :
    TblDo A W w (.loop a b c) st P (N * (Kb + 2) + 2) := by
  have key : ∀ r j s, j + r = N → Inv j s → TblDo A W w (.loop a b c) s P (r * (Kb + 2) + 2) := by
    intro r
    induction r with
    | zero =>
      intro j s hj hs
      subst hj
      obtain ⟨hlt, hp⟩ := hend s (by simpa using hs)
      exact ⟨s, 2, .loopF hlt, hp, by omega⟩
    | succ r ih =>
      intro j s hj hs
      obtain ⟨hlt, s₁, k₁, hb₁, hi₁, hk₁⟩ := hstep j (by omega) s hs
      obtain ⟨s₂, k₂, hb₂, hp₂, hk₂⟩ := ih (j + 1) s₁ (by omega) hi₁
      exact ⟨s₂, k₁ + k₂ + 2, .loopT hlt hb₁ hb₂, hp₂, by nlinarith⟩
  exact key N 0 st (by omega) h0

/-- A straight-line block of instructions. -/
def tblStraight (n : ℕ) : List (TblIns n) → TblCode n → TblCode n
  | [], c => c
  | i :: l, c => .seq (.ins i) (tblStraight n l c)

/-- The effect of a list of instructions. -/
def tblRunList (A W w : ℕ) : List (TblIns n) → TblSt n A → TblSt n A
  | [], st => st
  | i :: l, st => tblRunList A W w l (i.run A W w st)

theorem TblDo.straight (l : List (TblIns n)) {c : TblCode n} {st : TblSt n A}
    {P : TblSt n A → Prop} {K : ℕ} (h : TblDo A W w c (tblRunList A W w l st) P K) :
    TblDo A W w (tblStraight n l c) st P (l.length + K) := by
  induction l generalizing st with
  | nil => simpa [tblStraight, tblRunList] using h
  | cons i l ih =>
    have := (TblDo.ins (W := W) (w := w) i (st := st) (P := (· = i.run A W w st)) rfl).seq
      (fun s hs => hs ▸ ih h)
    exact this.mono (fun _ h => h) (by simp; omega)

end Rules

/-! ### Exact evaluation -/

section Exact

variable {n A W w : ℕ}

/-- The effect of an instruction in exact natural arithmetic (truncated subtraction). -/
def TblIns.exact {n : ℕ} (A w : ℕ) : TblIns n → TblSt n A → TblSt n A
  | .add a b c, st => ⟨Function.update st.val c (st.val a + st.val b), st.acc⟩
  | .sub a b c, st => ⟨Function.update st.val c (st.val a - st.val b), st.acc⟩
  | .mul a b c, st => ⟨Function.update st.val c (st.val a * st.val b), st.acc⟩
  | .div a b c, st => ⟨Function.update st.val c (st.val a / st.val b), st.acc⟩
  | .mod a b c, st => ⟨Function.update st.val c (st.val a % st.val b), st.acc⟩
  | .copy a c, st => ⟨Function.update st.val c (st.val a), st.acc⟩
  | .zero c, st => ⟨Function.update st.val c 0, st.acc⟩
  | .inc c, st => ⟨Function.update st.val c (st.val c + 1), st.acc⟩
  | .emit a b, st => ⟨st.val, (tblPairs A w (st.val a) (st.val b)).reverse ++ st.acc⟩

/-- No overflow in one instruction. -/
def TblIns.fits {n : ℕ} (A W : ℕ) : TblIns n → TblSt n A → Prop
  | .add a b _, st => st.val a + st.val b < 2 ^ W
  | .sub a b _, st => st.val b ≤ st.val a ∧ st.val a < 2 ^ W
  | .mul a b _, st => st.val a * st.val b < 2 ^ W
  | .inc c, st => st.val c + 1 < 2 ^ W
  | _, _ => True

theorem TblIns.run_eq_exact (i : TblIns n) (st : TblSt n A) (h : i.fits A W st) :
    i.run A W w st = i.exact A w st := by
  cases i with
  | add a b c => simp only [TblIns.run, TblIns.exact, Nat.mod_eq_of_lt h]
  | sub a b c =>
    simp only [TblIns.fits] at h
    simp only [TblIns.run, TblIns.exact]
    rw [show st.val a + 2 ^ W - st.val b = (st.val a - st.val b) + 2 ^ W by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega)]
  | mul a b c => simp only [TblIns.run, TblIns.exact, Nat.mod_eq_of_lt h]
  | div a b c => rfl
  | mod a b c => rfl
  | copy a c => rfl
  | zero c => rfl
  | inc c => simp only [TblIns.run, TblIns.exact, Nat.mod_eq_of_lt h]
  | emit a b => rfl

/-- Exact evaluation of a list of instructions. -/
def tblExactList (A w : ℕ) : List (TblIns n) → TblSt n A → TblSt n A
  | [], st => st
  | i :: l, st => tblExactList A w l (i.exact A w st)

/-- No overflow along a list of instructions. -/
def tblFitsList (A W w : ℕ) : List (TblIns n) → TblSt n A → Prop
  | [], _ => True
  | i :: l, st => i.fits A W st ∧ tblFitsList A W w l (i.exact A w st)

theorem tblRunList_eq_exact (l : List (TblIns n)) (st : TblSt n A) (h : tblFitsList A W w l st) :
    tblRunList A W w l st = tblExactList A w l st := by
  induction l generalizing st with
  | nil => rfl
  | cons i l ih =>
    simp only [tblFitsList] at h
    simp only [tblRunList, tblExactList, TblIns.run_eq_exact i st h.1, ih _ h.2]

/-- A straight-line block without overflow runs in exact arithmetic. -/
theorem TblDo.straightX (l : List (TblIns n)) {c : TblCode n} {st : TblSt n A}
    {P : TblSt n A → Prop} {K : ℕ} (hf : tblFitsList A W w l st)
    (h : TblDo A W w c (tblExactList A w l st) P K) :
    TblDo A W w (tblStraight n l c) st P (l.length + K) :=
  TblDo.straight l (by rw [tblRunList_eq_exact l st hf]; exact h)

theorem tblExactList_append (l₁ l₂ : List (TblIns n)) (st : TblSt n A) :
    tblExactList A w (l₁ ++ l₂) st = tblExactList A w l₂ (tblExactList A w l₁ st) := by
  induction l₁ generalizing st with
  | nil => rfl
  | cons i l ih => exact ih _

theorem tblFitsList_append (l₁ l₂ : List (TblIns n)) (st : TblSt n A)
    (h₁ : tblFitsList A W w l₁ st) (h₂ : tblFitsList A W w l₂ (tblExactList A w l₁ st)) :
    tblFitsList A W w (l₁ ++ l₂) st := by
  induction l₁ generalizing st with
  | nil => exact h₂
  | cons i l ih => exact ⟨h₁.1, ih _ h₁.2 h₂⟩

/-- One instruction without overflow. -/
theorem TblDo.insX (i : TblIns n) {st : TblSt n A} {P : TblSt n A → Prop} (hf : i.fits A W st)
    (h : P (i.exact A w st)) : TblDo A W w (.ins i) st P 1 :=
  TblDo.ins i (by rw [TblIns.run_eq_exact i st hf]; exact h)

/-- A block of instructions ending in `i`. -/
def tblBlock (n : ℕ) (l : List (TblIns n)) (i : TblIns n) : TblCode n := tblStraight n l (.ins i)

/-- A block without overflow, in exact arithmetic. -/
theorem TblDo.block (l : List (TblIns n)) (i : TblIns n) {st : TblSt n A} {P : TblSt n A → Prop}
    (hf : tblFitsList A W w (l ++ [i]) st) (h : P (tblExactList A w (l ++ [i]) st)) :
    TblDo A W w (tblBlock n l i) st P (l.length + 1) := by
  have hf' := hf
  induction l generalizing st with
  | nil =>
    simp only [List.nil_append, tblFitsList, tblExactList] at hf h
    simp only [tblBlock, tblStraight, List.length_nil]
    exact TblDo.ins i (by rw [TblIns.run_eq_exact i st hf.1]; exact h)
  | cons j l ih =>
    simp only [List.cons_append, tblFitsList, tblExactList] at hf h
    have := ih (st := j.exact A w st) hf.2 h hf.2
    have e := TblIns.run_eq_exact (w := w) j st hf.1
    refine ((TblDo.ins j (P := fun s => s = j.run A W w st) rfl).seq
      (fun s hs => hs ▸ e ▸ this)).mono (fun _ h => h) (by simp; omega)

end Exact

/-! ### Counting loops and constants -/

section Macros

variable {n A W w : ℕ}

/-- Sequencing. -/
infixr:60 " ;; " => TblCode.seq

/-- `for i < nv do body`: `i := 0`, then `body; i := i + 1` while `i < nv`. -/
def tblFor (i nv : Fin n) (body : TblCode n) : TblCode n :=
  .seq (.ins (.zero i)) (.loop i nv (.seq body (.ins (.inc i))))

/-- A counting loop: `Inv j` before iteration `j`, where `i = j` and `nv = N`; the body keeps
`i` and `nv` and establishes `Inv (j + 1)` up to the increment of `i`. -/
theorem TblDo.for {i nv : Fin n} {body : TblCode n} {st : TblSt n A} {P : TblSt n A → Prop}
    (N Kb : ℕ) (hN : st.val nv = N) (hNW : N < 2 ^ W) (hi : i ≠ nv)
    (Inv : ℕ → TblSt n A → Prop) (h0 : Inv 0 ⟨Function.update st.val i 0, st.acc⟩)
    (hstep : ∀ j < N, ∀ s, Inv j s → s.val i = j → s.val nv = N →
      TblDo A W w body s (fun s' => s'.val i = j ∧ s'.val nv = N ∧
        Inv (j + 1) ⟨Function.update s'.val i (j + 1), s'.acc⟩) Kb)
    (hend : ∀ s, Inv N s → s.val i = N → s.val nv = N → P s) :
    TblDo A W w (tblFor i nv body) st P (1 + (N * (Kb + 1 + 2) + 2)) := by
  refine (TblDo.ins (.zero i) (P := fun s => s = ⟨Function.update st.val i 0, st.acc⟩) rfl).seq
    (fun s hs => ?_)
  subst hs
  refine TblDo.loop (fun j s => Inv j s ∧ s.val i = j ∧ s.val nv = N) N (Kb + 1)
    ⟨h0, by simp, by simp [Function.update_of_ne hi.symm, hN]⟩ ?_ ?_
  · intro j hj s ⟨hs, hsi, hsn⟩
    refine ⟨by rw [hsi, hsn]; exact hj, ?_⟩
    refine (hstep j hj s hs hsi hsn).seq (fun s' ⟨h1, h2, h3⟩ => TblDo.ins (.inc i) ?_)
    have hm : (s'.val i + 1) % 2 ^ W = j + 1 := by rw [h1]; exact Nat.mod_eq_of_lt (by omega)
    refine ⟨by simpa [TblIns.run, hm] using h3, by simp [TblIns.run, hm], ?_⟩
    simp [TblIns.run, Function.update_of_ne hi.symm, h2]
  · intro s ⟨hs, hsi, hsn⟩
    exact ⟨by rw [hsi, hsn]; exact lt_irrefl N, hend s hs hsi hsn⟩

/-- `c := k`: zero and `k` increments. -/
def tblConstL (c : Fin n) (k : ℕ) : List (TblIns n) := .zero c :: List.replicate k (.inc c)

theorem tblRunList_replicate_inc (c : Fin n) (k x : ℕ) (l : List (TblIns n))
    (σ : Fin n → ℕ) (acc : List (Fin (A + 4))) :
    tblRunList A W w (List.replicate k (.inc c) ++ l) ⟨Function.update σ c (x % 2 ^ W), acc⟩ =
      tblRunList A W w l ⟨Function.update σ c ((x + k) % 2 ^ W), acc⟩ := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
    rw [List.replicate_succ, List.cons_append, tblRunList]
    have e : TblIns.run A W w (.inc c) (⟨Function.update σ c (x % 2 ^ W), acc⟩ : TblSt n A) =
        ⟨Function.update σ c ((x + 1) % 2 ^ W), acc⟩ := by
      simp [TblIns.run, Nat.add_mod]
    rw [e, ih, Nat.add_assoc, Nat.add_comm 1 k]

/-- The effect of `tblConstL c k` in front of a block. -/
theorem tblRunList_const (c : Fin n) (k : ℕ) (l : List (TblIns n)) (st : TblSt n A) :
    tblRunList A W w (tblConstL c k ++ l) st =
      tblRunList A W w l ⟨Function.update st.val c (k % 2 ^ W), st.acc⟩ := by
  rw [tblConstL, List.cons_append, tblRunList]
  have e : TblIns.run A W w (.zero c) st = ⟨Function.update st.val c (0 % 2 ^ W), st.acc⟩ := by
    simp [TblIns.run]
  rw [e, tblRunList_replicate_inc, Nat.zero_add]

theorem tblExactList_replicate_inc (c : Fin n) (k x : ℕ) (σ : Fin n → ℕ)
    (acc : List (Fin (A + 4))) :
    tblExactList A w (List.replicate k (.inc c)) ⟨Function.update σ c x, acc⟩ =
      ⟨Function.update σ c (x + k), acc⟩ := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
    rw [List.replicate_succ, tblExactList]
    have e : TblIns.exact A w (.inc c) (⟨Function.update σ c x, acc⟩ : TblSt n A) =
        ⟨Function.update σ c (x + 1), acc⟩ := by simp [TblIns.exact]
    rw [e, ih, Nat.add_assoc, Nat.add_comm 1 k]

theorem tblFitsList_replicate_inc (c : Fin n) (k x : ℕ) (σ : Fin n → ℕ)
    (acc : List (Fin (A + 4))) (hk : x + k < 2 ^ W) :
    tblFitsList A W w (List.replicate k (.inc c)) ⟨Function.update σ c x, acc⟩ := by
  induction k generalizing x with
  | zero => trivial
  | succ k ih =>
    rw [List.replicate_succ, tblFitsList]
    refine ⟨by simp [TblIns.fits]; omega, ?_⟩
    have e : TblIns.exact A w (.inc c) (⟨Function.update σ c x, acc⟩ : TblSt n A) =
        ⟨Function.update σ c (x + 1), acc⟩ := by simp [TblIns.exact]
    rw [e]
    exact ih (x + 1) (by omega)

/-- `tblConstL c k` in exact arithmetic. -/
theorem tblExactList_const (c : Fin n) (k : ℕ) (st : TblSt n A) :
    tblExactList A w (tblConstL c k) st = ⟨Function.update st.val c k, st.acc⟩ := by
  rw [tblConstL, tblExactList]
  have e : TblIns.exact A w (.zero c) st = ⟨Function.update st.val c 0, st.acc⟩ := rfl
  rw [e, tblExactList_replicate_inc, Nat.zero_add]

theorem tblFitsList_const (c : Fin n) (k : ℕ) (st : TblSt n A) (hk : k < 2 ^ W) :
    tblFitsList A W w (tblConstL c k) st := by
  rw [tblConstL, tblFitsList]
  exact ⟨trivial, tblFitsList_replicate_inc c k 0 st.val st.acc (by omega)⟩

@[simp] lemma length_tblConstL (c : Fin n) (k : ℕ) : (tblConstL c k).length = k + 1 := by
  simp [tblConstL]

/-- `c := 2 ^ e` by `e` doublings, counting on `i`. -/
def tblPow2 (c e i : Fin n) : TblCode n :=
  .seq (.ins (.zero c)) (.seq (.ins (.inc c)) (tblFor i e (.ins (.add c c c))))

/-- `tblPow2`: `c := 2 ^ e`, `i := e`, every other variable and `acc` unchanged. -/
theorem tblPow2_do {c e i : Fin n} (hce : c ≠ e) (hci : c ≠ i) (hei : e ≠ i) (st : TblSt n A)
    (hW : st.val e < W) :
    TblDo A W w (tblPow2 c e i) st (fun s => s.val c = 2 ^ st.val e ∧ s.val i = st.val e ∧
      (∀ x, x ≠ c → x ≠ i → s.val x = st.val x) ∧ s.acc = st.acc) (4 * st.val e + 5) := by
  have hpw : 2 ^ st.val e < 2 ^ W := Nat.pow_lt_pow_right (by norm_num) hW
  have h1 : 1 < 2 ^ W := Nat.one_lt_two_pow (by omega)
  have hloop : ∀ s : TblSt n A, s = ⟨Function.update st.val c 1, st.acc⟩ →
      TblDo A W w (tblFor i e (.ins (.add c c c))) s (fun s => s.val c = 2 ^ st.val e ∧
        s.val i = st.val e ∧ (∀ x, x ≠ c → x ≠ i → s.val x = st.val x) ∧ s.acc = st.acc)
        (1 + (st.val e * (1 + 1 + 2) + 2)) := by
    intro s hs
    subst hs
    refine TblDo.for (st.val e) 1 (by simp [Function.update_of_ne hce.symm]) (lt_trans hW Nat.lt_two_pow_self) hei.symm
      (fun j s => s.val c = 2 ^ j ∧ (∀ x, x ≠ c → x ≠ i → s.val x = st.val x) ∧ s.acc = st.acc)
      ⟨by simp [Function.update_of_ne hci], fun x h1 h2 => by
        simp [Function.update_of_ne h1, Function.update_of_ne h2], rfl⟩ ?_ ?_
    · intro j hj s ⟨hc, hx, ha⟩ hsi hsn
      refine TblDo.ins _ ⟨?_, ?_, ?_⟩
      · simp [TblIns.run, Function.update_of_ne hci.symm, hsi]
      · simp [TblIns.run, Function.update_of_ne hce.symm, hsn]
      · have hlt : 2 ^ (j + 1) < 2 ^ W := Nat.pow_lt_pow_right (by norm_num) (by omega)
        refine ⟨?_, fun x h1 h2 => ?_, ?_⟩
        · simp [TblIns.run, Function.update_of_ne hci, hc, ← two_mul]
          rw [Nat.mod_eq_of_lt (by rw [← pow_succ']; exact hlt), pow_succ']
        · simp [TblIns.run, Function.update_of_ne h1, Function.update_of_ne h2, hx x h1 h2]
        · simp [TblIns.run, ha]
    · intro s ⟨hc, hx, ha⟩ hsi hsn
      exact ⟨hc, hsi, hx, ha⟩
  refine (((TblDo.ins (.zero c) (P := fun s => s = ⟨Function.update st.val c 0, st.acc⟩)
    (by simp [TblIns.run])).seq (fun s hs => (TblDo.ins (.inc c)
      (P := fun s' => s' = ⟨Function.update st.val c 1, st.acc⟩) (by
        subst hs; simp [TblIns.run, Nat.mod_eq_of_lt h1])).seq hloop))).mono (fun _ h => h)
    (by omega)

end Macros

/-! ### Renaming variables -/

section Rename

variable {m n A W w : ℕ}

/-- An instruction with its variables renamed by `f`. -/
def TblIns.rename (f : Fin m → Fin n) : TblIns m → TblIns n
  | .add a b c => .add (f a) (f b) (f c)
  | .sub a b c => .sub (f a) (f b) (f c)
  | .mul a b c => .mul (f a) (f b) (f c)
  | .div a b c => .div (f a) (f b) (f c)
  | .mod a b c => .mod (f a) (f b) (f c)
  | .copy a c => .copy (f a) (f c)
  | .zero c => .zero (f c)
  | .inc c => .inc (f c)
  | .emit a b => .emit (f a) (f b)

/-- A program with its variables renamed by `f`. -/
def TblCode.rename (f : Fin m → Fin n) : TblCode m → TblCode n
  | .ins i => .ins (i.rename f)
  | .seq c d => .seq (c.rename f) (d.rename f)
  | .ite a b c d => .ite (f a) (f b) (c.rename f) (d.rename f)
  | .loop a b c => .loop (f a) (f b) (c.rename f)

/-- The variables `f` of a state. -/
def TblSt.restrict (f : Fin m → Fin n) (st : TblSt n A) : TblSt m A := ⟨st.val ∘ f, st.acc⟩

@[simp] lemma TblSt.restrict_val (f : Fin m → Fin n) (st : TblSt n A) (x : Fin m) :
    (st.restrict f).val x = st.val (f x) := rfl

@[simp] lemma TblSt.restrict_acc (f : Fin m → Fin n) (st : TblSt n A) :
    (st.restrict f).acc = st.acc := rfl

lemma tbl_update_comp {f : Fin m → Fin n} (hf : Function.Injective f) (g : Fin n → ℕ) (c : Fin m)
    (v : ℕ) : Function.update g (f c) v ∘ f = Function.update (g ∘ f) c v := by
  funext x
  by_cases h : x = c
  · subst h; simp
  · simp [Function.update_of_ne h, Function.update_of_ne (hf.ne h)]

theorem TblIns.run_rename {f : Fin m → Fin n} (hf : Function.Injective f) (i : TblIns m)
    (st : TblSt n A) :
    ((i.rename f).run A W w st).restrict f = i.run A W w (st.restrict f) ∧
      ∀ x, (∀ y, f y ≠ x) → ((i.rename f).run A W w st).val x = st.val x := by
  constructor
  · cases i <;> simp [TblIns.rename, TblIns.run, TblSt.restrict, tbl_update_comp hf]
  · intro x hx
    cases i <;> simp [TblIns.rename, TblIns.run, Function.update_of_ne (Ne.symm (hx _))]

theorem TblBig.rename {f : Fin m → Fin n} (hf : Function.Injective f) {c : TblCode m}
    {s s' : TblSt m A} {k : ℕ} (h : TblBig A W w c s s' k) :
    ∀ st : TblSt n A, st.restrict f = s → ∃ st', TblBig A W w (c.rename f) st st' k ∧
      st'.restrict f = s' ∧ ∀ x, (∀ y, f y ≠ x) → st'.val x = st.val x := by
  induction h with
  | ins i s₀ =>
    intro st hst
    subst hst
    exact ⟨_, .ins _ st, (TblIns.run_rename hf i st).1, (TblIns.run_rename hf i st).2⟩
  | seq _ _ ih₁ ih₂ =>
    intro st hst
    obtain ⟨st₁, hb₁, hr₁, hx₁⟩ := ih₁ st hst
    obtain ⟨st₂, hb₂, hr₂, hx₂⟩ := ih₂ st₁ hr₁
    exact ⟨st₂, .seq hb₁ hb₂, hr₂, fun x hx => (hx₂ x hx).trans (hx₁ x hx)⟩
  | iteT hlt _ ih =>
    intro st hst
    obtain ⟨st₁, hb₁, hr₁, hx₁⟩ := ih st hst
    refine ⟨st₁, .iteT ?_ hb₁, hr₁, hx₁⟩
    subst hst; exact hlt
  | iteF hlt _ ih =>
    intro st hst
    obtain ⟨st₁, hb₁, hr₁, hx₁⟩ := ih st hst
    refine ⟨st₁, .iteF ?_ hb₁, hr₁, hx₁⟩
    subst hst; exact hlt
  | loopF hlt =>
    intro st hst
    refine ⟨st, .loopF ?_, hst, fun _ _ => rfl⟩
    subst hst; exact hlt
  | loopT hlt _ _ ih₁ ih₂ =>
    intro st hst
    obtain ⟨st₁, hb₁, hr₁, hx₁⟩ := ih₁ st hst
    obtain ⟨st₂, hb₂, hr₂, hx₂⟩ := ih₂ st₁ hr₁
    refine ⟨st₂, .loopT ?_ hb₁ hb₂, hr₂, fun x hx => (hx₂ x hx).trans (hx₁ x hx)⟩
    subst hst; exact hlt

/-- A program on the variables `f`: its contract on the restricted state, every other variable
unchanged. -/
theorem TblDo.rename {f : Fin m → Fin n} (hf : Function.Injective f) {c : TblCode m}
    {st : TblSt n A} {Post : TblSt m A → Prop} {K : ℕ} (h : TblDo A W w c (st.restrict f) Post K) :
    TblDo A W w (c.rename f) st (fun s => Post (s.restrict f) ∧
      ∀ x, (∀ y, f y ≠ x) → s.val x = st.val x) K := by
  obtain ⟨s', k, hb, hp, hk⟩ := h
  obtain ⟨st', hb', hr, hx⟩ := hb.rename hf st rfl
  exact ⟨st', k, hb', ⟨hr ▸ hp, hx⟩, hk⟩

end Rename

/-! ### From programs to the host -/

section Host

variable {T Q A : ℕ} {U : Type} {P : Type} {body : P → Pr P T Q A U} {n : ℕ}
  {rg : TblR n → Fin T}

/-- A terminating program runs on the host: `K` atoms cost at most `K · tblC W w` steps. -/
theorem TblDo.host (hrg : Function.Injective rg) {W w : ℕ} (wl nl : List (Fin (A + 4)))
    (hwl : wl.length = W) (hnl : nl.length = w) (hw : w ≤ W) {c : TblCode n} {st : TblSt n A}
    {Post : TblSt n A → Prop} {K : ℕ} (h : TblDo A W w c st Post K)
    (hst : ∀ j, st.val j < 2 ^ W) :
    ∃ st', Post st' ∧ tblRuns body rg (tblCompile rg c) (tblRho W wl nl st) (tblRho W wl nl st')
      (K * tblC W w) := by
  obtain ⟨st', k, hb, hp, hk⟩ := h
  exact ⟨st', hp, (tblCompile_runs hrg wl nl hwl hnl hw hb hst).mono (Nat.mul_le_mul_right _ hk)⟩

end Host

/-! ### Streams on the host -/

section Stream

variable {T Q A : ℕ} {U : Type} {P : Type} {body : P → Pr P T Q A U} {n : ℕ}
  {rg : TblR n → Fin T}

/-- A table program followed by moving the emitted symbols onto the output register `out`,
first emitted symbol on top. -/
def tblHost (rg : TblR n → Fin T) (c : TblCode n) (out : Fin T) : Pr P T Q A U :=
  .seq (tblCompile rg c) (moveR (rg .acc) out id)

/-- **Streams on the host.** A program that terminates from `st` (with `acc` empty) within `K`
atoms in a state `st'` satisfying `Post` runs as `tblHost` in at most
`K · tblC W w + 2 |st'.acc| + 2` steps; the output register `out` (outside the layout) gains the
symbols of `acc` in emission order, `st'.acc.reverse`, on top; the layout carries `st'` with
`acc` emptied; every other register and the input, output and left stacks are unchanged. -/
theorem tblHost_runs (hrg : Function.Injective rg) {out : Fin T} (hout : ∀ r, rg r ≠ out)
    {W w : ℕ} (wl nl : List (Fin (A + 4))) (hwl : wl.length = W) (hnl : nl.length = w)
    (hw : w ≤ W) {c : TblCode n} {st : TblSt n A} {Post : TblSt n A → Prop} {K : ℕ}
    (h : TblDo A W w c st Post K) (hst : ∀ j, st.val j < 2 ^ W)
    (v : HS T Q A U) (S : Stacks T A) (hS : tblHolds rg S (tblRho W wl nl st)) :
    ∃ v' S' m st', Post st' ∧ v'.user = v.user ∧ m ≤ K * tblC W w + 2 * st'.acc.length + 2 ∧
      Exec body (tblHost rg c out) (mk v S) m (mk v' S') ∧
      S'.R out = st'.acc.reverse ++ S.R out ∧
      tblHolds rg S' (tblRho W wl nl ⟨st'.val, []⟩) ∧ S'.inp = S.inp ∧ S'.out = S.out ∧
      S'.L = S.L ∧ ∀ k, k ≠ out → (∀ r, rg r ≠ k) → S'.R k = S.R k := by
  obtain ⟨st', hp, hr⟩ := TblDo.host (body := body) hrg wl nl hwl hnl hw h hst
  obtain ⟨v₁, S₁, m₁, hu₁, hm₁, he₁, hS₁, hf₁⟩ := hr v S hS
  obtain ⟨v₂, hu₂, he₂⟩ := moveR_exec body (rg .acc) out (hout .acc) id v₁ S₁
  have hacc₁ : S₁.R (rg .acc) = st'.acc := hS₁ .acc
  refine ⟨v₂, _, _, st', hp, hu₂.trans hu₁, ?_, Exec.seq he₁ he₂, ?_, ?_, hf₁.1, hf₁.2.1,
    hf₁.2.2.1, fun k hk1 hk2 => ?_⟩
  · rw [hacc₁]; omega
  · simp only [movedR, List.map_id, Function.update_self, hacc₁]
    rw [hf₁.2.2.2 out hout]
  · intro r
    simp only [movedR, List.map_id]
    rw [Function.update_of_ne (hout r)]
    by_cases hr : r = .acc
    · subst hr; simp [tblRho]
    · rw [Function.update_of_ne (hrg.ne hr), hS₁ r]
      cases r <;> simp_all [tblRho]
  · simp only [movedR, List.map_id]
    rw [Function.update_of_ne hk1, Function.update_of_ne (Ne.symm (hk2 .acc)), hf₁.2.2.2 k hk2]

end Stream

/-! ### Signed values for emission -/

section Signed

variable {n A W w : ℕ}

/-- `out := mg` if `sg = 0` and `2^w − (mg mod 2^w)` if `sg = 1`, from `pw = 2^w` and `one = 1`,
through the scratch variable `t`: a natural number congruent to `±mg` modulo `2^w`. -/
def tblSignedL (sg mg pw one t out : Fin n) : List (TblIns n) :=
  [.mod mg pw t, .sub pw t t, .mul t sg t, .sub one sg out, .mul mg out out, .add out t out]

/-- The value of `tblSignedL`. -/
def tblSignedVal (w : ℕ) (neg : Bool) (mg : ℕ) : ℕ := if neg then 2 ^ w - mg % 2 ^ w else mg

theorem tblSignedVal_cast (w : ℕ) (neg : Bool) (mg : ℕ) :
    ((tblSignedVal w neg mg : ℕ) : ZMod (2 ^ w)) = ((if neg then -(mg : ℤ) else mg : ℤ) : ZMod (2 ^ w)) := by
  unfold tblSignedVal
  cases neg
  · simp
  · simp only [ite_true, Int.cast_neg, Int.cast_natCast]
    have hlt : mg % 2 ^ w ≤ 2 ^ w := (Nat.mod_lt _ (Nat.two_pow_pos w)).le
    rw [Nat.cast_sub hlt, ZMod.natCast_self, zero_sub, ZMod.natCast_mod]

theorem tblSignedVal_lt (w : ℕ) (neg : Bool) (mg : ℕ) :
    tblSignedVal w neg mg ≤ max mg (2 ^ w) := by
  unfold tblSignedVal
  split_ifs <;> omega

end Signed

end IntegerMultBounds.MathlibTM2.Fast.TableVM
