module

public import IntegerMultBounds.MathlibTM2.Fast.RingProd
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

/-!
# The header of the ring-product stage

`rpProg` (`IntegerMultBounds.MathlibTM2.Fast.RingProd`) reads the gamma-coded header `Γ(p) Γ(2^l) Γ(w)`
(`Spec.SignedRingProduct.header p (2 ^ l) w`) from the data register `d0`. `ldrHeader` writes
it from the parameters `p`, `l`, `w` held in unary registers.

**Registers** (`Fin T`, pairwise distinct, `ldrHeader pR lR wR d0 a h par cnt t`): the unary
inputs `pR`, `lR`, `wR` hold `p`, `l`, `w` symbols (any symbols; only the lengths are read, and
the registers end as they started); the destination `d0`; the work registers `a`, `h`, `par`,
`cnt`, `t`, empty before and after.

**Gamma code of a unary value** (`ldrGamma u …`). `u` is copied as ticks onto `a`. The halving
loop (`ldrLoop`) runs while `a` is nonempty: one pass over `a` (`drainR` with the toggle
`ldrHalfFx`) leaves `|a| mod 2` ticks on `par` and `⌊|a| / 2⌋` ticks on `h`; the parity is pushed
onto `d0` as a bit symbol and a tick onto `cnt` (`ldrBitAct`); `h` moves back onto `a`. The bits
of `v = |u|` come least significant first, so `d0` gains `msbBits (size v) v` (most significant
on top) and `cnt` gains `size v` ticks, within `13 v + 1` steps (`ldr_step_exec`,
`ldr_loop_aux`). Then one tick of `cnt` is dropped and `size v - 1` zeros are pushed onto `d0`:
`d0` gains `Γ(v)`, within `23 v + 13` steps (`ldr_gamma_runs`).

**Gamma code of `2^l`** (`ldrPow`): `Γ(2^l) = 0^l 1 0^l` (`ldr_gamma_two_pow`), pushed from the
unary `l` by two `zeroBits` and one push, within `8 l + 9` steps (`ldr_pow_runs`).

**Header** (`ldrHeader`): `Γ(w)`, then `Γ(2^l)`, then `Γ(p)`, so `d0` gains
`(header p (2 ^ l) w).map bitSymbol` with `Γ(p)` on top (`ldr_header_runs`, `ldrHeader_exec`),
within `ldrHeaderCost p l w = 23 p + 8 l + 23 w + 35` steps. `ldrRuns` is the contract used for
the pieces: register file `R₀` to `R₁`, `user` kept.

**Stage** (`ldRpStage`): `ldrHeader` with `d0 = rg .d0` and the scratch registers of the
ring-product layout as work registers (`a = rg .ta`, `h = rg .tb`, `par = rg .acc`,
`cnt = rg .sv`, `t = rg .tmp`), then `rpProg`. `ldRpStage_exec`: from the register
file of `rpProg_exec` with `d0` empty and `p`, `l`, `w` on the unary inputs, `out` gains the
stream of the pointwise products, `d0` ends holding the header, every other register ends as it
started, within `ldrHeaderCost p l w + rpCost p l w M` steps.
-/

@[expose] public section



namespace IntegerMultBounds.MathlibTM2.Fast

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.Spec.SignedRingProduct

/-! ### Binary words and gamma codes -/

/-- The low end of `msbBits`: the last bit is the parity. -/
theorem ldr_msbBits_succ :
    ∀ n v : ℕ, msbBits (n + 1) v = msbBits n (v / 2) ++ [decide (v % 2 = 1)]
  | 0, v => by simp [msbBits]
  | n + 1, v => by
    rw [msbBits, ldr_msbBits_succ n v, msbBits, Nat.div_div_eq_div_mul, ← pow_succ']
    rfl

theorem ldr_size_succ {v : ℕ} (hv : 1 ≤ v) : Nat.size v = Nat.size (v / 2) + 1 := by
  have h := Nat.size_bit (b := v % 2 = 1) (n := v / 2) (by
    simp [Nat.bit]; split <;> omega)
  have e : Nat.bit (decide (v % 2 = 1)) (v / 2) = v := by
    simp [Nat.bit]; split <;> omega
  rw [e] at h
  exact h

/-- The binary word of `v` with `size v` bits gains the parity of `v` at its low end. -/
theorem ldr_msbBits_size {v : ℕ} (hv : 1 ≤ v) :
    msbBits (Nat.size v) v = msbBits (Nat.size (v / 2)) (v / 2) ++ [decide (v % 2 = 1)] := by
  rw [ldr_size_succ hv, ldr_msbBits_succ]

theorem ldr_size_le (v : ℕ) : Nat.size v ≤ v := Nat.size_le.2 Nat.lt_two_pow_self

theorem ldr_msbBits_two_pow (l : ℕ) : ∀ n, n ≤ l → msbBits n (2 ^ l) = List.replicate n false
  | 0, _ => rfl
  | n + 1, h => by
    rw [msbBits, ldr_msbBits_two_pow l n (by omega), List.replicate_succ]
    congr 1
    rw [Nat.pow_div (by omega) (by norm_num)]
    obtain ⟨k, hk⟩ : ∃ k, l - n = k + 1 := ⟨l - n - 1, by omega⟩
    rw [hk, pow_succ]
    simp

/-- `Γ(2^l) = 0^l 1 0^l`. -/
theorem ldr_gamma_two_pow (l : ℕ) :
    gamma (2 ^ l) = List.replicate l false ++ true :: List.replicate l false := by
  rw [gamma, Nat.size_pow, Nat.add_sub_cancel, msbBits, ldr_msbBits_two_pow l l le_rfl]
  simp

/-! ### The programs -/

section Programs

variable {T Q A : ℕ} {U : Type} {P : Type}

/-- One symbol of the halving pass: pop the parity register `par`; if it held a tick, push a
tick onto `h`, otherwise push a tick onto `par`. -/
def ldrHalfFx (par h : Fin T) (k : Act T Q A U) : Act T Q A U :=
  .pop (.rt par) (fun v o => { v with flag := o.isSome })
    (.branch (·.flag) (.push (.rt h) (fun _ => tick) k) (.push (.rt par) (fun _ => tick) k))

/-- Move the parity from `par` onto `d0` as a bit symbol and count one bit on `cnt`. -/
def ldrBitAct (par d0 cnt : Fin T) : Act T Q A U :=
  .pop (.rt par) (fun v o => { v with flag := o.isSome })
    (.push (.rt d0) (fun v => bitSymbol v.flag) (.push (.rt cnt) (fun _ => tick) .done))

/-- One halving step: halve `a` onto `h` keeping the parity on `par`, emit the parity, move
`h` back onto `a`, and record in `flag` whether `a` is nonempty. -/
def ldrStep (a h par d0 cnt : Fin T) : Pr P T Q A U :=
  .seq (drainR a (ldrHalfFx par h))
    (.seq (.act (ldrBitAct par d0 cnt)) (.seq (moveR h a id) (.act (peekR a))))

/-- The halving loop: the bits of `|a|` onto `d0`, least significant first. -/
def ldrLoop (a h par d0 cnt : Fin T) : Pr P T Q A U :=
  .seq (.act (peekR a)) (.loop (·.flag) (ldrStep a h par d0 cnt))

/-- Push `Γ(|u|)` onto `d0`. -/
def ldrGamma (u d0 a h par cnt t : Fin T) : Pr P T Q A U :=
  .seq (ucopy u a t) (.seq (ldrLoop a h par d0 cnt)
    (.seq (.act (dropTop cnt .done)) (.seq (zeroBits cnt d0 t) (uclear cnt))))

/-- Push `Γ(2^|lR|) = 0^l 1 0^l` onto `d0`. -/
def ldrPow (lR d0 t : Fin T) : Pr P T Q A U :=
  .seq (zeroBits lR d0 t) (.seq (.act (.push (.rt d0) (fun _ => bitSymbol true) .done))
    (zeroBits lR d0 t))

/-- **The header program**: `Γ(|wR|)`, `Γ(2^|lR|)`, `Γ(|pR|)` onto `d0`. -/
def ldrHeader (pR lR wR d0 a h par cnt t : Fin T) : Pr P T Q A U :=
  .seq (ldrGamma wR d0 a h par cnt t) (.seq (ldrPow lR d0 t) (ldrGamma pR d0 a h par cnt t))

/-- The step bound of `ldrHeader`. -/
def ldrHeaderCost (p l w : ℕ) : ℕ := 23 * p + 8 * l + 23 * w + 35

end Programs

/-! ### Runs of the programs -/

section Runs

variable {T Q A : ℕ} {U : Type} {P : Type}

/-- The effect of one symbol of the halving pass on the registers. -/
def ldrHalfΦ (par h : Fin T) : Fin (A + 4) → Regs T A → Regs T A := fun _ R =>
  if (R par).head?.isSome then
    Function.update (Function.update R par (R par).tail) h
      (tick :: Function.update R par (R par).tail h)
  else
    Function.update (Function.update R par (R par).tail) par
      (tick :: Function.update R par (R par).tail par)

/-- `ldrHalfFx` acts as `ldrHalfΦ`. -/
theorem ldr_regFx_half (par h : Fin T) :
    RegFx (ldrHalfFx (T := T) (Q := Q) (A := A) (U := U) par h) (ldrHalfΦ par h) := by
  intro x k v S _
  refine ⟨{ v with flag := (S.R par).head?.isSome }, rfl, ?_⟩
  by_cases hp : (S.R par).head?.isSome = true
  · simp [ldrHalfFx, ldrHalfΦ, Action.run, update_rt, hp]
  · simp [ldrHalfFx, ldrHalfΦ, Action.run, update_rt, hp]

theorem ldr_frame_half {a par h : Fin T} (hap : a ≠ par) (hah : a ≠ h) :
    Frame a (ldrHalfΦ (A := A) par h) := by
  intro x R l
  funext k
  simp only [ldrHalfΦ, Function.update_of_ne (Ne.symm hap)]
  split_ifs <;> simp only [Function.update_apply] <;> split_ifs <;> simp_all

theorem ldr_fold_half {par h : Fin T} (hph : par ≠ h) :
    ∀ (l : List (Fin (A + 4))) (R : Regs T A) (e : ℕ), e ≤ 1 → R par = List.replicate e tick →
      l.foldl (fun R x => ldrHalfΦ par h x R) R =
        Function.update (Function.update R par (List.replicate ((e + l.length) % 2) tick)) h
          (List.replicate ((e + l.length) / 2) tick ++ R h)
  | [], R, e, he, hR => by
      have h1 : e % 2 = e := Nat.mod_eq_of_lt (by omega)
      have h2 : e / 2 = 0 := by omega
      simp only [List.foldl_nil, List.length_nil, Nat.add_zero, h1, h2, List.replicate_zero,
        List.nil_append, ← hR, Function.update_eq_self]
  | x :: rest, R, e, he, hR => by
      simp only [List.foldl_cons]
      rcases Nat.lt_or_ge e 1 with h0 | h1
      · have e0 : e = 0 := by omega
        subst e0
        have hΦ : ldrHalfΦ par h x R = Function.update R par [tick] := by
          simp [ldrHalfΦ, hR]
        rw [hΦ, ldr_fold_half hph rest _ 1 le_rfl (by simp)]
        have e2 : (1 + rest.length) / 2 = (0 + (rest.length + 1)) / 2 := by omega
        have e3 : (1 + rest.length) % 2 = (0 + (rest.length + 1)) % 2 := by omega
        funext k
        simp only [Function.update_apply, List.length_cons, e2, e3]
        split_ifs <;> subst_vars <;> simp_all
      · have e1 : e = 1 := by omega
        subst e1
        have hΦ : ldrHalfΦ par h x R =
            Function.update (Function.update R par []) h (tick :: R h) := by
          simp [ldrHalfΦ, hR, Function.update_of_ne hph.symm]
        rw [hΦ, ldr_fold_half hph rest _ 0 (by omega)
          (by simp [Function.update_of_ne hph])]
        have e2 : (1 + (rest.length + 1)) / 2 = (0 + rest.length) / 2 + 1 := by omega
        have e3 : (1 + (rest.length + 1)) % 2 = (0 + rest.length) % 2 := by omega
        funext k
        simp only [Function.update_apply, List.length_cons, e2, e3]
        split_ifs <;> subst_vars <;> simp_all [List.replicate_succ']

/-- `p` takes every store with register file `R₀` to the same store with register file `R₁`,
the `user` component kept, within `c` steps. -/
def ldrRuns (body : P → Pr P T Q A U) (p : Pr P T Q A U) (R₀ R₁ : Regs T A) (c : ℕ) : Prop :=
  ∀ (v : HS T Q A U) (S : Stacks T A), S.R = R₀ →
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧ m ≤ c ∧
      Exec body p (mk v S) m (mk v' { S with R := R₁ })

theorem ldrRuns.seq {body : P → Pr P T Q A U} {p q : Pr P T Q A U} {R₀ R₁ R₂ : Regs T A}
    {c₁ c₂ : ℕ} (h₁ : ldrRuns body p R₀ R₁ c₁) (h₂ : ldrRuns body q R₁ R₂ c₂) :
    ldrRuns body (.seq p q) R₀ R₂ (c₁ + c₂) := by
  intro v S hS
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := h₁ v S hS
  obtain ⟨v₂, m₂, hu₂, hm₂, he₂⟩ := h₂ v₁ { S with R := R₁ } rfl
  exact ⟨v₂, m₁ + m₂, hu₂.trans hu₁, by omega, Exec.seq he₁ he₂⟩

theorem ldrRuns.mono {body : P → Pr P T Q A U} {p : Pr P T Q A U} {R₀ R₁ : Regs T A}
    {c c' : ℕ} (h : ldrRuns body p R₀ R₁ c) (hc : c ≤ c') : ldrRuns body p R₀ R₁ c' := by
  intro v S hS
  obtain ⟨v', m, hu, hm, he⟩ := h v S hS
  exact ⟨v', m, hu, hm.trans hc, he⟩

theorem ldrRuns.congr {body : P → Pr P T Q A U} {p : Pr P T Q A U} {R₀ R₁ R₁' : Regs T A}
    {c : ℕ} (h : ldrRuns body p R₀ R₁ c) (e : R₁ = R₁') : ldrRuns body p R₀ R₁' c := e ▸ h

variable (body : P → Pr P T Q A U)

/-- One halving step: `a` halves, its parity goes onto `d0`, one tick onto `cnt`; `flag`
records whether the halved `a` is nonempty. -/
theorem ldr_step_exec {a h par d0 cnt : Fin T} (hreg : [a, h, par, d0, cnt].Nodup)
    (v : HS T Q A U) (S : Stacks T A) (hh : S.R h = []) (hp : S.R par = []) :
    ∃ v' : HS T Q A U, v'.user = v.user ∧
      v'.flag = (List.replicate ((S.R a).length / 2) (tick : Fin (A + 4))).head?.isSome ∧
      Exec body (ldrStep a h par d0 cnt) (mk v S)
        (2 * (S.R a).length + 2 * ((S.R a).length / 2) + 6)
        (mk v' { S with R := Function.update (Function.update (Function.update S.R a
          (List.replicate ((S.R a).length / 2) tick)) d0
          (bitSymbol (decide ((S.R a).length % 2 = 1)) :: S.R d0)) cnt (tick :: S.R cnt) }) := by
  simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil,
    not_false_eq_true, List.nodup_nil, and_true] at hreg
  obtain ⟨⟨hah, hap, had, hac⟩, ⟨hhp, hhd, hhc⟩, ⟨hpd, hpc⟩, hdc⟩ := hreg
  set n := (S.R a).length with hn
  obtain ⟨v₁, hu₁, he₁⟩ := drainR_exec body a (ldr_regFx_half par h) (ldr_frame_half hap hah) v S
  rw [ldr_fold_half (Ne.symm hhp) (S.R a) S.R 0 (by omega) (by simp [hp])] at he₁
  set R₁ := Function.update (Function.update (Function.update S.R par
    (List.replicate ((0 + n) % 2) tick)) h (List.replicate ((0 + n) / 2) tick ++ S.R h)) a []
    with hR₁
  have hpar₁ : R₁ par = List.replicate (n % 2) tick := by
    simp [hR₁, Function.update_of_ne (Ne.symm hap), Function.update_of_ne (Ne.symm hhp)]
  have hb : (List.replicate (n % 2) (tick : Fin (A + 4))).head?.isSome = decide (n % 2 = 1) := by
    rcases Nat.mod_two_eq_zero_or_one n with h0 | h1
    · simp [h0]
    · simp [h1]
  set R₂ := Function.update (Function.update (Function.update R₁ par []) d0
    (bitSymbol (decide (n % 2 = 1)) :: R₁ d0)) cnt (tick :: R₁ cnt) with hR₂
  have hrun₂ : (ldrBitAct par d0 cnt : Act T Q A U).run (mk v₁ { S with R := R₁ }) =
      mk { v₁ with flag := decide (n % 2 = 1) } { S with R := R₂ } := by
    have htail : (List.replicate (n % 2) (tick : Fin (A + 4))).tail = [] := by
      rcases Nat.mod_two_eq_zero_or_one n with h0 | h1
      · rw [h0]; rfl
      · rw [h1]; rfl
    simp only [ldrBitAct, Action.run, mk_var, mk_stk, get_rt, update_rt, store_mk, hpar₁, hb,
      htail]
    rw [hR₂]
    congr 2
    funext k
    simp only [Function.update_apply]
    split_ifs <;> simp_all
  have he₂ := Exec.act (body := body) (ldrBitAct par d0 cnt) (mk v₁ { S with R := R₁ })
  rw [hrun₂] at he₂
  obtain ⟨v₃, hu₃, he₃⟩ := moveR_exec body h a (Ne.symm hah) id
    { v₁ with flag := decide (n % 2 = 1) } { S with R := R₂ }
  have hh₂ : R₂ h = List.replicate (n / 2) tick := by
    simp [hR₂, hR₁, Function.update_of_ne hhc, Function.update_of_ne hhd,
      Function.update_of_ne hhp, Function.update_of_ne (Ne.symm hah), hh]
  set R₃ := movedR R₂ h a id (R₂ h) with hR₃
  have he₄ := Exec.act (body := body) (peekR a) (mk v₃ { S with R := R₃ })
  rw [peekR_run] at he₄
  have hR₂a : R₂ a = [] := by
    simp [hR₂, hR₁, Function.update_of_ne had, Function.update_of_ne hac,
      Function.update_of_ne hap]
  have ha₃ : R₃ a = List.replicate (n / 2) tick := by
    rw [hR₃, movedR, hh₂, Function.update_self, hR₂a]
    simp
  refine ⟨{ v₃ with flag := (List.replicate (n / 2) (tick : Fin (A + 4))).head?.isSome },
    by simp [hu₃, hu₁], rfl, ?_⟩
  have hfin : R₃ = Function.update (Function.update (Function.update S.R a
      (List.replicate (n / 2) tick)) d0 (bitSymbol (decide (n % 2 = 1)) :: S.R d0)) cnt
      (tick :: S.R cnt) := by
    funext k
    simp only [hR₃, movedR, hR₂, hR₁, Function.update_apply, List.map_id]
    split_ifs <;> subst_vars <;> simp_all
  rw [hfin] at he₃ he₄
  refine Exec.cast (Exec.seq he₁ (Exec.seq he₂ (Exec.seq he₃ he₄))) ?_ ?_
  · show 2 * (S.R a).length + 2 + (1 + (2 * (R₂ h).length + 2 + 1)) = 2 * n + 2 * (n / 2) + 6
    rw [hh₂, List.length_replicate, ← hn]
    ring
  · simp [Function.update_of_ne had, Function.update_of_ne hac]

/-- The register file after the halving loop on `n` symbols of `a`. -/
def ldrLoopR (a d0 cnt : Fin T) (R : Regs T A) (n : ℕ) : Regs T A :=
  Function.update (Function.update (Function.update R a []) d0
    ((msbBits (Nat.size n) n).map bitSymbol ++ R d0)) cnt
    (List.replicate (Nat.size n) tick ++ R cnt)

/-- The halving loop on a register `a` of `n` symbols: `d0` gains `msbBits (size n) n` (most
significant bit on top), `cnt` gains `size n` ticks, `a` ends empty; at most `13 n + 1` steps. -/
theorem ldr_loop_aux {a h par d0 cnt : Fin T} (hreg : [a, h, par, d0, cnt].Nodup) :
    ∀ (n : ℕ) (v : HS T Q A U) (S : Stacks T A), (S.R a).length = n → S.R h = [] →
      S.R par = [] → v.flag = (S.R a).head?.isSome →
      ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧ m ≤ 13 * n + 1 ∧
        Exec body (.loop (·.flag) (ldrStep a h par d0 cnt)) (mk v S) m
          (mk v' { S with R := ldrLoopR a d0 cnt S.R n }) := by
  have hreg' := hreg
  simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil,
    not_false_eq_true, List.nodup_nil, and_true] at hreg'
  obtain ⟨⟨hah, hap, had, hac⟩, ⟨hhp, hhd, hhc⟩, ⟨hpd, hpc⟩, hdc⟩ := hreg'
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro v S hn hh hp hf
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · subst h0
      have ha : S.R a = [] := List.eq_nil_of_length_eq_zero hn
      refine ⟨v, 1, rfl, by omega, ?_⟩
      have e : ({ S with R := ldrLoopR a d0 cnt S.R 0 } : Stacks T A) = S := by
        cases S with
        | mk inp out L R =>
          simp only at ha ⊢
          congr 1
          rw [ldrLoopR, ← ha]
          simp [Nat.size_zero, msbBits]
      rw [e]
      exact .loop_false (by show v.flag = false; rw [hf, ha]; rfl)
    · have hft : v.flag = true := by
        rw [hf]
        cases hS : S.R a with
        | nil => rw [hS] at hn; simp at hn; omega
        | cons _ _ => rfl
      obtain ⟨v₁, hu₁, hf₁, he₁⟩ := ldr_step_exec body hreg v S hh hp
      rw [hn] at hf₁ he₁
      set R₁ := Function.update (Function.update (Function.update S.R a
          (List.replicate (n / 2) tick)) d0 (bitSymbol (decide (n % 2 = 1)) :: S.R d0)) cnt
          (tick :: S.R cnt) with hR₁
      obtain ⟨v', m, hu, hm, he⟩ := ih (n / 2) (by omega) v₁ { S with R := R₁ }
        (by simp [hR₁, Function.update_of_ne hac, Function.update_of_ne had])
        (by simp [hR₁, Function.update_of_ne hhc, Function.update_of_ne hhd,
          Function.update_of_ne (Ne.symm hah), hh])
        (by simp [hR₁, Function.update_of_ne hpc, Function.update_of_ne hpd,
          Function.update_of_ne (Ne.symm hap), hp])
        (by rw [hf₁]; simp [hR₁, Function.update_of_ne hac, Function.update_of_ne had])
      refine ⟨v', 2 * n + 2 * (n / 2) + 6 + m + 1, by rw [hu, hu₁], by omega,
        Exec.cast (Exec.loop_true (body := body) (f := (·.flag)) hft he₁ he) rfl ?_⟩
      have hd0 : R₁ d0 = bitSymbol (decide (n % 2 = 1)) :: S.R d0 := by
        simp [hR₁, Function.update_of_ne hdc]
      have hc0 : R₁ cnt = tick :: S.R cnt := by simp [hR₁]
      simp only [ldrLoopR, hd0, hc0]
      rw [ldr_msbBits_size hpos, ldr_size_succ hpos, List.map_append, List.append_assoc,
        List.replicate_succ', List.append_assoc]
      congr 2
      funext k
      simp only [hR₁, Function.update_apply]
      split_ifs <;> simp_all

/-- `ldrGamma`: `d0` gains `Γ(|u|)`; every other register ends as it started. -/
theorem ldr_gamma_runs {u d0 a h par cnt t : Fin T} (hreg : [u, d0, a, h, par, cnt, t].Nodup)
    (R : Regs T A) (ha : R a = []) (hh : R h = []) (hp : R par = []) (hc : R cnt = [])
    (ht : R t = []) :
    ldrRuns body (ldrGamma u d0 a h par cnt t) R
      (Function.update R d0 ((gamma (R u).length).map bitSymbol ++ R d0))
      (23 * (R u).length + 13) := by
  have hreg' := hreg
  simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil,
    not_false_eq_true, List.nodup_nil, and_true] at hreg'
  obtain ⟨⟨hud, hua, huh, hup, huc, hut⟩, ⟨hda, hdh, hdp, hdc, hdt⟩, ⟨hah, hap, hac, hat⟩,
    ⟨hhp, hhc, hht⟩, ⟨hpc, hpt⟩, hct⟩ := hreg'
  intro v S hS
  subst hS
  set n := (S.R u).length with hn
  -- copy `u` onto `a`
  obtain ⟨v₁, hu₁, he₁⟩ := ucopy_exec body hua hut hat v S ht
  set R₁ := Function.update S.R a (List.replicate n tick ++ S.R a) with hR₁
  -- the halving loop
  have hp₁ := Exec.act (body := body) (peekR a) (mk v₁ { S with R := R₁ })
  rw [peekR_run] at hp₁
  obtain ⟨v₂, m₂, hu₂, hm₂, he₂⟩ := ldr_loop_aux body
    (a := a) (h := h) (par := par) (d0 := d0) (cnt := cnt)
    (by simp [List.nodup_cons, hah, hap, hac, Ne.symm hda, hhp, hhc, Ne.symm hdh, hpc,
      Ne.symm hdp, hdc]) n
    { v₁ with flag := (R₁ a).head?.isSome } { S with R := R₁ }
    (by simp [hR₁, ha]) (by simp [hR₁, Function.update_of_ne (Ne.symm hah), hh])
    (by simp [hR₁, Function.update_of_ne (Ne.symm hap), hp]) rfl
  set R₂ := ldrLoopR a d0 cnt R₁ n with hR₂
  -- drop one tick of `cnt`
  have he₃ := Exec.act (body := body) (dropTop cnt .done) (mk v₂ { S with R := R₂ })
  have hrun₃ : (dropTop cnt .done : Act T Q A U).run (mk v₂ { S with R := R₂ }) =
      mk v₂ { S with R := Function.update R₂ cnt (R₂ cnt).tail } := by
    simp [dropTop, Action.run, update_rt]
  rw [hrun₃] at he₃
  have hc₂ : R₂ cnt = List.replicate (Nat.size n) tick := by
    simp [hR₂, ldrLoopR, hR₁, Function.update_of_ne (Ne.symm hac), hc]
  set R₃ := Function.update R₂ cnt (R₂ cnt).tail with hR₃
  have hc₃ : R₃ cnt = List.replicate (Nat.size n - 1) tick := by
    simp [hR₃, hc₂, List.tail_replicate]
  -- the leading zeros
  obtain ⟨v₄, hu₄, he₄⟩ := zeroBits_exec body (Ne.symm hdc) hct hdt v₂
    { S with R := R₃ } (by simp [hR₃, hR₂, ldrLoopR, hR₁, Function.update_of_ne (Ne.symm hct),
      Function.update_of_ne (Ne.symm hdt), Function.update_of_ne (Ne.symm hat), ht])
  rw [show ({ S with R := R₃ } : Stacks T A).R cnt = R₃ cnt from rfl, hc₃,
    List.length_replicate] at he₄
  set R₄ := Function.update R₃ d0 (binSyms (Nat.size n - 1) 0 ++ R₃ d0) with hR₄
  obtain ⟨v₅, hu₅, he₅⟩ := uclear_exec body cnt v₄ { S with R := R₄ }
  refine ⟨v₅, _, by rw [hu₅, hu₄, hu₂, hu₁], ?_, Exec.cast (Exec.seq he₁ (Exec.seq
    (Exec.seq hp₁ he₂) (Exec.seq he₃ (Exec.seq he₄ he₅)))) rfl ?_⟩
  · have hc₄ : R₄ cnt = List.replicate (Nat.size n - 1) tick := by
      simp [hR₄, Function.update_of_ne (Ne.symm hdc), hc₃]
    simp only [hc₄, List.length_replicate]
    have := ldr_size_le n
    omega
  · have hg : (gamma n).map bitSymbol = binSyms (Nat.size n - 1) 0 ++
        (msbBits (Nat.size n) n).map (bitSymbol (a := A)) := by
      rw [gamma, List.map_append, List.map_replicate, binSyms_zero_right]
    have hd3 : R₃ d0 = (msbBits (Nat.size n) n).map bitSymbol ++ S.R d0 := by
      simp [hR₃, hR₂, ldrLoopR, hR₁, Function.update_of_ne hdc, Function.update_of_ne hda]
    rw [hg]
    congr 2
    funext k
    dsimp only
    by_cases hkc : k = cnt
    · subst hkc; simp [Function.update_of_ne (Ne.symm hdc), hc]
    · by_cases hkd : k = d0
      · subst hkd; simp [hR₄, Function.update_of_ne hdc, hd3]
      · rw [Function.update_of_ne hkc, Function.update_of_ne hkd, hR₄, Function.update_of_ne hkd,
          hR₃, Function.update_of_ne hkc, hR₂, ldrLoopR, Function.update_of_ne hkc,
          Function.update_of_ne hkd]
        by_cases hka : k = a
        · subst hka; simp [ha]
        · rw [Function.update_of_ne hka, hR₁, Function.update_of_ne hka]

/-- `ldrPow`: `d0` gains `Γ(2^|lR|)`. -/
theorem ldr_pow_runs {lR d0 t : Fin T} (hreg : [lR, d0, t].Nodup) (R : Regs T A)
    (ht : R t = []) :
    ldrRuns body (ldrPow lR d0 t) R
      (Function.update R d0 ((gamma (2 ^ (R lR).length)).map bitSymbol ++ R d0))
      (8 * (R lR).length + 9) := by
  have hreg' := hreg
  simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil,
    not_false_eq_true, List.nodup_nil, and_true] at hreg'
  obtain ⟨⟨hld, hlt⟩, hdt⟩ := hreg'
  intro v S hS
  subst hS
  obtain ⟨v₁, hu₁, he₁⟩ := zeroBits_exec body hld hlt hdt v S ht
  set R₁ := Function.update S.R d0 (binSyms (S.R lR).length 0 ++ S.R d0) with hR₁
  have he₂ := Exec.act (body := body)
    (.push (.rt d0) (fun _ => bitSymbol true) .done : Act T Q A U) (mk v₁ { S with R := R₁ })
  have hrun₂ : (.push (.rt d0) (fun _ => bitSymbol true) .done : Act T Q A U).run
      (mk v₁ { S with R := R₁ }) =
      mk v₁ { S with R := Function.update R₁ d0 (bitSymbol true :: R₁ d0) } := by
    simp [Action.run, update_rt]
  rw [hrun₂] at he₂
  set R₂ := Function.update R₁ d0 (bitSymbol true :: R₁ d0) with hR₂
  obtain ⟨v₃, hu₃, he₃⟩ := zeroBits_exec body hld hlt hdt v₁ { S with R := R₂ }
    (by simp [hR₂, hR₁, Function.update_of_ne (Ne.symm hdt), ht])
  have hl₂ : R₂ lR = S.R lR := by simp [hR₂, hR₁, Function.update_of_ne hld]
  refine ⟨v₃, _, by rw [hu₃, hu₁], ?_, Exec.cast (Exec.seq he₁ (Exec.seq he₂ he₃)) rfl ?_⟩
  · show 4 * (S.R lR).length + 4 + (1 + (4 * (R₂ lR).length + 4)) ≤ 8 * (S.R lR).length + 9
    rw [hl₂]; omega
  · rw [ldr_gamma_two_pow]
    congr 2
    funext k
    dsimp only
    rw [hl₂]
    by_cases hkd : k = d0
    · subst hkd
      simp [hR₂, hR₁, binSyms_zero_right]
    · simp [hR₂, hR₁, Function.update_of_ne hkd]

/-- `ldrHeader`: `d0` gains the header `Γ(p) Γ(2^l) Γ(w)`; every other register ends as it
started. -/
theorem ldr_header_runs {pR lR wR d0 a h par cnt t : Fin T}
    (hreg : [pR, lR, wR, d0, a, h, par, cnt, t].Nodup) (R : Regs T A) (ha : R a = [])
    (hh : R h = []) (hp : R par = []) (hc : R cnt = []) (ht : R t = []) :
    ldrRuns body (ldrHeader pR lR wR d0 a h par cnt t) R
      (Function.update R d0 ((header (R pR).length (2 ^ (R lR).length) (R wR).length).map
        bitSymbol ++ R d0))
      (ldrHeaderCost (R pR).length (R lR).length (R wR).length) := by
  have hreg' := hreg
  simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil,
    not_false_eq_true, List.nodup_nil, and_true] at hreg'
  obtain ⟨⟨hpl, hpw, hpd, hpa, hph, hpp, hpc, hpt⟩, ⟨hlw, hld, hla, hlh, hlp, hlc, hlt⟩,
    ⟨hwd, hwa, hwh, hwp, hwc, hwt⟩, ⟨hda, hdh, hdp, hdc, hdt⟩, ⟨hah, hap, hac, hat⟩,
    ⟨hhp, hhc, hht⟩, ⟨hpc', hpt'⟩, hct⟩ := hreg'
  have g1 := ldr_gamma_runs body (u := wR) (d0 := d0) (a := a) (h := h) (par := par) (cnt := cnt)
    (t := t) (by simp [List.nodup_cons, *]) R ha hh hp hc ht
  set R₁ := Function.update R d0 ((gamma (R wR).length).map bitSymbol ++ R d0) with hR₁
  have g2 := ldr_pow_runs body (lR := lR) (d0 := d0) (t := t) (by simp [List.nodup_cons, *]) R₁
    (by simp [hR₁, Function.update_of_ne (Ne.symm hdt), ht])
  set R₂ := Function.update R₁ d0 ((gamma (2 ^ (R₁ lR).length)).map bitSymbol ++ R₁ d0)
    with hR₂
  have e : ∀ k, k ≠ d0 → R₂ k = R k := fun k hk => by
    simp [hR₂, hR₁, Function.update_of_ne hk]
  have g3 := ldr_gamma_runs body (u := pR) (d0 := d0) (a := a) (h := h) (par := par) (cnt := cnt)
    (t := t) (by simp [List.nodup_cons, *]) R₂ (by rw [e a (Ne.symm hda)]; exact ha)
    (by rw [e h (Ne.symm hdh)]; exact hh) (by rw [e par (Ne.symm hdp)]; exact hp)
    (by rw [e cnt (Ne.symm hdc)]; exact hc) (by rw [e t (Ne.symm hdt)]; exact ht)
  have hl₁ : R₁ lR = R lR := by simp [hR₁, Function.update_of_ne hld]
  refine ((g1.seq (g2.seq g3)).mono ?_).congr ?_
  · rw [e pR hpd, hl₁]
    unfold ldrHeaderCost
    omega
  · rw [e pR hpd, header, List.map_append, List.map_append]
    funext k
    by_cases hkd : k = d0
    · subst hkd
      simp [hR₂, hR₁, Function.update_of_ne hld]
    · simp [hR₂, hR₁, Function.update_of_ne hkd]

/-- **The header.** From registers with the work registers `a`, `h`, `par`, `cnt`, `t` empty,
`ldrHeader` pushes `(header p (2 ^ l) w).map bitSymbol` onto `d0`, where `p`, `l`, `w` are the
lengths of `pR`, `lR`, `wR`; every other register (the inputs included) ends as it started, the
`user` component is kept, within `ldrHeaderCost p l w = 23 p + 8 l + 23 w + 35` steps. -/
theorem ldrHeader_exec {pR lR wR d0 a h par cnt t : Fin T}
    (hreg : [pR, lR, wR, d0, a, h, par, cnt, t].Nodup) (v : HS T Q A U) (S : Stacks T A)
    (ha : S.R a = []) (hh : S.R h = []) (hp : S.R par = []) (hc : S.R cnt = [])
    (ht : S.R t = []) :
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧
      m ≤ ldrHeaderCost (S.R pR).length (S.R lR).length (S.R wR).length ∧
      Exec body (ldrHeader pR lR wR d0 a h par cnt t) (mk v S) m
        (mk v' { S with R := (Function.update S.R d0
          ((header (S.R pR).length (2 ^ (S.R lR).length) (S.R wR).length).map bitSymbol ++
            S.R d0)) }) :=
  ldr_header_runs body hreg S.R ha hh hp hc ht v S rfl

end Runs

/-! ### The ring-product stage with its header -/

section Stage

variable {T Q A : ℕ} {U : Type} {P : Type} {body : P → Pr P T Q A U} {rg : RpReg → Fin T}
  {ι : Fin 91 → Fin T}

/-- **The ring-product stage**: the header `Γ(|pR|) Γ(2^|lR|) Γ(|wR|)` onto `d0 = rg .d0`
(work registers `rg .ta`, `rg .tb`, `rg .acc`, `rg .sv`, `rg .tmp`), then `rpProg`. -/
noncomputable def ldRpStage (rg : RpReg → Fin T) (ι : Fin 91 → Fin T)
    (hι : Function.Injective ι) (hT : 91 ≤ T) (hQ : rpStates ≤ Q) (pR lR wR : Fin T) :
    Pr P T Q A U :=
  .seq (ldrHeader pR lR wR (rg .d0) (rg .ta) (rg .tb) (rg .acc) (rg .sv) (rg .tmp))
    (rpProg rg ι hι hT hQ)

/-- **The ring-product stage from unary parameters.** The hypotheses of `rpProg_exec`, with the
data register `d0` empty in place of the header, and the registers `pR`, `lR`, `wR` holding
`p`, `l`, `w` symbols (distinct from each other and from `rg .d0`, `rg .ta`, `rg .tb`,
`rg .acc`, `rg .sv`, `rg .tmp`). Then `ldRpStage` leaves the header
`(header p (2 ^ l) w).map bitSymbol` on `d0`, pushes the stream of the numerators
`rpOut p X Y` of the pointwise products onto `rg .out`, and keeps every other register, within
`ldrHeaderCost p l w + rpCost p l w M` steps. -/
theorem ldRpStage_exec (h : RpLayout rg ι) (hT : 91 ≤ T) (hQ : rpStates ≤ Q) (hA : 4 ≤ A)
    {p l w M : ℕ} (hp : 1 ≤ p) (hw : p + 2 ≤ w) (X Y : ℕ → Fin (2 ^ l) → GaussianInt)
    (hX : ∀ n < M, DiskGrid p (rpRec X n).1 (rpRec X n).2)
    (hY : ∀ n < M, DiskGrid p (rpRec Y n).1 (rpRec Y n).2) (pR lR wR : Fin T)
    (hin : [pR, lR, wR, rg .d0, rg .ta, rg .tb, rg .acc, rg .sv, rg .tmp].Nodup)
    (v : HS T Q A U) (S : Stacks T A) (hc : RpClean ι S)
    (hxs : S.R (rg .xs) = cstream A w (rpStream M X))
    (hys : S.R (rg .ys) = cstream A w (rpStream M Y)) (hwn : (S.R (rg .wn)).length = w)
    (hsv : S.R (rg .sv) = []) (hta : S.R (rg .ta) = []) (htb : S.R (rg .tb) = [])
    (hacc : S.R (rg .acc) = []) (htmp : S.R (rg .tmp) = []) (hd0 : S.R (rg .d0) = [])
    (hd1 : S.R (rg .d1) = []) (hd2 : S.R (rg .d2) = []) (hd3 : S.R (rg .d3) = [])
    (hpR : (S.R pR).length = p) (hlR : (S.R lR).length = l) (hwR : (S.R wR).length = w) :
    ∃ v' n, v'.user = v.user ∧ n ≤ ldrHeaderCost p l w + rpCost p l w M ∧
      Exec body (ldRpStage rg ι h.ι_inj hT hQ pR lR wR) (mk v S) n
        (mk v' { S with
          R := (Function.update (Function.update S.R (rg .d0) ((header p (2 ^ l) w).map bitSymbol))
            (rg RpReg.out) (cstream A w (rpStream M (rpOut p X Y)) ++ S.R (rg RpReg.out))) }) := by
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := ldrHeader_exec body hin v S hta htb hacc hsv htmp
  rw [hpR, hlR, hwR] at hm₁ he₁
  rw [hd0, List.append_nil] at he₁
  set R₁ := Function.update S.R (rg .d0) ((header p (2 ^ l) w).map bitSymbol) with hR₁
  have e : ∀ r, r ≠ RpReg.d0 → R₁ (rg r) = S.R (rg r) := fun r hr => by
    rw [hR₁, Function.update_of_ne (h.rg_inj.ne hr)]
  have hc₁ : RpClean ι { S with R := R₁ } := by
    refine ⟨hc.1, fun j hj => ?_⟩
    have hne : ι j ≠ rg .d0 := by
      rw [h.d0]
      intro e'
      have := congrArg Fin.val (h.ι_inj e')
      simp at this
      omega
    show R₁ (ι j) = []
    rw [hR₁, Function.update_of_ne hne]
    exact hc.2 j hj
  obtain ⟨v₂, m₂, hu₂, hm₂, he₂⟩ := rpProg_exec (body := body) h hT hQ hA hp hw X Y hX hY v₁
    { S with R := R₁ } hc₁ (by rw [← hxs]; exact e _ (by decide))
    (by rw [← hys]; exact e _ (by decide))
    (by rw [← hwn]; exact congrArg List.length (e _ (by decide)))
    (by rw [← hsv]; exact e _ (by decide)) (by rw [← hta]; exact e _ (by decide))
    (by rw [← htb]; exact e _ (by decide)) (by rw [← hacc]; exact e _ (by decide))
    (by rw [← htmp]; exact e _ (by decide)) (by simp [hR₁])
    (by rw [← hd1]; exact e _ (by decide)) (by rw [← hd2]; exact e _ (by decide))
    (by rw [← hd3]; exact e _ (by decide))
  refine ⟨v₂, m₁ + m₂, by rw [hu₂, hu₁], by omega, Exec.cast (Exec.seq he₁ he₂) rfl ?_⟩
  show mk v₂ { S with R := (Function.update R₁ (rg .out)
    (cstream A w (rpStream M (rpOut p X Y)) ++ R₁ (rg .out))) } = _
  rw [e .out (by decide)]

end Stage

end IntegerMultBounds.MathlibTM2.Fast
