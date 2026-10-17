module

public import IntegerMultBounds.MathlibTM2.Fast.CRTPad
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein

/-!
# Prefix-controlled cyclic shifts of one axis

The rotation pass for a target axis acts on a box whose layout is
`crtRevAx i ++ i :: post`: the controls `i - 1, …, 0` (axis `0` least significant), the target
`i`, and the spectators `post`. Every control index `F` (a fiber) is a block of `t = 2 ^ a i`
slots, each slot `RB = 2 ^ crtW a post · B` symbols.

**Slot moves.** `crtSlots c tc r tr src dst` moves `|c| · |r|` symbols from `src` to `dst`
(one counted move of `|r|` symbols per symbol of `c`).

**Fibers.** `crtRotFib cA cB ts …` moves `|cA|` slots aside, `|cB|` slots onto the accumulator,
the `|cA|` slots after them, and the last `|ts|` slots: with `|cA| + |cB| = s`, the fiber's slot
list `sl` is output as `(sl.take s).rotate |cA| ++ sl.drop s` (`crtRotFib_runs`).
`crtCopyFib` outputs the fiber unchanged.

**Offsets.** The offset of a fiber is held in unary on `lo` with `hi` holding the complement
`s - lo`. `crtOffP` adds `μ` modulo `s` with representatives in `[0, s]`: `lo` becomes
`crtLoStep s μ lo` (`crtOffP_runs`). After `K` valid fibers the offset is
`crtLo s μ K = (crtLoStep s μ)^[K] 0`, congruent to `μ K` modulo `s` (`crtLo_cast`).
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Fast

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Mult


variable {T Q A : ℕ} {U P : Type} {body : P → Pr P T Q A U}

/-- The low `crtPre a i` bits of the packed bounds and mask of all axes. -/
lemma crt_binSyms_take_sig {d : ℕ} (a s : Fin d → ℕ) (hs : ∀ j, s j < 2 ^ a j) {i : ℕ} (hid : i ≤ d) :
    (binSyms (crtPre a d) (crtSig a s d) : List (Fin (A + 4))).take (crtPre a i) =
      binSyms (crtPre a i) (crtSig a s i) := by
  obtain ⟨e, he⟩ := Nat.exists_eq_add_of_le (crtPre_mono a hid)
  rw [he, binSyms_append, List.take_append_of_le_length (by simp), List.take_of_length_le
    (by simp), ← binSyms_mod, crtSig_mod_pre a s hs hid d hid le_rfl]

lemma crt_binSyms_take_mask {d : ℕ} (a : Fin d → ℕ) (ha : ∀ j, 1 ≤ a j) {i : ℕ} (hid : i ≤ d) :
    (binSyms (crtPre a d) (crtMask a d) : List (Fin (A + 4))).take (crtPre a i) =
      binSyms (crtPre a i) (crtMask a i) := by
  obtain ⟨e, he⟩ := Nat.exists_eq_add_of_le (crtPre_mono a hid)
  rw [he, binSyms_append, List.take_append_of_le_length (by simp), List.take_of_length_le
    (by simp), ← binSyms_mod, crtMask_mod_pre a ha hid d hid le_rfl]

/-! ### Uniform blocks -/

section Uniform

variable {α : Type*}

lemma crt_take_flatten_uniform (k : ℕ) :
    ∀ (l : List (List α)), (∀ x ∈ l, x.length = k) → ∀ n,
      l.flatten.take (n * k) = (l.take n).flatten
  | [], _, n => by simp
  | x :: l, h, 0 => by simp
  | x :: l, h, n + 1 => by
      have hx := h x (by simp)
      rw [List.flatten_cons, show (n + 1) * k = k + n * k by ring, List.take_append, hx,
        List.take_of_length_le (by omega), show k + n * k - k = n * k by omega,
        crt_take_flatten_uniform k l (fun y hy => h y (by simp [hy])) n, List.take_succ_cons,
        List.flatten_cons]

lemma crt_drop_flatten_uniform (k : ℕ) :
    ∀ (l : List (List α)), (∀ x ∈ l, x.length = k) → ∀ n,
      l.flatten.drop (n * k) = (l.drop n).flatten
  | [], _, n => by simp
  | x :: l, h, 0 => by simp
  | x :: l, h, n + 1 => by
      have hx := h x (by simp)
      rw [List.flatten_cons, show (n + 1) * k = k + n * k by ring, ← List.drop_drop,
        List.drop_append_of_le_length (by omega), ← hx, List.drop_length, List.nil_append, hx,
        crt_drop_flatten_uniform k l (fun y hy => h y (by simp [hy])) n, List.drop_succ_cons]

lemma crt_length_flatten_uniform (k : ℕ) (l : List (List α)) (h : ∀ x ∈ l, x.length = k) :
    l.flatten.length = l.length * k := by
  rw [List.length_flatten, List.map_congr_left h, List.map_const', List.sum_replicate, smul_eq_mul]

end Uniform

/-! ### Slot moves -/

/-- Move `|c| · |r|` symbols from `src` to `dst`: one counted move of `|r|` symbols per symbol of
`c`. -/
def crtSlots (c tc r tr src dst : Fin T) : Pr P T Q A U := crtFor c tc (crtCMv r tr src dst)

theorem crtSlots_runs {c tc r tr src dst : Fin T} (hreg : [c, tc, r, tr, src, dst].Nodup)
    (R : Regs T A) (htc : R tc = []) (htr : R tr = [])
    (hlen : (R c).length * (R r).length ≤ (R src).length) :
    crtRuns body (crtSlots c tc r tr src dst) R
      (Function.update (Function.update R src ((R src).drop ((R c).length * (R r).length))) dst
        (((R src).take ((R c).length * (R r).length)).reverse ++ R dst))
      ((R c).length * (4 * (R r).length + 9) + 4) := by
  have hreg' := hreg
  regs_ne hreg'
  obtain ⟨n, hn⟩ : ∃ n, (R c).length = n := ⟨_, rfl⟩
  obtain ⟨k, hk⟩ : ∃ k, (R r).length = k := ⟨_, rfl⟩
  rw [hn, hk] at hlen ⊢
  let Ψ : ℕ → Regs T A := fun j => Function.update (Function.update R src ((R src).drop (j * k)))
    dst (((R src).take (j * k)).reverse ++ R dst)
  have hit : crtIter (body := body) (crtCMv r tr src dst) c tc Ψ (4 * k + 4) n := by
    intro j hj R' hR'
    have hRr : R' r = R r := by
      rw [hR' r (Ne.symm ‹c ≠ r›) (Ne.symm ‹tc ≠ r›)]
      simp [Ψ, ‹r ≠ src›, ‹r ≠ dst›]
    have hRrk : (R' r).length = k := by rw [hRr, hk]
    have hRtr : R' tr = [] := by
      rw [hR' tr (Ne.symm ‹c ≠ tr›) (Ne.symm ‹tc ≠ tr›)]
      simp [Ψ, ‹tr ≠ src›, ‹tr ≠ dst›, htr]
    have hRsrc : R' src = (R src).drop (j * k) := by
      rw [hR' src (Ne.symm ‹c ≠ src›) (Ne.symm ‹tc ≠ src›)]; simp [Ψ, ‹src ≠ dst›]
    have hRdst : R' dst = ((R src).take (j * k)).reverse ++ R dst := by
      rw [hR' dst (Ne.symm ‹c ≠ dst›) (Ne.symm ‹tc ≠ dst›)]; simp [Ψ]
    have hlen' : (R' r).length ≤ (R' src).length := by
      rw [hRrk, hRsrc, List.length_drop]
      have : (j + 1) * k ≤ n * k := Nat.mul_le_mul_right _ (by omega)
      rw [Nat.succ_mul] at this
      omega
    refine crtRuns_mono (crtRuns_congr (crtCMv_runs (body := body) (c := r) (t := tr) (src := src)
      (dst := dst) (by regs_nodup) R' hRtr hlen') ?_) (by rw [hRrk])
    funext x
    by_cases hx : x = c ∨ x = tc
    · have h1 : x ≠ src := by rcases hx with h | h <;> rw [h] <;> assumption
      have h2 : x ≠ dst := by rcases hx with h | h <;> rw [h] <;> assumption
      simp [hx, h1, h2]
    · rw [not_or] at hx
      simp only [hx.1, hx.2, or_self, ↓reduceIte]
      by_cases x1 : x = dst
      · rw [x1]
        simp only [Function.update_self, Ψ, hRrk, hRsrc, hRdst]
        rw [Nat.succ_mul, List.take_add, List.reverse_append, List.append_assoc]
      · rw [Function.update_of_ne x1]
        by_cases x2 : x = src
        · rw [x2]
          simp only [Function.update_self, Function.update_of_ne ‹src ≠ dst›, Ψ, hRrk, hRsrc,
            List.drop_drop, Nat.succ_mul]
        · rw [Function.update_of_ne x2, hR' x hx.1 hx.2]
          simp [Ψ, x1, x2]
  have h := crtFor_runs (body := body) ‹c ≠ tc› hit (R c) hn
  have e0 : crtForRegs c tc (Ψ 0) (R c) [] = R := by
    funext x
    by_cases x1 : x = c
    · rw [x1]; simp [crtForRegs]
    · by_cases x2 : x = tc
      · rw [x2]; simp [crtForRegs, Ne.symm ‹c ≠ tc›, htc]
      · simp only [crtForRegs, x1, x2, ↓reduceIte, Ψ, Nat.zero_mul, List.drop_zero,
          List.take_zero, List.reverse_nil, List.nil_append]
        by_cases x3 : x = dst
        · rw [x3]; simp
        · rw [Function.update_of_ne x3]
          by_cases x4 : x = src
          · rw [x4]; simp
          · simp [x4]
  rw [e0] at h
  refine crtRuns_mono (crtRuns_congr h ?_) (by nlinarith)
  funext x
  by_cases x1 : x = c
  · rw [x1]; simp [crtForRegs, ‹c ≠ src›, ‹c ≠ dst›]
  · by_cases x2 : x = tc
    · rw [x2]; simp [crtForRegs, Ψ, Ne.symm ‹c ≠ tc›, ‹tc ≠ src›, ‹tc ≠ dst›, htc]
    · simp [crtForRegs, x1, x2, Ψ]

/-! ### Fibers -/

/-- One valid fiber: `|cA|` slots aside onto `tA`, `|cB|` slots onto `acc`, the aside slots back
in order (through `tB`), and the last `|ts|` slots; slots have `|rb|` symbols. -/
def crtRotFib (cA cB ts rb tc tr str acc tA tB : Fin T) : Pr P T Q A U :=
  .seq (crtSlots cA tc rb tr str tA) <| .seq (crtSlots cB tc rb tr str acc) <|
  .seq (crtMv tA tB) <| .seq (crtMv tB acc) (crtSlots ts tc rb tr str acc)

/-- One invalid fiber: all `|cA| + |cB| + |ts|` slots onto `acc`, in order. -/
def crtCopyFib (cA cB ts rb tc tr str acc : Fin T) : Pr P T Q A U :=
  .seq (crtSlots cA tc rb tr str acc) <| .seq (crtSlots cB tc rb tr str acc)
    (crtSlots ts tc rb tr str acc)

section FibLemmas

variable {α : Type*}

/-- The slots output by a rotating fiber. -/
lemma crt_rot_slots (sl : List (List α)) (a b : ℕ) (hs : a + b ≤ sl.length) :
    (sl.drop a).take b ++ sl.take a = (sl.take (a + b)).rotate a := by
  rw [List.rotate_eq_drop_append_take (by simp; omega), List.drop_take, List.take_take]
  simp

lemma crt_take_flatten_append (k : ℕ) (sl : List (List α)) (h : ∀ x ∈ sl, x.length = k)
    (rest : List α) (a : ℕ) (ha : a ≤ sl.length) :
    (sl.flatten ++ rest).take (a * k) = (sl.take a).flatten ∧
      (sl.flatten ++ rest).drop (a * k) = (sl.drop a).flatten ++ rest := by
  have hl := crt_length_flatten_uniform k sl h
  have hak : a * k ≤ sl.flatten.length := by rw [hl]; exact Nat.mul_le_mul_right _ ha
  refine ⟨?_, ?_⟩
  · rw [List.take_append_of_le_length hak, crt_take_flatten_uniform k sl h]
  · rw [List.drop_append_of_le_length hak, crt_drop_flatten_uniform k sl h]

lemma crt_uniform_drop (k : ℕ) (sl : List (List α)) (h : ∀ x ∈ sl, x.length = k) (a : ℕ) :
    ∀ x ∈ sl.drop a, x.length = k := fun x hx => h x (List.mem_of_mem_drop hx)

end FibLemmas

theorem crtRotFib_runs {cA cB ts rb tc tr str acc tA tB : Fin T}
    (hreg : [cA, cB, ts, rb, tc, tr, str, acc, tA, tB].Nodup) (R : Regs T A)
    (htc : R tc = []) (htr : R tr = []) (htA : R tA = []) (htB : R tB = [])
    (sl : List (List (Fin (A + 4)))) (hsl : ∀ x ∈ sl, x.length = (R rb).length)
    (hlen : sl.length = (R cA).length + (R cB).length + (R ts).length)
    (rest : List (Fin (A + 4))) (hstr : R str = sl.flatten ++ rest) :
    crtRuns body (crtRotFib cA cB ts rb tc tr str acc tA tB) R
      (Function.update (Function.update R str rest) acc
        ((((sl.take ((R cA).length + (R cB).length)).rotate (R cA).length ++
          sl.drop ((R cA).length + (R cB).length)).flatten).reverse ++ R acc))
      (sl.length * (8 * (R rb).length + 9) + 16) := by
  have hreg' := hreg
  regs_ne hreg'
  crt_ne_symm
  obtain ⟨a, ha⟩ : ∃ a, (R cA).length = a := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, (R cB).length = b := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c, (R ts).length = c := ⟨_, rfl⟩
  obtain ⟨k, hk⟩ : ∃ k, (R rb).length = k := ⟨_, rfl⟩
  simp only [ha, hb, hc] at hlen ⊢
  simp only [hk] at hsl ⊢
  -- step 1
  obtain ⟨t₁, d₁⟩ := crt_take_flatten_append k sl hsl rest a (by omega)
  have s₁ := crtSlots_runs (body := body) (c := cA) (tc := tc) (r := rb) (tr := tr) (src := str)
    (dst := tA) (by regs_nodup) R htc htr
    (by rw [ha, hk, hstr, List.length_append, crt_length_flatten_uniform k sl hsl]; nlinarith)
  rw [ha, hk, hstr, t₁, d₁, htA, List.append_nil] at s₁
  set R₁ := Function.update (Function.update R str ((sl.drop a).flatten ++ rest)) tA
    ((sl.take a).flatten).reverse with hR₁
  -- step 2
  have hsl₁ := crt_uniform_drop k sl hsl a
  obtain ⟨t₂, d₂⟩ := crt_take_flatten_append k (sl.drop a) hsl₁ rest b (by simp; omega)
  have s₂ := crtSlots_runs (body := body) (c := cB) (tc := tc) (r := rb) (tr := tr) (src := str)
    (dst := acc) (by regs_nodup) R₁ (by simp [*]) (by simp [*])
    (by
      simp only [hR₁, Function.update_of_ne ‹cB ≠ tA›, Function.update_of_ne ‹cB ≠ str›,
        Function.update_of_ne ‹rb ≠ tA›, Function.update_of_ne ‹rb ≠ str›,
        Function.update_of_ne ‹str ≠ tA›, Function.update_self, hb, hk, List.length_append,
        crt_length_flatten_uniform k _ hsl₁, List.length_drop]
      rw [hlen, show a + b + c - a = b + c by omega]
      nlinarith)
  have eR₁ : R₁ str = (sl.drop a).flatten ++ rest := by simp [hR₁, ‹str ≠ tA›]
  have eR₁cB : (R₁ cB).length = b := by simp [hR₁, ‹cB ≠ tA›, ‹cB ≠ str›, hb]
  have eR₁rb : (R₁ rb).length = k := by simp [hR₁, ‹rb ≠ tA›, ‹rb ≠ str›, hk]
  rw [eR₁cB, eR₁rb, eR₁, t₂, d₂, List.drop_drop] at s₂
  set R₂ := Function.update (Function.update R₁ str ((sl.drop (a + b)).flatten ++ rest)) acc
    ((((sl.drop a).take b).flatten).reverse ++ R₁ acc) with hR₂
  -- steps 3 and 4
  have s₃ := crtMv_runs (body := body) ‹tA ≠ tB› R₂
  set R₃ := Function.update (Function.update R₂ tA []) tB ((R₂ tA).reverse ++ R₂ tB) with hR₃
  have s₄ := crtMv_runs (body := body) ‹acc ≠ tB›.symm R₃
  set R₄ := Function.update (Function.update R₃ tB []) acc ((R₃ tB).reverse ++ R₃ acc) with hR₄
  -- step 5
  have hsl₂ := crt_uniform_drop k sl hsl (a + b)
  have hc' : (sl.drop (a + b)).length = c := by simp; omega
  obtain ⟨t₅, d₅⟩ := crt_take_flatten_append k (sl.drop (a + b)) hsl₂ rest c (by omega)
  have eR₄str : R₄ str = (sl.drop (a + b)).flatten ++ rest := by
    simp [hR₄, hR₃, hR₂, ‹str ≠ tA›, ‹str ≠ tB›, ‹str ≠ acc›]
  have eR₄ts : (R₄ ts).length = c := by
    simp [hR₄, hR₃, hR₂, hR₁, ‹ts ≠ tA›, ‹ts ≠ tB›, ‹ts ≠ acc›, ‹ts ≠ str›, hc]
  have eR₄rb : (R₄ rb).length = k := by
    simp [hR₄, hR₃, hR₂, hR₁, ‹rb ≠ tA›, ‹rb ≠ tB›, ‹rb ≠ acc›, ‹rb ≠ str›, hk]
  have s₅ := crtSlots_runs (body := body) (c := ts) (tc := tc) (r := rb) (tr := tr) (src := str)
    (dst := acc) (by regs_nodup) R₄
    (by simp [hR₄, hR₃, hR₂, hR₁, ‹tc ≠ tA›, ‹tc ≠ tB›, ‹tc ≠ acc›, ‹tc ≠ str›, htc])
    (by simp [hR₄, hR₃, hR₂, hR₁, ‹tr ≠ tA›, ‹tr ≠ tB›, ‹tr ≠ acc›, ‹tr ≠ str›, htr])
    (by rw [eR₄ts, eR₄rb, eR₄str, List.length_append, crt_length_flatten_uniform k _ hsl₂, hc']
        nlinarith)
  have hdrop5 : (sl.drop (a + b)).drop c = [] := List.drop_eq_nil_of_le (by rw [hc'])
  have htake5 : (sl.drop (a + b)).take c = sl.drop (a + b) := List.take_of_length_le (by rw [hc'])
  rw [eR₄ts, eR₄rb, eR₄str, t₅, d₅, hdrop5, htake5, List.flatten_nil, List.nil_append] at s₅
  refine crtRuns_mono (crtRuns_congr (crtRuns_seq s₁ (crtRuns_seq s₂ (crtRuns_seq s₃
    (crtRuns_seq s₄ s₅)))) ?_) ?_
  · have hrot := crt_rot_slots sl a b (by omega)
    funext x
    by_cases x1 : x = acc
    · rw [x1]
      simp only [Function.update_self, hR₄, hR₃, hR₂, hR₁, Function.update_of_ne ‹acc ≠ tB›,
        Function.update_of_ne ‹acc ≠ tA›, Function.update_of_ne ‹tB ≠ acc›,
        Function.update_of_ne ‹tB ≠ tA›, Function.update_of_ne ‹tA ≠ acc›,
        Function.update_of_ne ‹tA ≠ str›, Function.update_of_ne ‹tB ≠ str›,
        Function.update_of_ne ‹acc ≠ str›, htB, List.append_nil, List.reverse_reverse]
      rw [← hrot]
      simp
    · rw [Function.update_of_ne x1]
      by_cases x2 : x = str
      · rw [x2, Function.update_of_ne ‹str ≠ acc›, Function.update_self, Function.update_self]
      · rw [Function.update_of_ne x2]
        simp only [hR₄, hR₃, hR₂, hR₁, Function.update_apply]
        split_ifs <;> simp_all
  · have hta : ((sl.take a).flatten).length = a * k := by
      rw [crt_length_flatten_uniform k _ (fun x hx => hsl x (List.mem_of_mem_take hx)),
        List.length_take, Nat.min_eq_left (by omega)]
    have l₂ : (R₂ tA).length = a * k := by
      simp [hR₂, hR₁, ‹tA ≠ acc›, ‹tA ≠ str›, hta]
    have l₃ : (R₃ tB).length = a * k := by
      simp [hR₃, Function.update_of_ne ‹tB ≠ tA›, hR₂, hR₁, ‹tB ≠ acc›, ‹tB ≠ str›, htB]
      simpa [hR₂, hR₁, ‹tA ≠ acc›, ‹tA ≠ str›] using hta
    rw [l₂, l₃, hlen]
    nlinarith


theorem crtCopyFib_runs {cA cB ts rb tc tr str acc : Fin T}
    (hreg : [cA, cB, ts, rb, tc, tr, str, acc].Nodup) (R : Regs T A)
    (htc : R tc = []) (htr : R tr = [])
    (sl : List (List (Fin (A + 4)))) (hsl : ∀ x ∈ sl, x.length = (R rb).length)
    (hlen : sl.length = (R cA).length + (R cB).length + (R ts).length)
    (rest : List (Fin (A + 4))) (hstr : R str = sl.flatten ++ rest) :
    crtRuns body (crtCopyFib cA cB ts rb tc tr str acc) R
      (Function.update (Function.update R str rest) acc (sl.flatten.reverse ++ R acc))
      (sl.length * (4 * (R rb).length + 9) + 12) := by
  have hreg' := hreg
  regs_ne hreg'
  crt_ne_symm
  obtain ⟨a, ha⟩ : ∃ a, (R cA).length = a := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, (R cB).length = b := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c, (R ts).length = c := ⟨_, rfl⟩
  obtain ⟨k, hk⟩ : ∃ k, (R rb).length = k := ⟨_, rfl⟩
  simp only [ha, hb, hc] at hlen ⊢
  simp only [hk] at hsl ⊢
  obtain ⟨t₁, d₁⟩ := crt_take_flatten_append k sl hsl rest a (by omega)
  have s₁ := crtSlots_runs (body := body) (c := cA) (tc := tc) (r := rb) (tr := tr) (src := str)
    (dst := acc) (by regs_nodup) R htc htr
    (by rw [ha, hk, hstr, List.length_append, crt_length_flatten_uniform k sl hsl]; nlinarith)
  rw [ha, hk, hstr, t₁, d₁] at s₁
  set R₁ := Function.update (Function.update R str ((sl.drop a).flatten ++ rest)) acc
    (((sl.take a).flatten).reverse ++ R acc) with hR₁
  have hsl₁ := crt_uniform_drop k sl hsl a
  obtain ⟨t₂, d₂⟩ := crt_take_flatten_append k (sl.drop a) hsl₁ rest b (by simp; omega)
  have e₁ : R₁ str = (sl.drop a).flatten ++ rest := by simp [hR₁, ‹str ≠ acc›]
  have e₁b : (R₁ cB).length = b := by simp [hR₁, ‹cB ≠ acc›, ‹cB ≠ str›, hb]
  have e₁k : (R₁ rb).length = k := by simp [hR₁, ‹rb ≠ acc›, ‹rb ≠ str›, hk]
  have s₂ := crtSlots_runs (body := body) (c := cB) (tc := tc) (r := rb) (tr := tr) (src := str)
    (dst := acc) (by regs_nodup) R₁ (by simp [*]) (by simp [*])
    (by
      rw [e₁b, e₁k, e₁, List.length_append, crt_length_flatten_uniform k _ hsl₁, List.length_drop,
        hlen, show a + b + c - a = b + c by omega]
      nlinarith)
  rw [e₁b, e₁k, e₁, t₂, d₂, List.drop_drop] at s₂
  set R₂ := Function.update (Function.update R₁ str ((sl.drop (a + b)).flatten ++ rest)) acc
    ((((sl.drop a).take b).flatten).reverse ++ R₁ acc) with hR₂
  have hsl₂ := crt_uniform_drop k sl hsl (a + b)
  have hc' : (sl.drop (a + b)).length = c := by simp; omega
  obtain ⟨t₃, d₃⟩ := crt_take_flatten_append k (sl.drop (a + b)) hsl₂ rest c (by omega)
  have e₂ : R₂ str = (sl.drop (a + b)).flatten ++ rest := by simp [hR₂, ‹str ≠ acc›]
  have e₂c : (R₂ ts).length = c := by
    simp [hR₂, hR₁, ‹ts ≠ acc›, ‹ts ≠ str›, hc]
  have e₂k : (R₂ rb).length = k := by simp [hR₂, hR₁, ‹rb ≠ acc›, ‹rb ≠ str›, hk]
  have s₃ := crtSlots_runs (body := body) (c := ts) (tc := tc) (r := rb) (tr := tr) (src := str)
    (dst := acc) (by regs_nodup) R₂ (by simp [*]) (by simp [*])
    (by rw [e₂c, e₂k, e₂, List.length_append, crt_length_flatten_uniform k _ hsl₂, hc']; nlinarith)
  have hdrop3 : (sl.drop (a + b)).drop c = [] := List.drop_eq_nil_of_le (by rw [hc'])
  have htake3 : (sl.drop (a + b)).take c = sl.drop (a + b) := List.take_of_length_le (by rw [hc'])
  rw [e₂c, e₂k, e₂, t₃, d₃, hdrop3, htake3, List.flatten_nil, List.nil_append] at s₃
  refine crtRuns_mono (crtRuns_congr (crtRuns_seq s₁ (crtRuns_seq s₂ s₃)) ?_) ?_
  · have hsplit : sl = sl.take a ++ (sl.drop a).take b ++ sl.drop (a + b) := by
      rw [List.append_assoc, ← List.drop_drop, List.take_append_drop, List.take_append_drop]
    funext x
    by_cases x1 : x = acc
    · rw [x1]
      simp only [Function.update_self, hR₂, hR₁]
      have hf : sl.flatten = (sl.take a).flatten ++ ((sl.drop a).take b).flatten ++
          (sl.drop (a + b)).flatten := by
        rw [← List.flatten_append, ← List.flatten_append, ← hsplit]
      rw [hf]
      simp
    · rw [Function.update_of_ne x1]
      by_cases x2 : x = str
      · rw [x2, Function.update_of_ne ‹str ≠ acc›, Function.update_self, Function.update_self]
      · rw [Function.update_of_ne x2]
        simp [hR₂, hR₁, x1, x2]
  · rw [hlen]; nlinarith

/-! ### Offsets -/

/-- Adding `μ` to a representative `x ∈ [0, s]` modulo `s`, with representatives in `[0, s]`. -/
def crtLoStep (s μ x : ℕ) : ℕ := if x + μ ≤ s then x + μ else x + μ - s

/-- The offset after `K` additions of `μ`. -/
def crtLo (s μ K : ℕ) : ℕ := (crtLoStep s μ)^[K] 0

lemma crtLoStep_le {s μ x : ℕ} (hμ : μ ≤ s) (hx : x ≤ s) : crtLoStep s μ x ≤ s := by
  unfold crtLoStep; split_ifs <;> omega

lemma crtLo_le {s μ : ℕ} (hμ : μ ≤ s) : ∀ K, crtLo s μ K ≤ s
  | 0 => by simp [crtLo]
  | K + 1 => by
      rw [crtLo, Function.iterate_succ_apply']
      exact crtLoStep_le hμ (crtLo_le hμ K)

lemma crtLo_succ (s μ K : ℕ) : crtLo s μ (K + 1) = crtLoStep s μ (crtLo s μ K) := by
  rw [crtLo, crtLo, Function.iterate_succ_apply']

/-- The offset is congruent to `μ K` modulo `s`. -/
lemma crtLo_cast (s μ : ℕ) : ∀ K, ((crtLo s μ K : ℕ) : ZMod s) = (μ : ZMod s) * K
  | 0 => by simp [crtLo]
  | K + 1 => by
      rw [crtLo_succ, crtLoStep]
      split_ifs with h
      · push_cast; rw [crtLo_cast s μ K]; ring
      · rw [Nat.cast_sub (by omega)]
        push_cast; rw [crtLo_cast s μ K, ZMod.natCast_self]; ring

/-- Pop `hi`; push a tick onto `lo` if `hi` was nonempty and onto `ov` otherwise. -/
def crtOffStep (lo hi ov : Fin T) : Act T Q A U :=
  .pop (.rt hi) (fun v o => { v with flag := o.isSome })
    (.branch (·.flag) (.push (.rt lo) (fun _ => tick) .done) (.push (.rt ov) (fun _ => tick) .done))

/-- Add `|mu|` to the offset `lo` (complement `hi`) modulo `|lo| + |hi|`: one tick from `hi`
to `lo` per symbol of `mu`, overflow ticks onto `ov`; on overflow, move `lo` onto `hi` and the
overflow count back from `hi` to `lo`. -/
def crtOffP (mu tc lo hi ov t : Fin T) : Pr P T Q A U :=
  .seq (crtFor mu tc (.act (crtOffStep lo hi ov)))
    (crtIfR ov (.seq (crtMv lo hi) (.seq (crtCMv ov t hi lo) (uclear ov))) (.act .done))

theorem crtOffP_runs {mu tc lo hi ov t : Fin T} (hreg : [mu, tc, lo, hi, ov, t].Nodup)
    (R : Regs T A) (s x : ℕ) (hx : x ≤ s) (hμ : (R mu).length ≤ s)
    (hlo : R lo = List.replicate x tick) (hhi : R hi = List.replicate (s - x) tick)
    (hov : R ov = []) (htc : R tc = []) (ht : R t = []) :
    crtRuns body (crtOffP mu tc lo hi ov t) R
      (Function.update (Function.update R lo (List.replicate (crtLoStep s (R mu).length x) tick))
        hi (List.replicate (s - crtLoStep s (R mu).length x) tick))
      (14 * (R mu).length + 2 * s + 24) := by
  have hreg' := hreg
  regs_ne hreg'
  crt_ne_symm
  obtain ⟨μ, hμd⟩ : ∃ μ, (R mu).length = μ := ⟨_, rfl⟩
  simp only [hμd] at hμ ⊢
  let Ψ : ℕ → Regs T A := fun j => Function.update (Function.update (Function.update R lo
    (List.replicate (min (x + j) s) tick)) hi (List.replicate (s - min (x + j) s) tick)) ov
    (List.replicate (x + j - s) tick)
  have hit : crtIter (body := body) (.act (crtOffStep lo hi ov)) mu tc Ψ 1 μ := by
    intro j hj R' hR'
    have hRhi : R' hi = List.replicate (s - min (x + j) s) tick := by
      rw [hR' hi ‹mu ≠ hi›.symm ‹tc ≠ hi›.symm]; simp [Ψ, ‹hi ≠ ov›]
    have hRlo : R' lo = List.replicate (min (x + j) s) tick := by
      rw [hR' lo ‹mu ≠ lo›.symm ‹tc ≠ lo›.symm]; simp [Ψ, ‹lo ≠ ov›, ‹lo ≠ hi›]
    have hRov : R' ov = List.replicate (x + j - s) tick := by
      rw [hR' ov ‹mu ≠ ov›.symm ‹tc ≠ ov›.symm]; simp [Ψ]
    refine crtRuns_act _ fun v S hS => ?_
    by_cases hlt : x + j < s
    · have hne : R' hi = tick :: List.replicate (s - min (x + j) s - 1) tick := by
        rw [hRhi, ← List.replicate_succ]; congr 1; omega
      refine ⟨{ v with flag := true }, rfl, ?_⟩
      simp only [crtOffStep, Action.run, mk_var, mk_stk, get_rt, hS, hne, List.head?_cons,
        Option.isSome_some, update_rt, store_mk, List.tail_cons, ↓reduceIte]
      congr 2
      funext k
      by_cases hk : k = mu ∨ k = tc
      · have h1 : k ≠ lo := by rcases hk with h | h <;> rw [h] <;> assumption
        have h2 : k ≠ hi := by rcases hk with h | h <;> rw [h] <;> assumption
        simp [hk, h1, h2]
      · rw [not_or] at hk
        simp only [hk.1, hk.2, or_self, ↓reduceIte, Ψ]
        by_cases k1 : k = lo
        · rw [k1]; simp [‹lo ≠ ov›, ‹lo ≠ hi›, hRlo, ← List.replicate_succ]; omega
        · by_cases k2 : k = hi
          · rw [k2]; simp [‹hi ≠ ov›, ‹hi ≠ lo›, ‹lo ≠ hi›]; omega
          · by_cases k3 : k = ov
            · rw [k3]; simp [‹ov ≠ lo›, ‹ov ≠ hi›, hRov]; omega
            · simp [k1, k2, k3, hR' k hk.1 hk.2, Ψ]
    · have hnil : R' hi = [] := by rw [hRhi]; simp; omega
      refine ⟨{ v with flag := false }, rfl, ?_⟩
      simp only [crtOffStep, Action.run, mk_var, mk_stk, get_rt, hS, hnil, List.head?_nil,
        Option.isSome_none, update_rt, store_mk, List.tail_nil, Bool.false_eq_true, ↓reduceIte]
      congr 2
      funext k
      by_cases hk : k = mu ∨ k = tc
      · have h1 : k ≠ ov := by rcases hk with h | h <;> rw [h] <;> assumption
        have h2 : k ≠ hi := by rcases hk with h | h <;> rw [h] <;> assumption
        simp [hk, h1, h2]
      · rw [not_or] at hk
        simp only [hk.1, hk.2, or_self, ↓reduceIte, Ψ]
        by_cases k1 : k = ov
        · rw [k1]; simp [‹ov ≠ hi›, hRov, ← List.replicate_succ]; omega
        · by_cases k2 : k = hi
          · rw [k2]; simp [‹hi ≠ ov›, ‹ov ≠ hi›]; omega
          · by_cases k3 : k = lo
            · rw [k3]; simp [‹lo ≠ ov›, ‹lo ≠ hi›, hRlo]; omega
            · simp [k1, k2, k3, hR' k hk.1 hk.2, Ψ]
  have h₁ := crtFor_runs (body := body) ‹mu ≠ tc› hit (R mu) hμd
  have e0 : crtForRegs mu tc (Ψ 0) (R mu) [] = R := by
    funext k
    by_cases k1 : k = mu
    · rw [k1]; simp [crtForRegs]
    · by_cases k2 : k = tc
      · rw [k2]; simp [crtForRegs, ‹tc ≠ mu›, htc]
      · simp only [crtForRegs, k1, k2, ↓reduceIte, Ψ, Nat.add_zero, Nat.min_eq_left hx]
        by_cases k3 : k = ov
        · rw [k3]; simp [hov]; omega
        · rw [Function.update_of_ne k3]
          by_cases k4 : k = hi
          · rw [k4]; simp [hhi]
          · rw [Function.update_of_ne k4]
            by_cases k5 : k = lo
            · rw [k5]; simp [hlo]
            · simp [k5]
  rw [e0] at h₁
  set R₁ := crtForRegs mu tc (Ψ μ) (R mu) [] with hR₁
  have hR₁lo : R₁ lo = List.replicate (min (x + μ) s) tick := by
    simp [hR₁, crtForRegs, ‹lo ≠ mu›, ‹lo ≠ tc›, Ψ, ‹lo ≠ ov›, ‹lo ≠ hi›]
  have hR₁hi : R₁ hi = List.replicate (s - min (x + μ) s) tick := by
    simp [hR₁, crtForRegs, ‹hi ≠ mu›, ‹hi ≠ tc›, Ψ, ‹hi ≠ ov›]
  have hR₁ov : R₁ ov = List.replicate (x + μ - s) tick := by
    simp [hR₁, crtForRegs, ‹ov ≠ mu›, ‹ov ≠ tc›, Ψ]
  have hR₁t : R₁ t = [] := by
    simp [hR₁, crtForRegs, ‹t ≠ mu›, ‹t ≠ tc›, Ψ, ‹t ≠ ov›, ‹t ≠ hi›, ‹t ≠ lo›, ht]
  have hR₁oth : ∀ k, k ≠ lo → k ≠ hi → k ≠ ov → R₁ k = R k := by
    intro k k1 k2 k3
    by_cases k4 : k = mu
    · rw [k4]; simp [hR₁, crtForRegs]
    · by_cases k5 : k = tc
      · rw [k5]; simp [hR₁, crtForRegs, ‹tc ≠ mu›, htc]
      · simp [hR₁, crtForRegs, k4, k5, Ψ, k1, k2, k3]
  by_cases hover : x + μ ≤ s
  · -- no overflow
    have hov0 : R₁ ov = [] := by rw [hR₁ov]; simp; omega
    have h₂ : crtRuns body (crtIfR ov (.seq (crtMv lo hi) (.seq (crtCMv ov t hi lo) (uclear ov)))
        (.act .done)) R₁ R₁ (2 * s + 6 * μ + 12) :=
      crtRuns_mono (crtIfR_runs (fun h => absurd hov0 h) (fun _ =>
        crtRuns_act _ fun v S hS => ⟨v, rfl, by rw [← hS]; rfl⟩)) (by omega)
    refine crtRuns_mono (crtRuns_congr (crtRuns_seq h₁ h₂) ?_) (by omega)
    funext k
    by_cases k1 : k = hi
    · rw [k1, Function.update_self, hR₁hi, crtLoStep, ite_eq_left hover, Nat.min_eq_left hover]
    · rw [Function.update_of_ne k1]
      by_cases k2 : k = lo
      · rw [k2, Function.update_self, hR₁lo, crtLoStep, ite_eq_left hover, Nat.min_eq_left hover]
      · rw [Function.update_of_ne k2]
        by_cases k3 : k = ov
        · rw [k3, hov0, hov]
        · exact hR₁oth k k2 k1 k3
  · -- overflow
    replace hover : s < x + μ := by omega
    have hmin : min (x + μ) s = s := Nat.min_eq_right hover.le
    rw [hmin] at hR₁lo hR₁hi
    simp only [Nat.sub_self, List.replicate_zero] at hR₁hi
    have hovne : R₁ ov ≠ [] := by rw [hR₁ov]; simp; omega
    have m₁ := crtMv_runs (body := body) ‹lo ≠ hi› R₁
    set R₂ := Function.update (Function.update R₁ lo []) hi ((R₁ lo).reverse ++ R₁ hi) with hR₂
    have hR₂hi : R₂ hi = List.replicate s tick := by simp [hR₂, hR₁lo, hR₁hi]
    have hR₂ov : R₂ ov = List.replicate (x + μ - s) tick := by
      simp [hR₂, ‹ov ≠ hi›, ‹ov ≠ lo›, hR₁ov]
    have m₂ := crtCMv_runs (body := body) (c := ov) (t := t) (src := hi) (dst := lo)
      (by regs_nodup) R₂ (by simp [hR₂, ‹t ≠ hi›, ‹t ≠ lo›, hR₁t])
      (by rw [hR₂ov, hR₂hi]; simp; omega)
    set R₃ := Function.update (Function.update R₂ hi ((R₂ hi).drop (R₂ ov).length)) lo
      (((R₂ hi).take (R₂ ov).length).reverse ++ R₂ lo) with hR₃
    have m₃ := crtClear_runs (body := body) ov R₃
    have h₂ : crtRuns body (crtIfR ov (.seq (crtMv lo hi) (.seq (crtCMv ov t hi lo) (uclear ov)))
        (.act .done)) R₁ (Function.update R₃ ov []) (2 * s + 8 * μ + 20) := by
      refine crtRuns_mono (crtIfR_runs (fun _ => crtRuns_seq m₁ (crtRuns_seq m₂ m₃))
        (fun h => absurd h hovne)) ?_
      have l1 : (R₁ lo).length = s := by rw [hR₁lo]; simp
      have l2 : (R₂ ov).length = x + μ - s := by rw [hR₂ov]; simp
      have l3 : (R₃ ov).length = x + μ - s := by
        rw [hR₃, Function.update_of_ne ‹ov ≠ lo›, Function.update_of_ne ‹ov ≠ hi›, l2]
      rw [l1, l2, l3]
      omega
    refine crtRuns_mono (crtRuns_congr (crtRuns_seq h₁ h₂) ?_) (by omega)
    have hstep : crtLoStep s μ x = x + μ - s := by rw [crtLoStep, ite_eq_right (by omega)]
    rw [hstep]
    funext k
    by_cases k1 : k = ov
    · rw [k1, Function.update_self, Function.update_of_ne ‹ov ≠ hi›,
        Function.update_of_ne ‹ov ≠ lo›, hov]
    · by_cases k2 : k = lo
      · rw [k2]
        simp only [Function.update_of_ne ‹lo ≠ ov›, Function.update_of_ne ‹lo ≠ hi›,
          Function.update_self, hR₃, hR₂hi, hR₂ov, List.take_replicate, List.reverse_replicate,
          List.length_replicate]
        have : R₂ lo = [] := by
          rw [hR₂, Function.update_of_ne ‹lo ≠ hi›, Function.update_self]
        rw [this, List.append_nil]
        congr 1
        omega
      · by_cases k3 : k = hi
        · rw [k3]
          simp only [Function.update_of_ne ‹hi ≠ ov›, Function.update_of_ne ‹hi ≠ lo›,
            Function.update_self, hR₃, hR₂hi, hR₂ov, List.drop_replicate, List.length_replicate]
        · simp only [hR₃, hR₂, Function.update_of_ne k1, Function.update_of_ne k2,
            Function.update_of_ne k3]
          exact hR₁oth k k2 k3 k1

/-! ### The rotation on contents -/

section RotSem

variable {d : ℕ} (a s : Fin d → ℕ)

/-- The rotation amount of a fiber with `K` valid fibers before it: `s - crtLo s μ K` forward,
`crtLo s μ K` inverse. -/
def crtShift (fwd : Bool) (S μ K : ℕ) : ℕ := if fwd then S - crtLo S μ K else crtLo S μ K

/-- The mixed-radix value `∑_{j < i} y j · prefixProd s j` of the controls of `y`. -/
def crtKI (i : ℕ) (y : Fin d → ℕ) : ℕ := ∑ j ∈ crtLow i, y j * prefixProd s j

/-- The content after the rotation pass for target `i`: at coordinates `y` with valid controls
and valid target, the old content at target coordinate `(y_i + shift) mod s_i`. -/
def crtRotC {α : Type*} (i : ℕ) (hi : i < d) (μ : ℕ) (fwd : Bool) (C : (Fin d → ℕ) → α)
    (y : Fin d → ℕ) : α :=
  if (∀ j : Fin d, j.val < i → y j < s j) ∧ y ⟨i, hi⟩ < s ⟨i, hi⟩ then
    C (Function.update y ⟨i, hi⟩
      ((y ⟨i, hi⟩ + crtShift fwd (s ⟨i, hi⟩) μ (crtKI s i y)) % s ⟨i, hi⟩))
  else C y

variable {α : Type*}

lemma crt_rot_getElem (sl : List (List α)) (t S r : ℕ) (ht : sl.length = t) (hS : S ≤ t) :
    (sl.take S).rotate r ++ sl.drop S =
      (List.range t).map fun z => sl.getD (if z < S then (z + r) % S else z) [] := by
  apply List.ext_getElem
  · simp [ht]; omega
  · intro z h₁ h₂
    simp only [List.getElem_map, List.getElem_range]
    by_cases hz : z < S
    · have hS0 : 0 < S := by omega
      rw [List.getElem_append_left (by simp; omega), List.getElem_rotate, ite_eq_left hz]
      simp only [List.length_take, Nat.min_eq_left (by omega : S ≤ sl.length), List.getElem_take]
      rw [List.getD_eq_getElem _ _ (by have := Nat.mod_lt (z + r) hS0; omega)]
    · rw [List.getElem_append_right (by simp; omega), List.getElem_drop, ite_eq_right hz]
      rw [List.getD_eq_getElem _ _ (by simp at h₁; omega)]
      congr 1; simp; omega

/-- The slots of the fiber `F` of the box of `C` along `crtRevAx i ++ (⟨i, hi⟩ : Fin d) :: post`. -/
def crtSlotsOf (i : ℕ) (hi : i < d) (post : List (Fin d)) (C : (Fin d → ℕ) → List α) (F : ℕ) :
    List (List α) :=
  (List.range (2 ^ a ⟨i, hi⟩)).map fun z =>
    (crtBox a post C (Function.update (crtDec a (crtRevAx i) F 0) ⟨i, hi⟩ z)).flatten

lemma crt_layout_mem {i : ℕ} (hi : i < d) {post : List (Fin d)}
    (hnd : (crtRevAx i ++ (⟨i, hi⟩ : Fin d) :: post).Nodup) :
    (⟨i, hi⟩ : Fin d) ∉ post ∧ ∀ j : Fin d, j.val < i → j ∉ post := by
  rw [List.nodup_append, List.nodup_cons] at hnd
  refine ⟨hnd.2.1.1, fun j hj hjp => ?_⟩
  exact hnd.2.2 j ((crt_mem_revAx j).2 hj) j (List.mem_cons_of_mem _ hjp) rfl

/-- One fiber of the rotated content. -/
theorem crtRot_fiber {i : ℕ} (hi : i < d) {post : List (Fin d)}
    (hnd : (crtRevAx i ++ (⟨i, hi⟩ : Fin d) :: post).Nodup) (hs : s ⟨i, hi⟩ ≤ 2 ^ a ⟨i, hi⟩)
    (μ : ℕ) (fwd : Bool) (C : (Fin d → ℕ) → List α) {F : ℕ} (hF : F < 2 ^ crtPre a i) :
    (crtBox a ((⟨i, hi⟩ : Fin d) :: post) (crtRotC s i hi μ fwd C) (crtDec a (crtRevAx i) F 0)).flatten =
      if crtVal a s i F then
        (((crtSlotsOf a i hi post C F).take (s ⟨i, hi⟩)).rotate
          (crtShift fwd (s ⟨i, hi⟩) μ (crtK a s i F)) ++
          (crtSlotsOf a i hi post C F).drop (s ⟨i, hi⟩)).flatten
      else (crtSlotsOf a i hi post C F).flatten := by
  obtain ⟨hIp, hjp⟩ := crt_layout_mem hi hnd
  set I : Fin d := ⟨i, hi⟩ with hI
  set y₀ := crtDec a (crtRevAx i) F 0 with hy₀
  have hy₀c : ∀ j : Fin d, j.val < i → y₀ j = crtDig a j F := fun j hj => by
    rw [hy₀, crtDec_revAx a i hi.le F hF]; simp [hj]
  have hval : crtVal a s i F = true ↔ ∀ j : Fin d, j.val < i → y₀ j < s j := by
    simp only [crtVal, decide_eq_true_eq]
    exact ⟨fun H j hj => hy₀c j hj ▸ H j hj, fun H j hj => hy₀c j hj ▸ H j hj⟩
  -- coordinates inside a slot
  have hw : ∀ e z, ∀ j : Fin d, j.val < i → crtDec a post e (Function.update y₀ I z) j = y₀ j := by
    intro e z j hj
    rw [crtDec_apply_of_not_mem a post e _ j (hjp j hj), Function.update_of_ne]
    intro h; rw [h] at hj; simp [hI] at hj
  have hwI : ∀ e z, crtDec a post e (Function.update y₀ I z) I = z := by
    intro e z; rw [crtDec_apply_of_not_mem a post e _ I hIp, Function.update_self]
  have hK : ∀ e z, crtKI s i (crtDec a post e (Function.update y₀ I z)) = crtK a s i F := by
    intro e z
    simp only [crtKI, crtK]
    refine Finset.sum_congr rfl fun j hj => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    rw [hw e z j hj, hy₀c j hj]
  have hupd : ∀ e z v, Function.update (crtDec a post e (Function.update y₀ I z)) I v =
      crtDec a post e (Function.update y₀ I v) := by
    intro e z v
    rw [← crtDec_update_of_not_mem a post e _ I v hIp, Function.update_idem]
  rw [crtBox_cons, crt_flatten_flatMap]
  by_cases hv : crtVal a s i F = true
  · rw [ite_eq_left hv, crt_rot_getElem _ (2 ^ a I) _ _ (by simp [crtSlotsOf, hI]) hs, List.flatMap_def]
    congr 1
    refine List.map_congr_left fun z hz => ?_
    have hz' := List.mem_range.1 hz
    have hσ : (if z < s I then (z + crtShift fwd (s I) μ (crtK a s i F)) % s I else z) < 2 ^ a I := by
      split_ifs with h
      · exact lt_of_lt_of_le (Nat.mod_lt _ (by omega)) hs
      · exact hz'
    rw [List.getD_eq_getElem _ _ (by simp [crtSlotsOf]; exact hσ)]
    simp only [crtSlotsOf, List.getElem_map, List.getElem_range]
    congr 1
    rw [crtBox, crtBox]
    refine List.map_congr_left fun e _ => ?_
    rw [crtRotC]
    have hvalw : (∀ j : Fin d, j.val < i → crtDec a post e (Function.update y₀ I z) j < s j) := by
      intro j hj; rw [hw e z j hj]; exact (hval.1 hv) j hj
    by_cases hzs : z < s I
    · rw [ite_eq_left ⟨hvalw, by rw [hwI]; exact hzs⟩, ite_eq_left hzs, hwI, hK, hupd]
    · rw [ite_eq_right (fun h => hzs (by have := h.2; rwa [hwI] at this)), ite_eq_right hzs]
  · rw [ite_eq_right hv, crtSlotsOf, List.flatMap_def]
    congr 1
    refine List.map_congr_left fun z _ => ?_
    congr 1
    rw [crtBox, crtBox]
    refine List.map_congr_left fun e _ => ?_
    rw [crtRotC, ite_eq_right]
    rintro ⟨h, _⟩
    exact hv ((hval.2) fun j hj => by rw [← hw e z j hj]; exact h j hj)

/-- The box along `crtRevAx i ++ (⟨i, hi⟩ : Fin d) :: post`, flattened, as a list of fibers. -/
lemma crtBox_fibers (i : ℕ) (hi : i < d) (post : List (Fin d)) (C : (Fin d → ℕ) → List α) :
    (crtBox a (crtRevAx i ++ (⟨i, hi⟩ : Fin d) :: post) C 0).flatten =
      (List.range (2 ^ crtPre a i)).flatMap fun F =>
        (crtBox a ((⟨i, hi⟩ : Fin d) :: post) C (crtDec a (crtRevAx i) F 0)).flatten := by
  rw [crtBox_append, crt_flatten_flatMap, crtW_revAx a i hi.le]

lemma crtSlotsOf_flatten (i : ℕ) (hi : i < d) (post : List (Fin d)) (C : (Fin d → ℕ) → List α)
    (F : ℕ) :
    (crtSlotsOf a i hi post C F).flatten =
      (crtBox a ((⟨i, hi⟩ : Fin d) :: post) C (crtDec a (crtRevAx i) F 0)).flatten := by
  rw [crtBox_cons, crt_flatten_flatMap, crtSlotsOf, List.flatMap_def]

end RotSem

/-! ### Setup of a rotation pass -/

/-- The registers of a rotation pass: the control bounds and mask `sg`, `mq` (the first
`|preU|` bits of `sig`, `msk`), the slot length `rbU` (`2 ^ |postU| · |zr|` ticks), the
invalid target values `tsU` (`2 ^ |aI| - |sI|` ticks) and the offset complement `hi` (`|sI|`
ticks); spares `u₁`, `u₂`. -/
def crtRotSetup (sig msk preU postU aI sI zr rbU tsU hi u₁ u₂ sg mq : Fin T) : Pr P T Q A U :=
  .seq (crtCpy preU u₁ sig sg u₂) <| .seq (crtCpy preU u₁ msk mq u₂) <|
  .seq (ucopy zr rbU u₁) <| .seq (upow2 postU rbU u₁ u₂) <|
  .seq (crtPush tsU tick) <| .seq (upow2 aI tsU u₁ u₂) <| .seq (usub sI tsU u₁) (ucopy sI hi u₁)

/-- The register file after `crtRotSetup`. -/
def crtRotSetupRegs (R : Regs T A) (sig msk preU postU aI sI zr rbU tsU hi sg mq : Fin T) :
    Regs T A :=
  Function.update (Function.update (Function.update (Function.update (Function.update R
    sg ((R sig).take (R preU).length)) mq ((R msk).take (R preU).length))
    rbU (List.replicate (2 ^ (R postU).length * (R zr).length) tick))
    tsU (List.replicate (2 ^ (R aI).length - (R sI).length) tick))
    hi (List.replicate (R sI).length tick)

theorem crtRotSetup_runs {sig msk preU postU aI sI zr rbU tsU hi u₁ u₂ sg mq : Fin T}
    (hreg : [sig, msk, preU, postU, aI, sI, zr, rbU, tsU, hi, u₁, u₂, sg, mq].Nodup)
    (R : Regs T A) (hsg : R sg = []) (hmq : R mq = []) (hrb : R rbU = []) (hts : R tsU = [])
    (hhi : R hi = []) (hu₁ : R u₁ = []) (hu₂ : R u₂ = [])
    (hpre₁ : (R preU).length ≤ (R sig).length) (hpre₂ : (R preU).length ≤ (R msk).length) :
    crtRuns body (crtRotSetup sig msk preU postU aI sI zr rbU tsU hi u₁ u₂ sg mq) R
      (crtRotSetupRegs R sig msk preU postU aI sI zr rbU tsU hi sg mq)
      (12 * (R preU).length + 8 * (R zr).length + 4 * (2 ^ (R postU).length * (R zr).length) +
        9 * (R postU).length + 4 * 2 ^ (R aI).length + 9 * (R aI).length +
        8 * (R sI).length + 40) := by
  have hreg' := hreg
  regs_ne hreg'
  crt_ne_symm
  have s₁ := crtCpy_runs (body := body) (c := preU) (t := u₁) (src := sig) (dst := sg) (u := u₂)
    (by regs_nodup) R hu₁ hu₂ hpre₁
  set R₁ := Function.update R sg ((R sig).take (R preU).length ++ R sg) with hR₁
  have s₂ := crtCpy_runs (body := body) (c := preU) (t := u₁) (src := msk) (dst := mq) (u := u₂)
    (by regs_nodup) R₁ (by simp [*]) (by simp [*]) (by simp [*])
  set R₂ := Function.update R₁ mq ((R₁ msk).take (R₁ preU).length ++ R₁ mq) with hR₂
  have s₃ := crtUcopy_runs (body := body) (a := zr) (b := rbU) (t := u₁) (by assumption)
    (by assumption) (by assumption) R₂ (by simp [*])
  set R₃ := Function.update R₂ rbU (List.replicate (R₂ zr).length tick ++ R₂ rbU) with hR₃
  have s₄ := crtUpow2_runs (body := body) (a := postU) (b := rbU) (t₁ := u₁) (t₂ := u₂)
    (by regs_nodup) R₃ (by simp [*]) (by simp [*])
  set R₄ := Function.update R₃ rbU ((R₃ rbU).flatMap (List.replicate (2 ^ (R₃ postU).length)))
    with hR₄
  have s₅ := crtPush_runs (body := body) tsU tick R₄
  set R₅ := Function.update R₄ tsU (tick :: R₄ tsU) with hR₅
  have s₆ := crtUpow2_runs (body := body) (a := aI) (b := tsU) (t₁ := u₁) (t₂ := u₂)
    (by regs_nodup) R₅ (by simp [*])
    (by simp [*])
  set R₆ := Function.update R₅ tsU ((R₅ tsU).flatMap (List.replicate (2 ^ (R₅ aI).length)))
    with hR₆
  have s₇ := crtUsub_runs (body := body) (a := sI) (b := tsU) (t := u₁) (by assumption)
    (by assumption) (by assumption) R₆ (by simp [*])
  set R₇ := Function.update R₆ tsU ((R₆ tsU).drop (R₆ sI).length) with hR₇
  have s₈ := crtUcopy_runs (body := body) (a := sI) (b := hi) (t := u₁) (by assumption)
    (by assumption) (by assumption) R₇ (by simp [*])
  refine crtRuns_mono (crtRuns_congr (crtRuns_seq s₁ (crtRuns_seq s₂ (crtRuns_seq s₃
    (crtRuns_seq s₄ (crtRuns_seq s₅ (crtRuns_seq s₆ (crtRuns_seq s₇ s₈))))))) ?_) ?_
  · funext k
    by_cases k1 : k = hi
    · rw [k1]
      simp (disch := assumption) only [crtRotSetupRegs, hR₇, hR₆, hR₅, hR₄, hR₃, hR₂, hR₁,
        Function.update_self, Function.update_of_ne, hhi, List.append_nil]
    by_cases k2 : k = tsU
    · rw [k2]
      simp (disch := assumption) only [crtRotSetupRegs, hR₇, hR₆, hR₅, hR₄, hR₃, hR₂, hR₁,
        Function.update_self, Function.update_of_ne, hts, List.flatMap_singleton,
        List.drop_replicate]
    by_cases k3 : k = rbU
    · rw [k3]
      simp (disch := assumption) only [crtRotSetupRegs, hR₇, hR₆, hR₅, hR₄, hR₃, hR₂, hR₁,
        Function.update_self, Function.update_of_ne, hrb, List.append_nil,
        flatMap_replicate_of_replicate, Nat.mul_comm]
    by_cases k4 : k = mq
    · rw [k4]
      simp (disch := assumption) only [crtRotSetupRegs, hR₇, hR₆, hR₅, hR₄, hR₃, hR₂, hR₁,
        Function.update_self, Function.update_of_ne, hmq, List.append_nil]
    by_cases k5 : k = sg
    · rw [k5]
      simp (disch := assumption) only [crtRotSetupRegs, hR₇, hR₆, hR₅, hR₄, hR₃, hR₂, hR₁,
        Function.update_self, Function.update_of_ne, hsg, List.append_nil]
    simp (disch := assumption) only [crtRotSetupRegs, hR₇, hR₆, hR₅, hR₄, hR₃, hR₂, hR₁,
      Function.update_self, Function.update_of_ne]
  · have e₁ : (R₁ preU).length = (R preU).length := by
      simp (disch := assumption) only [hR₁, Function.update_of_ne]
    have e₂ : (R₂ zr).length = (R zr).length := by
      simp (disch := assumption) only [hR₂, hR₁, Function.update_of_ne]
    have e₃ : (R₃ postU).length = (R postU).length := by
      simp (disch := assumption) only [hR₃, hR₂, hR₁, Function.update_of_ne]
    have e₃' : (R₃ rbU).length = (R zr).length := by
      simp (disch := assumption) only [hR₃, hR₂, hR₁, Function.update_of_ne,
        Function.update_self, hrb, List.append_nil, List.length_replicate]
    have e₅ : (R₅ aI).length = (R aI).length := by
      simp (disch := assumption) only [hR₅, hR₄, hR₃, hR₂, hR₁, Function.update_of_ne]
    have e₅' : (R₅ tsU).length = 1 := by
      simp (disch := assumption) only [hR₅, hR₄, hR₃, hR₂, hR₁, Function.update_of_ne,
        Function.update_self, hts, List.length_singleton]
    have e₆ : (R₆ sI).length = (R sI).length := by
      simp (disch := assumption) only [hR₆, hR₅, hR₄, hR₃, hR₂, hR₁, Function.update_of_ne]
    have e₇ : (R₇ sI).length = (R sI).length := by
      simp (disch := assumption) only [hR₇, hR₆, hR₅, hR₄, hR₃, hR₂, hR₁, Function.update_of_ne]
    rw [e₁, e₂, e₃, e₃', e₅, e₅', e₆, e₇]
    nlinarith

/-! ### One valid fiber with its offset update -/

theorem crtRotV_runs {cA cB ts rb tc tr str acc tA tB mu lo hi ov u : Fin T}
    (hreg : [ts, rb, tc, tr, str, acc, tA, tB, mu, lo, hi, ov, u].Nodup)
    (hAB : (cA = hi ∧ cB = lo) ∨ (cA = lo ∧ cB = hi))
    (R : Regs T A) (S x : ℕ) (hx : x ≤ S) (hμ : (R mu).length ≤ S)
    (hlo : R lo = List.replicate x tick) (hhi : R hi = List.replicate (S - x) tick)
    (htc : R tc = []) (htr : R tr = []) (htA : R tA = []) (htB : R tB = []) (hov : R ov = [])
    (hu : R u = [])
    (sl : List (List (Fin (A + 4)))) (hsl : ∀ y ∈ sl, y.length = (R rb).length)
    (hlen : sl.length = S + (R ts).length) (rest : List (Fin (A + 4)))
    (hstr : R str = sl.flatten ++ rest) :
    crtRuns body (.seq (crtRotFib cA cB ts rb tc tr str acc tA tB) (crtOffP mu tc lo hi ov u)) R
      (Function.update (Function.update (Function.update (Function.update R str rest) acc
        ((((sl.take S).rotate (R cA).length ++ sl.drop S).flatten).reverse ++ R acc))
        lo (List.replicate (crtLoStep S (R mu).length x) tick))
        hi (List.replicate (S - crtLoStep S (R mu).length x) tick))
      (sl.length * (8 * (R rb).length + 9) + 14 * (R mu).length + 2 * S + 40) := by
  have hreg' := hreg
  regs_ne hreg'
  crt_ne_symm
  have hAB' : ((R cA).length + (R cB).length = S) ∧ cA ≠ cB ∧ cA ≠ ts ∧ cA ≠ rb ∧ cA ≠ tc ∧
      cA ≠ tr ∧ cA ≠ str ∧ cA ≠ acc ∧ cA ≠ tA ∧ cA ≠ tB ∧ cB ≠ ts ∧ cB ≠ rb ∧ cB ≠ tc ∧
      cB ≠ tr ∧ cB ≠ str ∧ cB ≠ acc ∧ cB ≠ tA ∧ cB ≠ tB := by
    rcases hAB with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · refine ⟨by rw [hhi, hlo]; simp; omega, ?_⟩
      exact ⟨by assumption, by assumption, by assumption, by assumption, by assumption,
        by assumption, by assumption, by assumption, by assumption, by assumption,
        by assumption, by assumption, by assumption, by assumption, by assumption,
        by assumption, by assumption⟩
    · refine ⟨by rw [hhi, hlo]; simp; omega, ?_⟩
      exact ⟨by assumption, by assumption, by assumption, by assumption, by assumption,
        by assumption, by assumption, by assumption, by assumption, by assumption,
        by assumption, by assumption, by assumption, by assumption, by assumption,
        by assumption, by assumption⟩
  obtain ⟨hsum, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17⟩ := hAB'
  have s₁ := crtRotFib_runs (body := body) (cA := cA) (cB := cB) (ts := ts) (rb := rb) (tc := tc)
    (tr := tr) (str := str) (acc := acc) (tA := tA) (tB := tB) (by regs_nodup) R htc htr htA htB
    sl hsl (by omega) rest hstr
  rw [hsum] at s₁
  set R₁ := Function.update (Function.update R str rest) acc
    ((((sl.take S).rotate (R cA).length ++ sl.drop S).flatten).reverse ++ R acc) with hR₁
  have s₂ := crtOffP_runs (body := body) (mu := mu) (tc := tc) (lo := lo) (hi := hi) (ov := ov)
    (t := u) (by regs_nodup) R₁ S x hx
    (by simp (disch := assumption) only [hR₁, Function.update_of_ne]; exact hμ)
    (by simp (disch := assumption) only [hR₁, Function.update_of_ne]; exact hlo)
    (by simp (disch := assumption) only [hR₁, Function.update_of_ne]; exact hhi)
    (by simp (disch := assumption) only [hR₁, Function.update_of_ne]; exact hov)
    (by simp (disch := assumption) only [hR₁, Function.update_of_ne]; exact htc)
    (by simp (disch := assumption) only [hR₁, Function.update_of_ne]; exact hu)
  have hmu : (R₁ mu).length = (R mu).length := by
    simp (disch := assumption) only [hR₁, Function.update_of_ne]
  rw [hmu] at s₂
  exact crtRuns_mono (crtRuns_seq s₁ s₂) (by omega)

/-! ### The rotation pass -/

/-- The rotation pass for one target axis: setup, the address loop over the control indices
(a valid fiber is rotated by `|hi|` slots forward or `|lo|` slots inverse, then the offset
advances by `|muI|`; an invalid fiber is copied), and cleanup. -/
def crtRotP (fwd : Bool) (L : CrtAL T)
    (str acc tA tB tc tr sig msk preU postU aI sI muI zr rbU tsU lo hi ov u₁ u₂ : Fin T) :
    Pr P T Q A U :=
  .seq (crtRotSetup sig msk preU postU aI sI zr rbU tsU hi u₁ u₂ L.sg L.mq) <|
  .seq (crtALFull L
      (.seq (crtRotFib (if fwd then hi else lo) (if fwd then lo else hi) tsU rbU tc tr str acc tA tB)
        (crtOffP muI tc lo hi ov u₁))
      (crtCopyFib lo hi tsU rbU tc tr str acc)) <|
  .seq (crtMv acc str) <| .seq (uclear L.sg) <| .seq (uclear L.mq) <| .seq (uclear rbU) <|
  .seq (uclear tsU) <| .seq (uclear lo) (uclear hi)

lemma crt_rot_cost_arith (N A2 RB B pre post a μ S lo P2 : ℕ) (hRB : RB = P2 * B) (hS : S ≤ A2)
    (hlo : lo ≤ S) :
    12 * pre + 8 * B + 4 * (P2 * B) + 9 * post + 4 * A2 + 9 * a + 8 * S + 40 +
      (N * (A2 * (8 * RB + 9) + 14 * μ + 2 * S + 40 + 10 * pre + 21) + 25 * pre + 21 +
        (2 * (N * A2 * RB) + 2 + (2 * pre + 2 + (2 * pre + 2 + (2 * RB + 2 + (2 * (A2 - S) + 2 +
          (2 * lo + 2 + (2 * (S - lo) + 2)))))))) ≤
    N * (A2 * (8 * RB + 9) + 14 * μ + 2 * S + 10 * pre + 61) + 2 * (N * A2 * RB) + 41 * pre +
      8 * B + 6 * RB + 9 * post + 6 * A2 + 9 * a + 12 * S + 80 := by
  have h1 : N * (A2 * (8 * RB + 9) + 14 * μ + 2 * S + 40 + 10 * pre + 21) =
      N * (A2 * (8 * RB + 9) + 14 * μ + 2 * S + 10 * pre + 61) := by ring
  rw [h1, ← hRB]
  omega

section RotPass

variable {d : ℕ} (a s : Fin d → ℕ)

/-- The output of fiber `F` of the rotation pass. -/
def crtRotOut {α : Type*} (fwd : Bool) (i : ℕ) (hi : i < d) (post : List (Fin d)) (μ : ℕ)
    (C : (Fin d → ℕ) → List α) (F : ℕ) : List α :=
  if crtVal a s i F then
    (((crtSlotsOf a i hi post C F).take (s ⟨i, hi⟩)).rotate
      (crtShift fwd (s ⟨i, hi⟩) μ (crtCnt a s i F)) ++
      (crtSlotsOf a i hi post C F).drop (s ⟨i, hi⟩)).flatten
  else (crtSlotsOf a i hi post C F).flatten

theorem crtRotOut_top {α : Type*} (fwd : Bool) {i : ℕ} (hi : i < d) {post : List (Fin d)}
    (hnd : (crtRevAx i ++ (⟨i, hi⟩ : Fin d) :: post).Nodup) (hs : ∀ j, s j ≤ 2 ^ a j) (μ : ℕ)
    (C : (Fin d → ℕ) → List α) :
    (List.range (2 ^ crtPre a i)).flatMap (crtRotOut a s fwd i hi post μ C) =
      (crtBox a (crtRevAx i ++ (⟨i, hi⟩ : Fin d) :: post) (crtRotC s i hi μ fwd C) 0).flatten := by
  rw [crtBox_fibers]
  refine List.flatMap_congr fun F hF => ?_
  have hF' := List.mem_range.1 hF
  rw [crtRot_fiber a s hi hnd (hs _) μ fwd C hF', crtRotOut]
  by_cases hv : crtVal a s i F = true
  · rw [ite_eq_left hv, ite_eq_left hv, (crtCnt_main a s hs i hi.le).2 F hF' hv]
  · rw [ite_eq_right hv, ite_eq_right hv]

lemma crt_drop_range_cons {N F : ℕ} (h : F < N) :
    (List.range N).drop F = F :: (List.range N).drop (F + 1) := by
  rw [List.drop_eq_getElem_cons (by simpa using h), List.getElem_range]

lemma crtSlotsOf_length {α : Type*} (i : ℕ) (hi : i < d) (post : List (Fin d))
    (C : (Fin d → ℕ) → List α) (F : ℕ) : (crtSlotsOf a i hi post C F).length = 2 ^ a ⟨i, hi⟩ := by
  simp [crtSlotsOf]

lemma crtSlotsOf_uniform {α : Type*} (i : ℕ) (hi : i < d) (post : List (Fin d))
    (C : (Fin d → ℕ) → List α) (B : ℕ) (hC : ∀ y, (C y).length = B) (F : ℕ) :
    ∀ x ∈ crtSlotsOf a i hi post C F, x.length = 2 ^ crtW a post * B := by
  intro x hx
  simp only [crtSlotsOf, List.mem_map] at hx
  obtain ⟨z, _, rfl⟩ := hx
  exact crtBox_flatten_length a post C _ B hC

variable {T Q A : ℕ} {U P : Type} {body : P → Pr P T Q A U}

set_option maxHeartbeats 4000000 in
theorem crtRotP_runs (fwd : Bool) (L : CrtAL T) (hL : L.Ok)
    {str acc tA tB tc tr sig msk preU postU aI sI muI zr rbU tsU lo hi ov u₁ u₂ : Fin T}
    (hreg : [str, acc, tA, tB, tc, tr, sig, msk, preU, postU, aI, sI, muI, zr, rbU, tsU, lo, hi,
      ov, u₁, u₂].Nodup)
    (hp : ∀ k ∈ [str, acc, tA, tB, tc, tr, sig, msk, preU, postU, aI, sI, muI, zr, rbU, tsU, lo,
      hi, ov, u₁, u₂], ¬ L.Prot k)
    (hs : ∀ j, 0 < s j ∧ s j < 2 ^ a j) {i : ℕ} (hid : i < d) (post : List (Fin d))
    (hnd : (crtRevAx i ++ (⟨i, hid⟩ : Fin d) :: post).Nodup) (μ : ℕ) (hμ : μ ≤ s ⟨i, hid⟩)
    (C : (Fin d → ℕ) → List (Fin (A + 4))) (B : ℕ) (hC : ∀ y, (C y).length = B)
    (R : Regs T A)
    (hstr : R str = (crtBox a (crtRevAx i ++ (⟨i, hid⟩ : Fin d) :: post) C 0).flatten)
    (hsig : R sig = binSyms (crtPre a d) (crtSig a s d))
    (hmsk : R msk = binSyms (crtPre a d) (crtMask a d))
    (hpre : (R preU).length = crtPre a i) (hpost : (R postU).length = crtW a post)
    (haI : (R aI).length = a ⟨i, hid⟩) (hsI : (R sI).length = s ⟨i, hid⟩)
    (hmu : (R muI).length = μ) (hzr : (R zr).length = B)
    (h0 : ∀ k ∈ [acc, tA, tB, tc, tr, rbU, tsU, lo, hi, ov, u₁, u₂, L.nF, L.tN, L.fc, L.sg, L.mq,
      L.c0, L.c1, L.c2, L.it], R k = []) :
    crtRuns body (crtRotP fwd L str acc tA tB tc tr sig msk preU postU aI sI muI zr rbU tsU lo hi
        ov u₁ u₂) R
      (Function.update R str
        (crtBox a (crtRevAx i ++ (⟨i, hid⟩ : Fin d) :: post) (crtRotC s i hid μ fwd C) 0).flatten)
      (2 ^ crtPre a i * (2 ^ a ⟨i, hid⟩ * (8 * (2 ^ crtW a post * B) + 9) + 14 * μ +
          2 * s ⟨i, hid⟩ + 10 * crtPre a i + 61) +
        2 * (2 ^ crtPre a i * 2 ^ a ⟨i, hid⟩ * (2 ^ crtW a post * B)) + 41 * crtPre a i +
        8 * B + 6 * (2 ^ crtW a post * B) + 9 * crtW a post + 6 * 2 ^ a ⟨i, hid⟩ +
        9 * a ⟨i, hid⟩ + 12 * s ⟨i, hid⟩ + 80) := by
  have hreg' := hreg
  regs_ne hreg'
  have hL' := hL
  unfold CrtAL.Ok at hL'
  regs_ne hL'
  -- every pass register differs from every loop register
  have np : ∀ k ∈ [str, acc, tA, tB, tc, tr, sig, msk, preU, postU, aI, sI, muI, zr, rbU, tsU,
      lo, hi, ov, u₁, u₂], k ≠ L.nF ∧ k ≠ L.tN ∧ k ≠ L.fc ∧ k ≠ L.sg ∧ k ≠ L.mq ∧ k ≠ L.c0 ∧
      k ≠ L.c1 ∧ k ≠ L.c2 ∧ k ≠ L.it := fun k hk => CrtAL.ne_of_not_prot (hp k hk)
  obtain ⟨-, -, -, sig_sg, sig_mq, -⟩ := np sig (by simp)
  obtain ⟨-, -, -, msk_sg, msk_mq, -⟩ := np msk (by simp)
  obtain ⟨-, -, -, pre_sg, pre_mq, -⟩ := np preU (by simp)
  obtain ⟨-, -, -, post_sg, post_mq, -⟩ := np postU (by simp)
  obtain ⟨-, -, -, aI_sg, aI_mq, -⟩ := np aI (by simp)
  obtain ⟨-, -, -, sI_sg, sI_mq, -⟩ := np sI (by simp)
  obtain ⟨-, -, -, zr_sg, zr_mq, -⟩ := np zr (by simp)
  obtain ⟨rb_nF, rb_tN, rb_fc, rb_sg, rb_mq, rb_c0, rb_c1, rb_c2, rb_it⟩ := np rbU (by simp)
  obtain ⟨ts_nF, ts_tN, ts_fc, ts_sg, ts_mq, ts_c0, ts_c1, ts_c2, ts_it⟩ := np tsU (by simp)
  obtain ⟨hi_nF, hi_tN, hi_fc, hi_sg, hi_mq, hi_c0, hi_c1, hi_c2, hi_it⟩ := np hi (by simp)
  obtain ⟨-, -, -, u₁_sg, u₁_mq, -⟩ := np u₁ (by simp)
  obtain ⟨-, -, -, u₂_sg, u₂_mq, -⟩ := np u₂ (by simp)
  obtain ⟨-, -, -, str_sg, str_mq, -⟩ := np str (by simp)
  obtain ⟨-, -, -, acc_sg, acc_mq, -⟩ := np acc (by simp)
  obtain ⟨-, -, -, tA_sg, tA_mq, -⟩ := np tA (by simp)
  obtain ⟨-, -, -, tB_sg, tB_mq, -⟩ := np tB (by simp)
  obtain ⟨-, -, -, tc_sg, tc_mq, -⟩ := np tc (by simp)
  obtain ⟨-, -, -, tr_sg, tr_mq, -⟩ := np tr (by simp)
  obtain ⟨-, -, -, mu_sg, mu_mq, -⟩ := np muI (by simp)
  obtain ⟨lo_nF, lo_tN, lo_fc, lo_sg, lo_mq, lo_c0, lo_c1, lo_c2, lo_it⟩ := np lo (by simp)
  obtain ⟨-, -, -, ov_sg, ov_mq, -⟩ := np ov (by simp)
  crt_ne_symm
  have hsle : ∀ j, s j ≤ 2 ^ a j := fun j => (hs j).2.le
  have ha : ∀ j, 1 ≤ a j := fun j => by
    by_contra hz
    have h0' : a j = 0 := by omega
    have := hs j; rw [h0'] at this; omega
  set I : Fin d := ⟨i, hid⟩ with hI
  set S := s I with hS
  set N := 2 ^ crtPre a i with hN
  set RB := 2 ^ crtW a post * B with hRB
  have hSt : S ≤ 2 ^ a I := hsle I
  have hz : ∀ k ∈ [acc, tA, tB, tc, tr, rbU, tsU, lo, hi, ov, u₁, u₂, L.nF, L.tN, L.fc, L.sg,
      L.mq, L.c0, L.c1, L.c2, L.it], R k = [] := h0
  -- setup
  have s₁ := crtRotSetup_runs (body := body) (sig := sig) (msk := msk) (preU := preU)
    (postU := postU) (aI := aI) (sI := sI) (zr := zr) (rbU := rbU) (tsU := tsU) (hi := hi)
    (u₁ := u₁) (u₂ := u₂) (sg := L.sg) (mq := L.mq) (by regs_nodup) R
    (hz _ (by simp)) (hz _ (by simp)) (hz _ (by simp)) (hz _ (by simp)) (hz _ (by simp))
    (hz _ (by simp)) (hz _ (by simp))
    (by rw [hpre, hsig, length_binSyms]; exact crtPre_mono a hid.le)
    (by rw [hpre, hmsk, length_binSyms]; exact crtPre_mono a hid.le)
  set R₁ := crtRotSetupRegs R sig msk preU postU aI sI zr rbU tsU hi L.sg L.mq with hR₁
  have hR₁sg : R₁ L.sg = binSyms (crtPre a i) (crtSig a s i) := by
    simp (disch := assumption) only [hR₁, crtRotSetupRegs, Function.update_of_ne,
      Function.update_self]
    rw [hsig, hpre, crt_binSyms_take_sig a s (fun j => (hs j).2) hid.le]
  have hR₁mq : R₁ L.mq = binSyms (crtPre a i) (crtMask a i) := by
    simp (disch := assumption) only [hR₁, crtRotSetupRegs, Function.update_of_ne,
      Function.update_self]
    rw [hmsk, hpre, crt_binSyms_take_mask a ha hid.le]
  have hR₁rb : R₁ rbU = List.replicate RB tick := by
    simp (disch := assumption) only [hR₁, crtRotSetupRegs, Function.update_of_ne,
      Function.update_self]
    rw [hpost, hzr]
  have hR₁ts : R₁ tsU = List.replicate (2 ^ a I - S) tick := by
    simp (disch := assumption) only [hR₁, crtRotSetupRegs, Function.update_of_ne,
      Function.update_self]
    rw [haI, hsI]
  have hR₁hi : R₁ hi = List.replicate S tick := by
    simp (disch := assumption) only [hR₁, crtRotSetupRegs, Function.update_self]
    rw [hsI]
  have hR₁oth : ∀ k, k ≠ L.sg → k ≠ L.mq → k ≠ rbU → k ≠ tsU → k ≠ hi → R₁ k = R k := by
    intro k k1 k2 k3 k4 k5
    simp (disch := assumption) only [hR₁, crtRotSetupRegs, Function.update_of_ne]
  -- the loop invariant
  set slots := crtSlotsOf a i hid post C with hslots
  set outF := crtRotOut a s fwd i hid post μ C with houtF
  let strF : ℕ → List (Fin (A + 4)) := fun F =>
    ((List.range N).drop F).flatMap fun F' => (slots F').flatten
  let accF : ℕ → List (Fin (A + 4)) := fun F => ((List.range F).flatMap outF).reverse
  let loF : ℕ → ℕ := fun F => crtLo S μ (crtCnt a s i F)
  let Ψ : ℕ → Regs T A := fun F => Function.update (Function.update (Function.update
    (Function.update R₁ str (strF F)) acc (accF F)) lo (List.replicate (loF F) tick)) hi
    (List.replicate (S - loF F) tick)
  have hΨstr : ∀ F, Ψ F str = strF F := fun F => by
    simp (disch := assumption) only [Ψ, Function.update_of_ne, Function.update_self]
  have hΨacc : ∀ F, Ψ F acc = accF F := fun F => by
    simp (disch := assumption) only [Ψ, Function.update_of_ne, Function.update_self]
  have hΨlo : ∀ F, Ψ F lo = List.replicate (loF F) tick := fun F => by
    simp (disch := assumption) only [Ψ, Function.update_of_ne, Function.update_self]
  have hΨhi : ∀ F, Ψ F hi = List.replicate (S - loF F) tick := fun F => by
    simp (disch := assumption) only [Ψ, Function.update_self]
  have hΨoth : ∀ F k, k ≠ str → k ≠ acc → k ≠ lo → k ≠ hi → Ψ F k = R₁ k := fun F k k1 k2 k3 k4 => by
    simp (disch := assumption) only [Ψ, Function.update_of_ne]
  have hstrF : ∀ F < N, strF F = (slots F).flatten ++ strF (F + 1) := fun F hF => by
    simp only [strF]
    rw [crt_drop_range_cons hF, List.flatMap_cons]
  have hloF_le : ∀ F, loF F ≤ S := fun F => crtLo_le hμ _
  have hsl : ∀ F, ∀ x ∈ slots F, x.length = RB := fun F =>
    crtSlotsOf_uniform a i hid post C B hC F
  have hsllen : ∀ F, (slots F).length = 2 ^ a I := fun F => crtSlotsOf_length a i hid post C F
  -- registers of `R'` agreeing with `Ψ F` off the loop registers
  have hRΨ : ∀ F (R' : Regs T A), (∀ k, ¬ L.Prot k → R' k = Ψ F k) → ∀ k ∈
      [str, acc, tA, tB, tc, tr, sig, msk, preU, postU, aI, sI, muI, zr, rbU, tsU, lo, hi, ov,
        u₁, u₂], R' k = Ψ F k := fun F R' hR' k hk => hR' k (hp k hk)
  have hR₁z : ∀ k ∈ [tA, tB, tc, tr, ov, u₁, u₂], R₁ k = [] := by
    intro k hk
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      (rw [hR₁oth _ (by assumption) (by assumption) (by assumption) (by assumption)
        (by assumption)]; exact hz _ (by simp))
  have hV : ∀ F < N, crtVal a s i F = true → ∀ R' : Regs T A,
      (∀ k, ¬ L.Prot k → R' k = Ψ F k) →
      crtRuns body (.seq (crtRotFib (if fwd then hi else lo) (if fwd then lo else hi) tsU rbU tc tr
          str acc tA tB) (crtOffP muI tc lo hi ov u₁)) R'
        (fun k => if L.Prot k then R' k else Ψ (F + 1) k)
        (2 ^ a I * (8 * RB + 9) + 14 * μ + 2 * S + 40) := by
    intro F hF hv R' hR'
    have e := hRΨ F R' hR'
    have eΨ : ∀ k, k ≠ str → k ≠ acc → k ≠ lo → k ≠ hi → R' k = R₁ k → R' k = R₁ k := fun _ _ _ _ _ h => h
    have rlo : R' lo = List.replicate (loF F) tick := by rw [e lo (by simp), hΨlo]
    have rhi : R' hi = List.replicate (S - loF F) tick := by rw [e hi (by simp), hΨhi]
    have rstr : R' str = (slots F).flatten ++ strF (F + 1) := by
      rw [e str (by simp), hΨstr, hstrF F hF]
    have racc : R' acc = accF F := by rw [e acc (by simp), hΨacc]
    have r0 : ∀ k ∈ [tA, tB, tc, tr, ov, u₁, u₂], R' k = [] := by
      intro k hk
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        (rw [e _ (by simp), hΨoth F _ (by assumption) (by assumption) (by assumption)
          (by assumption)]; exact hR₁z _ (by simp))
    have rmu : (R' muI).length = μ := by
      rw [e muI (by simp), hΨoth F _ (by assumption) (by assumption) (by assumption)
        (by assumption), hR₁oth _ (by assumption) (by assumption) (by assumption) (by assumption)
        (by assumption), hmu]
    have rrb : (R' rbU).length = RB := by
      rw [e rbU (by simp), hΨoth F _ (by assumption) (by assumption) (by assumption)
        (by assumption), hR₁rb, List.length_replicate]
    have rts : (R' tsU).length = 2 ^ a I - S := by
      rw [e tsU (by simp), hΨoth F _ (by assumption) (by assumption) (by assumption)
        (by assumption), hR₁ts, List.length_replicate]
    have h := crtRotV_runs (body := body) (cA := if fwd then hi else lo)
      (cB := if fwd then lo else hi) (ts := tsU) (rb := rbU) (tc := tc) (tr := tr) (str := str)
      (acc := acc) (tA := tA) (tB := tB) (mu := muI) (lo := lo) (hi := hi) (ov := ov) (u := u₁)
      (by regs_nodup) (by cases fwd <;> simp) R' S (loF F) (hloF_le F) (by rw [rmu]; exact hμ)
      rlo rhi (r0 tc (by simp)) (r0 tr (by simp)) (r0 tA (by simp)) (r0 tB (by simp))
      (r0 ov (by simp)) (r0 u₁ (by simp)) (slots F) (by rw [rrb]; exact hsl F)
      (by rw [hsllen, rts]; omega) (strF (F + 1)) rstr
    have hcA : (R' (if fwd then hi else lo)).length = crtShift fwd S μ (crtCnt a s i F) := by
      cases fwd <;> simp [rlo, rhi, crtShift, loF]
    rw [hcA, rmu, rrb, hsllen] at h
    refine crtRuns_mono (crtRuns_congr h ?_) le_rfl
    have hcs : crtCnt a s i (F + 1) = crtCnt a s i F + 1 := by rw [crtCnt_succ_arg, hv]; rfl
    have hlo1 : loF (F + 1) = crtLoStep S μ (loF F) := by
      simp only [loF, hcs, crtLo_succ]
    have hout : outF F = (((slots F).take S).rotate (crtShift fwd S μ (crtCnt a s i F)) ++
        (slots F).drop S).flatten := by
      rw [houtF, crtRotOut, ite_eq_left hv]
    funext k
    by_cases k1 : k = hi
    · rw [k1, Function.update_self, ite_eq_right (hp hi (by simp)), hΨhi, hlo1]
    rw [Function.update_of_ne k1]
    by_cases k2 : k = lo
    · rw [k2, Function.update_self, ite_eq_right (hp lo (by simp)), hΨlo, hlo1]
    rw [Function.update_of_ne k2]
    by_cases k3 : k = acc
    · rw [k3, Function.update_self, ite_eq_right (hp acc (by simp)), hΨacc, racc, ← hout]
      simp only [accF, List.range_succ, List.flatMap_append, List.flatMap_singleton,
        List.reverse_append]
    rw [Function.update_of_ne k3]
    by_cases k4 : k = str
    · rw [k4, Function.update_self, ite_eq_right (hp str (by simp)), hΨstr]
    rw [Function.update_of_ne k4]
    by_cases hk : L.Prot k
    · rw [ite_eq_left hk]
    · rw [ite_eq_right hk, hR' k hk, hΨoth F k k4 k3 k2 k1, hΨoth (F + 1) k k4 k3 k2 k1]
  have hI : ∀ F < N, crtVal a s i F = false → ∀ R' : Regs T A,
      (∀ k, ¬ L.Prot k → R' k = Ψ F k) →
      crtRuns body (crtCopyFib lo hi tsU rbU tc tr str acc) R'
        (fun k => if L.Prot k then R' k else Ψ (F + 1) k)
        (2 ^ a I * (8 * RB + 9) + 14 * μ + 2 * S + 40) := by
    intro F hF hv R' hR'
    have e := hRΨ F R' hR'
    have rlo : R' lo = List.replicate (loF F) tick := by rw [e lo (by simp), hΨlo]
    have rhi : R' hi = List.replicate (S - loF F) tick := by rw [e hi (by simp), hΨhi]
    have rstr : R' str = (slots F).flatten ++ strF (F + 1) := by
      rw [e str (by simp), hΨstr, hstrF F hF]
    have racc : R' acc = accF F := by rw [e acc (by simp), hΨacc]
    have r0 : ∀ k ∈ [tc, tr], R' k = [] := by
      intro k hk
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl <;>
        (rw [e _ (by simp), hΨoth F _ (by assumption) (by assumption) (by assumption)
          (by assumption)]; exact hR₁z _ (by simp))
    have rrb : (R' rbU).length = RB := by
      rw [e rbU (by simp), hΨoth F _ (by assumption) (by assumption) (by assumption)
        (by assumption), hR₁rb, List.length_replicate]
    have rts : (R' tsU).length = 2 ^ a I - S := by
      rw [e tsU (by simp), hΨoth F _ (by assumption) (by assumption) (by assumption)
        (by assumption), hR₁ts, List.length_replicate]
    have h := crtCopyFib_runs (body := body) (cA := lo) (cB := hi) (ts := tsU) (rb := rbU)
      (tc := tc) (tr := tr) (str := str) (acc := acc) (by regs_nodup) R'
      (r0 tc (by simp)) (r0 tr (by simp)) (slots F) (by rw [rrb]; exact hsl F)
      (by rw [hsllen, rts, rlo, rhi, List.length_replicate, List.length_replicate]
          have := hloF_le F; omega) (strF (F + 1)) rstr
    rw [rrb, hsllen] at h
    refine crtRuns_mono (crtRuns_congr h ?_)
      (by have := Nat.mul_le_mul_left (2 ^ a I) (show 4 * RB + 9 ≤ 8 * RB + 9 by omega); omega)
    have hcs : crtCnt a s i (F + 1) = crtCnt a s i F := by rw [crtCnt_succ_arg, hv]; rfl
    have hout : outF F = (slots F).flatten := by
      rw [houtF, crtRotOut, ite_eq_right (by simp [hv])]
    funext k
    by_cases k3 : k = acc
    · rw [k3, Function.update_self, ite_eq_right (hp acc (by simp)), hΨacc, racc, ← hout]
      simp only [accF, List.range_succ, List.flatMap_append, List.flatMap_singleton,
        List.reverse_append]
    rw [Function.update_of_ne k3]
    by_cases k4 : k = str
    · rw [k4, Function.update_self, ite_eq_right (hp str (by simp)), hΨstr]
    rw [Function.update_of_ne k4]
    by_cases hk : L.Prot k
    · rw [ite_eq_left hk]
    rw [ite_eq_right hk, hR' k hk]
    by_cases k1 : k = hi
    · rw [k1, hΨhi, hΨhi]; simp only [loF, hcs]
    by_cases k2 : k = lo
    · rw [k2, hΨlo, hΨlo]; simp only [loF, hcs]
    rw [hΨoth F k k4 k3 k2 k1, hΨoth (F + 1) k k4 k3 k2 k1]
  -- the input as fibers
  have hin : R str = strF 0 := by
    rw [hstr, crtBox_fibers]
    simp only [strF, List.drop_zero]
    exact List.flatMap_congr fun F _ => (crtSlotsOf_flatten a i hid post C F).symm
  have h₂ := crtALFull_runs a s L hL hid.le hs hV hI R₁
    (fun k hk => by
      by_cases k1 : k = str
      · rw [k1, hΨstr, hR₁oth _ (by assumption) (by assumption) (by assumption) (by assumption)
          (by assumption), hin]
      by_cases k2 : k = acc
      · rw [k2, hΨacc, hR₁oth _ (by assumption) (by assumption) (by assumption) (by assumption)
          (by assumption), hz acc (by simp)]
        simp [accF]
      by_cases k3 : k = lo
      · rw [k3, hΨlo, hR₁oth _ (by assumption) (by assumption) (by assumption) (by assumption)
          (by assumption), hz lo (by simp)]
        simp [loF, crtCnt, crtLo]
      by_cases k4 : k = hi
      · rw [k4, hΨhi, hR₁hi]
        simp [loF, crtCnt, crtLo]
      rw [hΨoth 0 k k1 k2 k3 k4])
    (by rw [hR₁oth _ (by assumption) (by assumption) (by assumption) (by assumption)
          (by assumption)]; exact hz _ (by simp))
    (by rw [hR₁oth _ (by assumption) (by assumption) (by assumption) (by assumption)
          (by assumption)]; exact hz _ (by simp))
    (by rw [hR₁oth _ (by assumption) (by assumption) (by assumption) (by assumption)
          (by assumption)]; exact hz _ (by simp))
    hR₁sg hR₁mq
    (by rw [hR₁oth _ (by assumption) (by assumption) (by assumption) (by assumption)
          (by assumption)]; exact hz _ (by simp))
    (by rw [hR₁oth _ (by assumption) (by assumption) (by assumption) (by assumption)
          (by assumption)]; exact hz _ (by simp))
    (by rw [hR₁oth _ (by assumption) (by assumption) (by assumption) (by assumption)
          (by assumption)]; exact hz _ (by simp))
    (by rw [hR₁oth _ (by assumption) (by assumption) (by assumption) (by assumption)
          (by assumption)]; exact hz _ (by simp))
  -- cleanup
  set R₂ : Regs T A := fun k => if L.Prot k then R₁ k else Ψ N k with hR₂
  have hR₂acc : R₂ acc = accF N := by rw [hR₂]; simp only [ite_eq_right (hp acc (by simp)), hΨacc]
  have hR₂str : R₂ str = [] := by
    rw [hR₂]
    simp only [ite_eq_right (hp str (by simp)), hΨstr, strF]
    rw [List.drop_eq_nil_of_le (by simp)]; rfl
  have hbox : (accF N).reverse = (crtBox a (crtRevAx i ++ I :: post) (crtRotC s i hid μ fwd C)
      0).flatten := by
    simp only [accF, List.reverse_reverse, houtF]
    exact crtRotOut_top a s fwd hid hnd hsle μ C
  have c₁ := crtMv_runs (body := body) (i := acc) (j := str) (by assumption) R₂
  have c₂ := crtClear_runs (body := body) L.sg
    (Function.update (Function.update R₂ acc []) str ((R₂ acc).reverse ++ R₂ str))
  have c₃ := crtClear_runs (body := body) L.mq (Function.update
    (Function.update (Function.update R₂ acc []) str ((R₂ acc).reverse ++ R₂ str)) L.sg [])
  have c₄ := crtClear_runs (body := body) rbU (Function.update (Function.update
    (Function.update (Function.update R₂ acc []) str ((R₂ acc).reverse ++ R₂ str)) L.sg [])
    L.mq [])
  have c₅ := crtClear_runs (body := body) tsU (Function.update (Function.update (Function.update
    (Function.update (Function.update R₂ acc []) str ((R₂ acc).reverse ++ R₂ str)) L.sg [])
    L.mq []) rbU [])
  have c₆ := crtClear_runs (body := body) lo (Function.update (Function.update (Function.update
    (Function.update (Function.update (Function.update R₂ acc []) str
      ((R₂ acc).reverse ++ R₂ str)) L.sg []) L.mq []) rbU []) tsU [])
  have c₇ := crtClear_runs (body := body) hi (Function.update (Function.update (Function.update
    (Function.update (Function.update (Function.update (Function.update R₂ acc []) str
      ((R₂ acc).reverse ++ R₂ str)) L.sg []) L.mq []) rbU []) tsU []) lo [])
  refine crtRuns_mono (crtRuns_congr (crtRuns_seq s₁ (crtRuns_seq h₂ (crtRuns_seq c₁
    (crtRuns_seq c₂ (crtRuns_seq c₃ (crtRuns_seq c₄ (crtRuns_seq c₅ (crtRuns_seq c₆ c₇))))))))
    ?_) ?_
  · funext k
    by_cases k1 : k = str
    · rw [k1, Function.update_of_ne ‹str ≠ hi›, Function.update_of_ne ‹str ≠ lo›,
        Function.update_of_ne ‹str ≠ tsU›, Function.update_of_ne ‹str ≠ rbU›,
        Function.update_of_ne ‹str ≠ L.mq›, Function.update_of_ne ‹str ≠ L.sg›,
        Function.update_self, Function.update_self, hR₂acc, hR₂str, List.append_nil, hbox]
    rw [Function.update_of_ne k1]
    by_cases k2 : k = acc
    · rw [k2, Function.update_of_ne ‹acc ≠ hi›, Function.update_of_ne ‹acc ≠ lo›,
        Function.update_of_ne ‹acc ≠ tsU›, Function.update_of_ne ‹acc ≠ rbU›,
        Function.update_of_ne ‹acc ≠ L.mq›, Function.update_of_ne ‹acc ≠ L.sg›,
        Function.update_of_ne ‹acc ≠ str›, Function.update_self]
      exact (hz acc (by simp)).symm
    by_cases k3 : k = L.sg
    · rw [k3, Function.update_of_ne ‹L.sg ≠ hi›, Function.update_of_ne ‹L.sg ≠ lo›,
        Function.update_of_ne ‹L.sg ≠ tsU›, Function.update_of_ne ‹L.sg ≠ rbU›,
        Function.update_of_ne ‹L.sg ≠ L.mq›, Function.update_self]
      exact (hz _ (by simp)).symm
    by_cases k4 : k = L.mq
    · rw [k4, Function.update_of_ne ‹L.mq ≠ hi›, Function.update_of_ne ‹L.mq ≠ lo›,
        Function.update_of_ne ‹L.mq ≠ tsU›, Function.update_of_ne ‹L.mq ≠ rbU›,
        Function.update_self]
      exact (hz _ (by simp)).symm
    by_cases k5 : k = rbU
    · rw [k5, Function.update_of_ne ‹rbU ≠ hi›, Function.update_of_ne ‹rbU ≠ lo›,
        Function.update_of_ne ‹rbU ≠ tsU›, Function.update_self]
      exact (hz _ (by simp)).symm
    by_cases k6 : k = tsU
    · rw [k6, Function.update_of_ne ‹tsU ≠ hi›, Function.update_of_ne ‹tsU ≠ lo›,
        Function.update_self]
      exact (hz _ (by simp)).symm
    by_cases k7 : k = lo
    · rw [k7, Function.update_of_ne ‹lo ≠ hi›, Function.update_self]
      exact (hz _ (by simp)).symm
    by_cases k8 : k = hi
    · rw [k8, Function.update_self]
      exact (hz _ (by simp)).symm
    rw [Function.update_of_ne k8, Function.update_of_ne k7, Function.update_of_ne k6,
      Function.update_of_ne k5, Function.update_of_ne k4, Function.update_of_ne k3,
      Function.update_of_ne k1, Function.update_of_ne k2, hR₂]
    beta_reduce
    by_cases hk : L.Prot k
    · rw [ite_eq_left hk, hR₁oth k k3 k4 k5 k6 k8]
    · rw [ite_eq_right hk, hΨoth _ k k1 k2 k7 k8, hR₁oth k k3 k4 k5 k6 k8]
  · have hC' : ∀ y, (crtRotC s i hid μ fwd C y).length = B := fun y => by
      unfold crtRotC; split_ifs <;> exact hC _
    have l₁ : (R₂ acc).length = N * 2 ^ a I * RB := by
      rw [hR₂acc, ← List.length_reverse, hbox, crtBox_flatten_length a _ _ _ B hC', crtW_append,
        crtW_revAx a i hid.le, crtW_cons, pow_add, pow_add, hN, hRB]
      ring
    have l₂ : (R₂ L.sg).length = crtPre a i := by
      rw [hR₂]; beta_reduce
      rw [ite_eq_left (show L.Prot L.sg from Or.inr (Or.inr (Or.inr (Or.inl rfl)))), hR₁sg,
        length_binSyms]
    have l₃ : (R₂ L.mq).length = crtPre a i := by
      rw [hR₂]; beta_reduce
      rw [ite_eq_left (show L.Prot L.mq from Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))), hR₁mq,
        length_binSyms]
    have l₄ : (R₂ rbU).length = RB := by
      rw [hR₂]; beta_reduce
      rw [ite_eq_right (hp rbU (by simp)), hΨoth _ _ ‹rbU ≠ str› ‹rbU ≠ acc› ‹rbU ≠ lo› ‹rbU ≠ hi›,
        hR₁rb, List.length_replicate]
    have l₅ : (R₂ tsU).length = 2 ^ a I - S := by
      rw [hR₂]; beta_reduce
      rw [ite_eq_right (hp tsU (by simp)), hΨoth _ _ ‹tsU ≠ str› ‹tsU ≠ acc› ‹tsU ≠ lo› ‹tsU ≠ hi›,
        hR₁ts, List.length_replicate]
    have l₆ : (R₂ lo).length = loF N := by
      rw [hR₂]; beta_reduce
      rw [ite_eq_right (hp lo (by simp)), hΨlo, List.length_replicate]
    have l₇ : (R₂ hi).length = S - loF N := by
      rw [hR₂]; beta_reduce
      rw [ite_eq_right (hp hi (by simp)), hΨhi, List.length_replicate]
    simp only [Function.update_of_ne ‹L.sg ≠ str›, Function.update_of_ne ‹L.sg ≠ acc›,
      Function.update_of_ne ‹L.mq ≠ str›, Function.update_of_ne ‹L.mq ≠ acc›,
      Function.update_of_ne ‹L.mq ≠ L.sg›,
      Function.update_of_ne ‹rbU ≠ str›, Function.update_of_ne ‹rbU ≠ acc›,
      Function.update_of_ne ‹rbU ≠ L.sg›, Function.update_of_ne ‹rbU ≠ L.mq›,
      Function.update_of_ne ‹tsU ≠ str›, Function.update_of_ne ‹tsU ≠ acc›,
      Function.update_of_ne ‹tsU ≠ L.sg›, Function.update_of_ne ‹tsU ≠ L.mq›,
      Function.update_of_ne ‹tsU ≠ rbU›,
      Function.update_of_ne ‹lo ≠ str›, Function.update_of_ne ‹lo ≠ acc›,
      Function.update_of_ne ‹lo ≠ L.sg›, Function.update_of_ne ‹lo ≠ L.mq›,
      Function.update_of_ne ‹lo ≠ rbU›, Function.update_of_ne ‹lo ≠ tsU›,
      Function.update_of_ne ‹hi ≠ str›, Function.update_of_ne ‹hi ≠ acc›,
      Function.update_of_ne ‹hi ≠ L.sg›, Function.update_of_ne ‹hi ≠ L.mq›,
      Function.update_of_ne ‹hi ≠ rbU›, Function.update_of_ne ‹hi ≠ tsU›,
      Function.update_of_ne ‹hi ≠ lo›, l₁, l₂, l₃, l₄, l₅, l₆, l₇, hpre, hzr, hpost, haI, hsI]
    exact crt_rot_cost_arith N (2 ^ a I) RB B (crtPre a i) (crtW a post) (a I) μ S (loF N)
      (2 ^ crtW a post) hRB hSt (hloF_le N)

end RotPass

end IntegerMultBounds.MathlibTM2.Fast
