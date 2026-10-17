module

public import IntegerMultBounds.MathlibTM2.Node.Params
public import IntegerMultBounds.MathlibTM2.Layer.Shift
public import IntegerMultBounds.MathlibTM2.Layer.TopZ
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Data.Sym.Sym2.Init

/-!
# Word passes of the simultaneous layer: widening and the truncating shift

Counter-driven host programs used by the host machine of the simultaneous layer
(`Node/TopProc.lean`): the word lengths and shift amounts are the lengths of counter registers,
so the program text does not depend on them. Every `_exec` theorem gives the final register file
exactly, `v'.user = v.user` and an exact step count.

**Word passes.** `topPass src dst wp` runs the word program `wp` while `src` is nonempty and moves
`dst` back onto `src`. `TopWordSpec … G L F c` is the per-word contract: from registers satisfying
`G` (`TopWordFrame`: `G` reads neither `src` nor `dst`), a word `x` of `L` symbols on top of
`src` is consumed and `(F x).reverse` pushed onto `dst`. `topPass_exec`: `src` holding the words
`ws` ends holding `(ws.map F).flatten`.

**Counted steps.** `topCopyC_exec`: `Shift.counted c t (Shift.copyStep c t src dst)` moves `|c|`
symbols from `src` onto `dst`. `topDupF d` pushes the top of `d` again; under `scanR c t` it
runs `|c|` times (`foldl_topDup`).

**Widening** (`topWidenWord`, `topWidenP_exec`). Each word of `|c₁| = w` symbols is copied and
its last pair (the two sign bits) repeated `|c₂| = w' - w` times (`topWidenF`); for coefficients
fitting `w` signed bits (`TopFitsZ w`) this is the `w'`-bit word (`topWidenF_coeffSyms`, by
`topWiden_bit`), so `encZ A w Z` becomes `encZ A w' Z`.

**The truncating shift** (`topShiftWord`, `topShiftP_exec`). Truncation toward zero is
`tdiv x 2^s = ⌊(x + σ (2^s - 1)) / 2^s⌋` with `σ` the sign (`topTrunc_int`). Each word of
`|cW| = w'` symbols is copied onto `tmp` and back, its last pair (the signs) going onto the
register `sg` and a zero carry pair onto `cy` (`topSignAct`); then `|cS| = s` absorbing steps add
the sign bits to the low bits and keep only the carries (`topAbsF`, model `topAbsorb`),
`|cE| = w` emitting steps output the next bits plus the carry (`topEmitF`, model `topEmit`), and
the remaining `|cD| = w' - s - w` symbols are dropped (`usub`). `topTrunc_bits` computes the
emitted bits of one part, `topShiftF_coeffSyms` the emitted word: for coefficients fitting `w'`
signed bits and `s + w ≤ w'`, `encZ A w' Z` becomes `encZ A w (fun p => tdivZ s (Z p))`.
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Node

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Layer


variable {T Q A : ℕ} {U : Type} {P : Type} (body : P → Pr P T Q A U)

/-! ### Word passes -/

/-- Run the word program `wp` while `src` is nonempty. -/
def topWords (src : Fin T) (wp : Pr P T Q A U) : Pr P T Q A U :=
  .seq (.act (peekR src)) (.loop (·.flag) wp)

/-- **Per-word specification.** From `src` holding a word `x` of `L` symbols on top of `rest` and
registers satisfying `G`, `wp` leaves `src` holding `rest`, pushes `(F x).reverse` onto `dst`,
records in `flag` whether `rest` is nonempty and keeps every other register and `user`, in `c`
steps. -/
def TopWordSpec (wp : Pr P T Q A U) (src dst : Fin T) (G : Regs T A → Prop) (L : ℕ)
    (F : List (Fin (A + 4)) → List (Fin (A + 4))) (c : ℕ) : Prop :=
  ∀ (x rest : List (Fin (A + 4))) (v : HS T Q A U) (S : Stacks T A), x.length = L →
    S.R src = x ++ rest → G S.R →
    ∃ v' : HS T Q A U, v'.user = v.user ∧ v'.flag = rest.head?.isSome ∧
      Exec body wp (mk v S) c
        (mk v' { S with
          R := Function.update (Function.update S.R src rest) dst ((F x).reverse ++ S.R dst) })

/-- `G` reads neither `src` nor `dst`. -/
def TopWordFrame (src dst : Fin T) (G : Regs T A → Prop) : Prop :=
  ∀ (R : Regs T A) (l l' : List (Fin (A + 4))), G R →
    G (Function.update (Function.update R src l) dst l')

theorem topWords_loop {wp : Pr P T Q A U} {src dst : Fin T} (hsd : src ≠ dst)
    {G : Regs T A → Prop} (hG : TopWordFrame src dst G) {L : ℕ}
    {F : List (Fin (A + 4)) → List (Fin (A + 4))} {c : ℕ} (hL : 1 ≤ L)
    (hwp : TopWordSpec body wp src dst G L F c) :
    ∀ (ws : List (List (Fin (A + 4)))) (v : HS T Q A U) (S : Stacks T A),
      (∀ x ∈ ws, x.length = L) → S.R src = ws.flatten → G S.R →
      v.flag = ws.flatten.head?.isSome →
      ∃ v' : HS T Q A U, v'.user = v.user ∧
        Exec body (.loop (·.flag) wp) (mk v S) (ws.length * (c + 1) + 1)
          (mk v' { S with
            R := Function.update (Function.update S.R src []) dst
              ((ws.map F).flatten.reverse ++ S.R dst) }) := by
  intro ws
  induction ws with
  | nil =>
      intro v S _ hs _ hf
      refine ⟨v, rfl, ?_⟩
      have hR : ({ S with
          R := Function.update (Function.update S.R src []) dst
            ((([] : List (List (Fin (A + 4)))).map F).flatten.reverse ++ S.R dst) } : Stacks T A)
          = S := by
        cases S with
        | mk inp out L R =>
          simp only at hs ⊢
          congr 1
          funext k
          by_cases hk : k = dst
          · subst hk; simp
          · by_cases hk' : k = src
            · subst hk'; simp [hk, hs]
            · simp [hk, hk']
      rw [hR]
      exact Exec.cast (.loop_false (by simpa using hf)) (by simp) rfl
  | cons x ws ih =>
      intro v S hlen hs hg hf
      have hx : x.length = L := hlen x List.mem_cons_self
      obtain ⟨v₁, hu₁, hf₁, he₁⟩ := hwp x ws.flatten v S hx (by simpa using hs) hg
      obtain ⟨v₂, hu₂, he₂⟩ := ih v₁
        { S with
          R := Function.update (Function.update S.R src ws.flatten) dst ((F x).reverse ++ S.R dst) }
        (fun y hy => hlen y (List.mem_cons_of_mem _ hy)) (by simp [Function.update_of_ne hsd])
        (hG _ _ _ hg) hf₁
      refine ⟨v₂, hu₂.trans hu₁, ?_⟩
      have hne : (x ++ ws.flatten).head?.isSome = true := by
        cases x with
        | nil => simp at hx; omega
        | cons a x => simp
      have hf' : v.flag = true := by rw [hf, List.flatten_cons]; exact hne
      refine Exec.cast (Exec.loop_true hf' he₁ he₂) (by simp; ring) ?_
      congr 2
      funext k
      by_cases hk : k = dst
      · subst hk; simp
      · by_cases hk' : k = src
        · subst hk'; simp [hk]
        · simp [hk, hk']

/-- A word pass: the words of `src` through `wp` onto `dst`, then back onto `src` in order. -/
def topPass (src dst : Fin T) (wp : Pr P T Q A U) : Pr P T Q A U :=
  .seq (topWords src wp) (moveR dst src id)

/-- **A word pass.** With `src` holding the words `ws` of `L ≥ 1` symbols each, `dst` empty and
the other registers satisfying `G`, `topPass` leaves `src` holding the images
`(ws.map F).flatten`; every other register and `user` end as they started. -/
theorem topPass_exec {wp : Pr P T Q A U} {src dst : Fin T} (hsd : src ≠ dst)
    {G : Regs T A → Prop} (hG : TopWordFrame src dst G) {L : ℕ}
    {F : List (Fin (A + 4)) → List (Fin (A + 4))} {c : ℕ} (hL : 1 ≤ L)
    (hwp : TopWordSpec body wp src dst G L F c)
    (ws : List (List (Fin (A + 4)))) (v : HS T Q A U) (S : Stacks T A)
    (hlen : ∀ x ∈ ws, x.length = L) (hs : S.R src = ws.flatten) (hd : S.R dst = [])
    (hg : G S.R) :
    ∃ v' : HS T Q A U, v'.user = v.user ∧
      Exec body (topPass src dst wp) (mk v S)
        (1 + (ws.length * (c + 1) + 1) + (2 * (ws.map F).flatten.length + 2))
        (mk v' { S with R := Function.update S.R src (ws.map F).flatten }) := by
  have h0 := Exec.act (body := body) (peekR src : Act T Q A U) (mk v S)
  rw [peekR_run] at h0
  obtain ⟨v₁, hu₁, he₁⟩ := topWords_loop body hsd hG hL hwp ws
    { v with flag := (S.R src).head?.isSome } S hlen hs hg
    (by show (S.R src).head?.isSome = _; rw [hs])
  obtain ⟨v₂, hu₂, he₂⟩ := moveR_exec body dst src hsd.symm id v₁
    { S with
      R := Function.update (Function.update S.R src []) dst
        ((ws.map F).flatten.reverse ++ S.R dst) }
  refine ⟨v₂, hu₂.trans hu₁, Exec.cast (Exec.seq (Exec.seq h0 he₁) he₂) ?_ ?_⟩
  · simp [hd]
  · congr 2
    funext k
    simp only [movedR, hd, List.append_nil, List.map_id, List.reverse_reverse, Function.update_self]
    by_cases hk : k = src
    · subst hk; simp [hsd]
    · by_cases hk' : k = dst
      · subst hk'; simp [hk, hd]
      · simp [hk, hk']

/-! ### Counted copies and repeats -/

/-- **A counted copy.** `Shift.counted c t (Shift.copyStep c t src dst)` moves `|c|` symbols from
`src` onto `dst` (reversed), restoring the counter `c` through the empty spare `t`. -/
theorem topCopyC_exec {c t src dst : Fin T} (hreg : [c, t, src, dst].Nodup)
    (ys rest : List (Fin (A + 4))) (v : HS T Q A U) (S : Stacks T A)
    (hc : (S.R c).length = ys.length) (hs : S.R src = ys ++ rest) (ht : S.R t = []) :
    ∃ v' : HS T Q A U, Shift.Scratch v v' ∧
      Exec body (Shift.counted c t (Shift.copyStep c t src dst)) (mk v S) (4 * ys.length + 4)
        (mk v' { S with
          R := Function.update (Function.update S.R src rest) dst (ys.reverse ++ S.R dst) }) := by
  simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil,
    not_false_eq_true, and_true, List.nodup_nil] at hreg
  obtain ⟨⟨hct, hcs, hcd⟩, ⟨hts, htd⟩, hsd⟩ := hreg
  obtain ⟨v₁, R₁, hv₁, he₁, hc₁, ht₁, hs₁, hd₁, ho₁⟩ := Shift.copyStep_loop body c t src dst hct
    (Ne.symm hcs) (Ne.symm hts) (Ne.symm hcd) (Ne.symm htd) (Ne.symm hsd) (S.R c) ys rest
    { v with flag := (S.R c).head?.isSome } S hc rfl hs rfl
  obtain ⟨v₂, R₂, hv₂, he₂, hc₂, ht₂, ho₂⟩ := Shift.counted_exec body c t hct _ v v₁ S R₁ ht hv₁
    he₁ hc₁ ht₁
  refine ⟨v₂, hv₂, Exec.cast he₂ (by rw [hc]) ?_⟩
  congr 2
  funext k
  by_cases h1 : k = c
  · subst h1; rw [hc₂]; simp [Function.update_of_ne hcs, Function.update_of_ne hcd]
  by_cases h2 : k = t
  · subst h2; rw [ht₂]; simp [Function.update_of_ne hts, Function.update_of_ne htd, ht]
  rw [ho₂ k h1 h2]
  by_cases h3 : k = src
  · subst h3; rw [hs₁]; simp [hsd]
  by_cases h4 : k = dst
  · subst h4; rw [hd₁]; simp
  rw [ho₁ k h1 h2 h3 h4]
  simp [h3, h4]

/-- Push the top of `d` again. -/
def topDupF (d : Fin T) (k : Act T Q A U) : Act T Q A U :=
  .peek (.rt d) (fun v o => { v with sym := o }) (.push (.rt d) (fun v => v.sym.getD blank) k)

/-- The effect of `topDupF d`. -/
def topDupFx (d : Fin T) : Fin (A + 4) → Regs T A → Regs T A :=
  fun _ R => Function.update R d ((R d).head?.getD blank :: R d)

lemma regFx_topDup (d : Fin T) :
    RegFx (topDupF (T := T) (Q := Q) (A := A) (U := U) d) (topDupFx d) := by
  intro x k v S _
  refine ⟨{ v with sym := (S.R d).head? }, rfl, ?_⟩
  simp [topDupF, topDupFx, Action.run, update_rt]

lemma frame_topDup {a d : Fin T} (had : a ≠ d) : Frame a (topDupFx (A := A) d) := by
  intro x R l
  funext k
  simp only [topDupFx, Function.update_apply]
  split_ifs <;> simp_all

lemma foldl_topDup (d : Fin T) (h : Fin (A + 4)) : ∀ (l : List (Fin (A + 4))) (R : Regs T A),
    (R d).head? = some h →
    l.foldl (fun R x => topDupFx d x R) R = Function.update R d (List.replicate l.length h ++ R d)
  | [], R, _ => by simp
  | x :: l, R, hR => by
      have hh : (R d).head?.getD blank = h := by rw [hR]; rfl
      simp only [List.foldl_cons]
      rw [foldl_topDup d h l _ (by simp [topDupFx, hh])]
      simp [topDupFx, hh, List.replicate_succ']

/-! ### Signed words -/

/-- `x` fits a signed `k`-bit word: `-2^(k-1) ≤ x < 2^(k-1)`. -/
def TopFits (k : ℕ) (x : ℤ) : Prop := -(2 : ℤ) ^ (k - 1) ≤ x ∧ x < 2 ^ (k - 1)

/-- Both parts of `z` fit a signed `k`-bit word. -/
def TopFitsZ (k : ℕ) (z : GaussianInt) : Prop := TopFits k z.re ∧ TopFits k z.im

lemma topFits_mono {k k' : ℕ} (hk : 1 ≤ k) (hkk : k ≤ k') {x : ℤ} (hx : TopFits k x) :
    TopFits k' x := by
  have h : (2 : ℤ) ^ (k - 1) ≤ 2 ^ (k' - 1) := pow_le_pow_right₀ (by norm_num) (by omega)
  exact ⟨by linarith [hx.1], by linarith [hx.2]⟩

/-- The residue of a fitting `x` modulo `2^k`: `x`, plus `2^k` for negative `x`. -/
lemma topVal_eq {k : ℕ} (hk : 1 ≤ k) {x : ℤ} (hx : TopFits k x) :
    (((x : ZMod (2 ^ k)).val : ℕ) : ℤ) = x + if x < 0 then 2 ^ k else 0 := by
  rw [ZMod.val_intCast]
  have hp : (2 : ℤ) ^ k = 2 * 2 ^ (k - 1) := by
    rw [← pow_succ']; congr 1; omega
  have hpos : (0 : ℤ) < 2 ^ (k - 1) := by positivity
  obtain ⟨h1, h2⟩ := hx
  push_cast
  split_ifs with hneg
  · rw [← Int.add_emod_right, Int.emod_eq_of_lt] <;> omega
  · rw [Int.emod_eq_of_lt] <;> omega

/-- The top bit of the residue of a fitting `x` is its sign. -/
lemma topVal_sign {k : ℕ} (hk : 1 ≤ k) {x : ℤ} (hx : TopFits k x) :
    (x : ZMod (2 ^ k)).val.testBit (k - 1) = decide (x < 0) := by
  have hv := topVal_eq hk hx
  have hlt := ZMod.val_lt (x : ZMod (2 ^ k))
  set V := (x : ZMod (2 ^ k)).val with hV
  have hp : (2 : ℕ) ^ k = 2 * 2 ^ (k - 1) := by
    rw [← pow_succ']; congr 1; omega
  have hpz : (2 : ℤ) ^ k = 2 * 2 ^ (k - 1) := by exact_mod_cast hp
  have hpos : 0 < 2 ^ (k - 1) := by positivity
  rw [Nat.testBit_eq_decide_div_mod_eq]
  obtain ⟨h1, h2⟩ := hx
  by_cases hneg : x < 0
  · simp only [hneg, ite_true] at hv
    have hge : 2 ^ (k - 1) ≤ V := by
      have : ((2 ^ (k - 1) : ℕ) : ℤ) ≤ (V : ℤ) := by push_cast; omega
      exact_mod_cast this
    have hq : V / 2 ^ (k - 1) = 1 := by
      exact Nat.div_eq_of_lt_le (by omega) (by omega)
    simp [hq, hneg]
  · simp only [hneg, ite_false] at hv
    have hlt' : V < 2 ^ (k - 1) := by
      have : (V : ℤ) < ((2 ^ (k - 1) : ℕ) : ℤ) := by push_cast; omega
      exact_mod_cast this
    simp [Nat.div_eq_of_lt hlt', hneg]

/-- **Sign extension.** For `x` fitting `w ≥ 1` bits and `t < w'`, bit `t` of `x` modulo `2^w'`
is bit `t` of `x` modulo `2^w` below `w` and the sign above. -/
lemma topWiden_bit {w w' : ℕ} (hw : 1 ≤ w) (hww : w ≤ w') {x : ℤ} (hx : TopFits w x) (t : ℕ)
    (ht : t < w') :
    (x : ZMod (2 ^ w')).val.testBit t =
      if t < w then (x : ZMod (2 ^ w)).val.testBit t else decide (x < 0) := by
  have hY := topVal_eq (by omega : 1 ≤ w') (topFits_mono hw hww hx)
  have hy := topVal_eq hw hx
  have hylt := ZMod.val_lt (x : ZMod (2 ^ w))
  set y := (x : ZMod (2 ^ w)).val
  set Y := (x : ZMod (2 ^ w')).val
  have hpw : (2 : ℕ) ^ w' = 2 ^ w * 2 ^ (w' - w) := by rw [← pow_add]; congr 1; omega
  have h1 : 1 ≤ 2 ^ (w' - w) := Nat.one_le_two_pow
  have hYe : Y = 2 ^ w * (if x < 0 then 2 ^ (w' - w) - 1 else 0) + y := by
    have : (Y : ℤ) = ((2 ^ w * (if x < 0 then 2 ^ (w' - w) - 1 else 0) + y : ℕ) : ℤ) := by
      rw [hY]
      split_ifs with hneg
      · simp only [hneg, ite_true] at hy
        push_cast [Nat.cast_sub h1]
        have hpw' : (2 : ℤ) ^ w' = 2 ^ w * 2 ^ (w' - w) := by exact_mod_cast hpw
        rw [hy, hpw']; ring
      · simp only [hneg, ite_false] at hy
        push_cast; omega
    exact_mod_cast this
  rw [hYe, Nat.testBit_two_pow_mul_add _ hylt]
  split_ifs with h2 hneg
  · rfl
  · rw [Nat.testBit_two_pow_sub_one]; simp [hneg]; omega
  · simp [hneg]

/-! ### Widening -/

/-- The widened word: `x` followed by `w' - w` copies of its last symbol. -/
def topWidenF (w w' : ℕ) (x : List (Fin (A + 4))) : List (Fin (A + 4)) :=
  x ++ List.replicate (w' - w) (x.getLast?.getD blank)


/-- Widen one word: copy `|c₁|` symbols from `src` onto `dst`, push `|c₂|` copies of the last
one, and record in `flag` whether `src` is nonempty (spare `sp`). -/
def topWidenWord (src dst c₁ c₂ sp : Fin T) : Pr P T Q A U :=
  .seq (Shift.counted c₁ sp (Shift.copyStep c₁ sp src dst))
    (.seq (scanR c₂ sp (topDupF dst)) (.act (peekR src)))

/-- The registers of the widening pass: `c₁` holds `w` symbols, `c₂` holds `w' - w`, `sp` is
empty. -/
def topWidenG (c₁ c₂ sp : Fin T) (w w' : ℕ) (R : Regs T A) : Prop :=
  (R c₁).length = w ∧ (R c₂).length = w' - w ∧ R sp = []

theorem topWidenWord_spec {src dst c₁ c₂ sp : Fin T} (hreg : [src, dst, c₁, c₂, sp].Nodup)
    {w w' : ℕ} (hw : 1 ≤ w) :
    TopWordSpec body (topWidenWord src dst c₁ c₂ sp) src dst (topWidenG c₁ c₂ sp w w') w
      (topWidenF w w') ((4 * w + 4) + ((4 * (w' - w) + 4) + 1)) := by
  have hreg' := hreg
  simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil,
    not_false_eq_true, and_true, List.nodup_nil] at hreg'
  obtain ⟨⟨hsd, hs1, hs2, hss⟩, ⟨hd1, hd2, hds⟩, ⟨h12, h1s⟩, h2s⟩ := hreg'
  intro x rest v S hx hs ⟨hc₁, hc₂, hsp⟩
  have hne : x ≠ [] := by rintro rfl; simp at hx; omega
  obtain ⟨v₁, hv₁, e₁⟩ := topCopyC_exec body (c := c₁) (t := sp) (src := src) (dst := dst)
    (by simp [h1s, Ne.symm hs1, Ne.symm hd1, Ne.symm hss, Ne.symm hds, hsd]) x rest v S
    (by rw [hc₁, hx]) hs hsp
  rw [hx] at e₁
  set R₁ := Function.update (Function.update S.R src rest) dst (x.reverse ++ S.R dst) with hR₁
  obtain ⟨v₂, hu₂, e₂⟩ := scanR_exec' body h2s (regFx_topDup dst) (frame_topDup (Ne.symm hd2))
    (frame_topDup (Ne.symm hds)) v₁ { S with R := R₁ }
    (by simp [hR₁, Function.update_of_ne (Ne.symm hss), Function.update_of_ne (Ne.symm hds), hsp])
  have hlast : (R₁ dst).head? = some (x.getLast hne) := by
    simp [hR₁, List.head?_reverse, List.getLast?_eq_some_getLast hne]
  rw [foldl_topDup dst _ _ _ hlast] at e₂
  have hc₂' : (R₁ c₂).length = w' - w := by
    simp [hR₁, Function.update_of_ne (Ne.symm hs2), Function.update_of_ne (Ne.symm hd2), hc₂]
  rw [hc₂'] at e₂
  set R₂ := Function.update R₁ dst (List.replicate (w' - w) (x.getLast hne) ++ R₁ dst) with hR₂
  have e₃ := Exec.act (body := body) (peekR src : Act T Q A U) (mk v₂ { S with R := R₂ })
  rw [peekR_run] at e₃
  refine ⟨{ v₂ with flag := rest.head?.isSome }, by rw [hu₂, hv₁.user], rfl,
    Exec.cast (Exec.seq e₁ (Exec.seq e₂ e₃)) rfl ?_⟩
  congr 1
  · simp [hR₂, hR₁, Function.update_of_ne hsd]
  · congr 1
    funext k
    by_cases hk : k = dst
    · subst hk
      simp [hR₂, hR₁, topWidenF, List.getLast?_eq_some_getLast hne]
    · simp [hR₂, hR₁, hk]

/-- The step count of the widening pass on `R` rows of `2^n` records of `r` coefficients. -/
def topWidenCost (R n r w w' : ℕ) : ℕ :=
  1 + (R * 2 ^ n * r * ((4 * w + 4) + ((4 * (w' - w) + 4) + 1) + 1) + 1) +
    (2 * (R * 2 ^ n * r * w') + 2)

/-- **Widening a word.** The widened word of a coefficient fitting `w` bits is its `w'`-bit
word. -/
theorem topWidenF_coeffSyms {w w' : ℕ} (hw : 1 ≤ w) (hww : w ≤ w') (z : GaussianInt)
    (hz : TopFitsZ w z) :
    topWidenF w w' (coeffSyms A w (red w z)) = coeffSyms A w' (red w' z) := by
  have hlast : (coeffSyms A w (red w z)).getLast?.getD blank =
      pairSym A (decide (z.re < 0)) (decide (z.im < 0)) := by
    rw [List.getLast?_eq_getElem?]
    simp only [coeffSyms, List.length_ofFn, red]
    rw [List.getElem?_ofFn]
    simp only [show w - 1 < w by omega, dite_true, Option.getD_some]
    rw [topVal_sign hw hz.1, topVal_sign hw hz.2]
  apply List.ext_getElem
  · simp [topWidenF]; omega
  · intro t h1 h2
    simp only [length_coeffSyms] at h2
    simp only [topWidenF, hlast]
    by_cases ht : t < w
    · rw [List.getElem_append_left (by simpa using ht)]
      simp only [coeffSyms, red, List.getElem_ofFn]
      rw [topWiden_bit hw hww hz.1 t h2, topWiden_bit hw hww hz.2 t h2]
      simp only [ht, ite_true]
    · rw [List.getElem_append_right (by simpa using ht)]
      simp only [coeffSyms, red, List.getElem_ofFn, List.getElem_replicate]
      rw [topWiden_bit hw hww hz.1 t h2, topWiden_bit hw hww hz.2 t h2]
      simp only [ht, ite_false]

/-! ### Truncating shift: bit model -/

/-- The majority of three bits (the carry of a full adder). -/
def topMaj (a b c : Bool) : Bool := (a && b) || (a && c) || (b && c)

/-- The carry out of adding the bits `bs` and the constant bits `σ` to the carry `c`. -/
def topAbsorb (σ : Bool) : Bool → List Bool → Bool
  | c, [] => c
  | c, b :: bs => topAbsorb σ (topMaj b σ c) bs

/-- The bits of `bs` plus the carry `c`, truncated to the length of `bs`. -/
def topEmit : Bool → List Bool → List Bool
  | _, [] => []
  | c, b :: bs => xor b c :: topEmit (b && c) bs

lemma topMod_two_mul {r Y M : ℕ} (hr : r < 2) (hM : 0 < M) :
    (r + 2 * Y) % (2 * M) = r + 2 * (Y % M) := by
  have hlt := Nat.mod_lt Y hM
  conv_lhs => rw [← Nat.div_add_mod Y M]
  rw [show r + 2 * (M * (Y / M) + Y % M) = (r + 2 * (Y % M)) + 2 * M * (Y / M) by ring,
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]

lemma topValBits_take : ∀ (l : List Bool) (k : ℕ), valBits (l.take k) = valBits l % 2 ^ k
  | [], k => by simp [valBits]
  | b :: l, 0 => by simp [valBits, Nat.mod_one]
  | b :: l, k + 1 => by
      simp only [List.take_succ_cons, valBits]
      rw [topValBits_take l k, pow_succ', topMod_two_mul (Bool.toNat_lt b) (by positivity)]

lemma topValBits_drop : ∀ (l : List Bool) (k : ℕ), valBits (l.drop k) = valBits l / 2 ^ k
  | [], k => by simp [valBits]
  | b :: l, 0 => by simp
  | b :: l, k + 1 => by
      simp only [List.drop_succ_cons, valBits]
      have hb := Bool.toNat_lt b
      rw [topValBits_drop l k, pow_succ', ← Nat.div_div_eq_div_mul,
        show (b.toNat + 2 * valBits l) / 2 = valBits l by omega]

lemma topGetElem_valBits : ∀ (l : List Bool) (t : ℕ) (h : t < l.length),
    l[t] = (valBits l).testBit t
  | b :: l, 0, _ => by cases b <;> simp [valBits, Nat.testBit_zero]
  | b :: l, t + 1, h => by
      have hb := Bool.toNat_lt b
      simp only [List.getElem_cons_succ, valBits]
      rw [topGetElem_valBits l t (by simpa using h), Nat.testBit_succ]
      congr 1
      omega

lemma topAbsorb_val (σ : Bool) : ∀ (c : Bool) (bs : List Bool),
    (valBits bs + σ.toNat * (2 ^ bs.length - 1) + c.toNat) / 2 ^ bs.length =
      (topAbsorb σ c bs).toNat
  | c, [] => by cases c <;> cases σ <;> simp [valBits, topAbsorb]
  | c, b :: bs => by
      rw [topAbsorb, ← topAbsorb_val σ (topMaj b σ c) bs]
      simp only [valBits, List.length_cons]
      have hP : 1 ≤ 2 ^ bs.length := Nat.one_le_two_pow
      rw [pow_succ', ← Nat.div_div_eq_div_mul]
      congr 1
      cases b <;> cases σ <;> cases c <;> simp [topMaj] <;> omega

lemma topEmit_length : ∀ (c : Bool) (bs : List Bool), (topEmit c bs).length = bs.length
  | _, [] => rfl
  | c, b :: bs => by simp [topEmit, topEmit_length _ bs]

lemma topEmit_val : ∀ (c : Bool) (bs : List Bool),
    valBits (topEmit c bs) = (valBits bs + c.toNat) % 2 ^ bs.length
  | c, [] => by cases c <;> simp [topEmit, valBits]
  | c, b :: bs => by
      simp only [topEmit, valBits, List.length_cons]
      rw [topEmit_val (b && c) bs, pow_succ',
        show b.toNat + 2 * valBits bs + c.toNat =
          (xor b c).toNat + 2 * (valBits bs + (b && c).toNat) by
            cases b <;> cases c <;> simp <;> omega,
        topMod_two_mul (Bool.toNat_lt _) (by positivity)]

/-- Rounding a negative `x` up: `(x + b - 1) / b` is the truncated quotient. -/
lemma topEdiv_neg {x b : ℤ} (hx : x < 0) (hb : 0 < b) : (x + (b - 1)) / b = x.tdiv b := by
  have h1 : x.tdiv b = -((-x) / b) := by
    rw [← Int.tdiv_eq_ediv_of_nonneg (by omega), Int.neg_tdiv, neg_neg]
  have hy := Int.emod_add_mul_ediv (-x) b
  have h0 := Int.emod_nonneg (-x) hb.ne'
  have hlt := Int.emod_lt_of_pos (-x) hb
  rw [h1, show x + (b - 1) = (b - 1 - (-x) % b) + b * (-((-x) / b)) by linear_combination hy,
    Int.add_mul_ediv_left _ _ hb.ne', Int.ediv_eq_zero_of_lt (by omega) (by omega), zero_add]

/-- The rounded shift of the residue: for `x` fitting `w'` bits and `s ≤ w'`,
`(V + σ (2^s - 1)) / 2^s = tdiv x 2^s + σ 2^(w' - s)`, `V` the residue and `σ` the sign. -/
lemma topTrunc_int {w' s : ℕ} (hw' : 1 ≤ w') (hs : s ≤ w') {x : ℤ} (hx : TopFits w' x) :
    ((((x : ZMod (2 ^ w')).val + (decide (x < 0)).toNat * (2 ^ s - 1)) / 2 ^ s : ℕ) : ℤ) =
      x.tdiv (2 ^ s) + (decide (x < 0)).toNat * 2 ^ (w' - s) := by
  have hv := topVal_eq hw' hx
  have hpow : (2 : ℤ) ^ w' = 2 ^ s * 2 ^ (w' - s) := by rw [← pow_add]; congr 1; omega
  have hs1 : 1 ≤ 2 ^ s := Nat.one_le_two_pow
  have hpos : (0 : ℤ) < 2 ^ s := by positivity
  rw [Int.natCast_div]
  push_cast [Nat.cast_sub hs1]
  by_cases hneg : x < 0
  · simp only [hneg, ite_true] at hv
    simp only [hneg, decide_true, Bool.toNat_true, Nat.cast_one, one_mul]
    rw [hv, hpow, show x + 2 ^ s * 2 ^ (w' - s) + (2 ^ s - 1) =
        (x + (2 ^ s - 1)) + 2 ^ s * 2 ^ (w' - s) by ring,
      Int.add_mul_ediv_left _ _ hpos.ne', topEdiv_neg hneg hpos]
  · simp only [hneg, ite_false] at hv
    simp only [hneg, decide_false, Bool.toNat_false, Nat.cast_zero, zero_mul, add_zero] at hv ⊢
    rw [hv, Int.tdiv_eq_ediv_of_nonneg (by omega)]

/-- **The truncating shift on bits.** For `x` fitting `w'` bits and `s + w ≤ w'`, absorbing
the low `s` bits of the residue with the sign bits and emitting the next `w` bits with the carry
gives the `w` low bits of `tdiv x 2^s`. -/
theorem topTrunc_bits {w' s w : ℕ} (hw' : 1 ≤ w') (hsw : s + w ≤ w') {x : ℤ}
    (hx : TopFits w' x) :
    topEmit (topAbsorb (decide (x < 0)) false
        ((List.ofFn fun t : Fin w' => (x : ZMod (2 ^ w')).val.testBit t).take s))
      (((List.ofFn fun t : Fin w' => (x : ZMod (2 ^ w')).val.testBit t).drop s).take w) =
      List.ofFn fun t : Fin w => ((x.tdiv (2 ^ s) : ℤ) : ZMod (2 ^ w)).val.testBit t := by
  set bs := List.ofFn fun t : Fin w' => (x : ZMod (2 ^ w')).val.testBit t with hbs
  set V := (x : ZMod (2 ^ w')).val with hV
  set σ := decide (x < 0) with hσ
  have hval : valBits bs = V := valBits_val w' _
  have hlen : bs.length = w' := by simp [hbs]
  have hts : (bs.take s).length = s := by simp [hlen]; omega
  have htw : ((bs.drop s).take w).length = w := by simp [hlen]; omega
  set out := topEmit (topAbsorb σ false (bs.take s)) ((bs.drop s).take w) with hout
  have hol : out.length = w := by rw [hout, topEmit_length, htw]
  have hcarry := topAbsorb_val σ false (bs.take s)
  rw [hts, topValBits_take, hval] at hcarry
  set N := (V + σ.toNat * (2 ^ s - 1)) / 2 ^ s with hN
  have hspl : N = V / 2 ^ s + (V % 2 ^ s + σ.toNat * (2 ^ s - 1)) / 2 ^ s := by
    rw [hN]
    conv_lhs => rw [← Nat.div_add_mod V (2 ^ s)]
    rw [show 2 ^ s * (V / 2 ^ s) + V % 2 ^ s + σ.toNat * (2 ^ s - 1) =
        (V % 2 ^ s + σ.toNat * (2 ^ s - 1)) + 2 ^ s * (V / 2 ^ s) by ring,
      Nat.add_mul_div_left _ _ (by positivity)]
    ring
  have hvo : valBits out = N % 2 ^ w := by
    rw [hout, topEmit_val, htw, topValBits_take, topValBits_drop, hval, ← hcarry,
      Bool.toNat_false, add_zero, Nat.mod_add_mod, hspl]
  have hq : (((x.tdiv (2 ^ s) : ℤ) : ZMod (2 ^ w))).val = N % 2 ^ w := by
    have hi := topTrunc_int hw' (by omega : s ≤ w') hx
    rw [← hV, ← hσ, ← hN] at hi
    have h2w : (2 : ZMod (2 ^ w)) ^ w = 0 := by exact_mod_cast ZMod.natCast_self (2 ^ w)
    have hz : (2 : ZMod (2 ^ w)) ^ (w' - s) = 0 := by
      rw [show w' - s = w + (w' - s - w) by omega, pow_add, h2w, zero_mul]
    have : ((N : ℤ) : ZMod (2 ^ w)) = ((x.tdiv (2 ^ s) : ℤ) : ZMod (2 ^ w)) := by
      rw [hi]; push_cast; rw [hz]; ring
    rw [← this, Int.cast_natCast, ZMod.val_natCast]
  apply List.ext_getElem
  · simp [hol]
  · intro t h1 h2
    rw [topGetElem_valBits out t h1, hvo]
    simp only [List.getElem_ofFn, hq]

/-- The shifted word of `x`: the parts of `x` with their sign bits added below position `s`
(rounding toward zero), bits `s, …, s + w - 1`. -/
def topShiftF (A s w : ℕ) (x : List (Fin (A + 4))) : List (Fin (A + 4)) :=
  List.zipWith (pairSym A)
    (topEmit (topAbsorb (pairRe (x.getLast?.getD blank)) false ((x.take s).map pairRe))
      (((x.drop s).take w).map pairRe))
    (topEmit (topAbsorb (pairIm (x.getLast?.getD blank)) false ((x.take s).map pairIm))
      (((x.drop s).take w).map pairIm))

/-- The carry pair after absorbing the symbol `b` with the sign pair `σ` into the carry `c`. -/
def topAbsSym (b σ c : Fin (A + 4)) : Fin (A + 4) :=
  pairSym A (topMaj (pairRe b) (pairRe σ) (pairRe c)) (topMaj (pairIm b) (pairIm σ) (pairIm c))

/-- The output pair of the symbol `b` plus the carry `c`. -/
def topOutSym (b c : Fin (A + 4)) : Fin (A + 4) :=
  pairSym A (xor (pairRe b) (pairRe c)) (xor (pairIm b) (pairIm c))

/-- The carry pair of the symbol `b` plus the carry `c`. -/
def topCarSym (b c : Fin (A + 4)) : Fin (A + 4) :=
  pairSym A (pairRe b && pairRe c) (pairIm b && pairIm c)

/-! ### Truncating shift: the machine -/

/-- Copy the top of `tmp` (the sign pair) onto `sg` and push the zero carry pair onto `cy`. -/
def topSignAct (tmp sg cy : Fin T) : Act T Q A U :=
  .peek (.rt tmp) (fun v o => { v with sym := o })
    (.push (.rt sg) (fun v => v.sym.getD blank)
      (.push (.rt cy) (fun _ => pairSym A false false) .done))

/-- Absorb the top of `src`: add it and the sign pair on `sg` to the carry pair on `cy`. -/
def topAbsF (src sg cy : Fin T) (k : Act T Q A U) : Act T Q A U :=
  .pop (.rt src) (fun v o => { v with sym := o })
    (.pop (.rt cy) (fun v o => { v with scan := Function.update v.scan cy (o.getD blank) })
      (.peek (.rt sg) (fun v o => { v with scan := Function.update v.scan sg (o.getD blank) })
        (.push (.rt cy) (fun v => topAbsSym (v.sym.getD blank) (v.scan sg) (v.scan cy)) k)))

/-- The effect of `topAbsF`. -/
def topAbsFx (src sg cy : Fin T) : Fin (A + 4) → Regs T A → Regs T A :=
  fun _ R => Function.update (Function.update R src (R src).tail) cy
    (topAbsSym ((R src).head?.getD blank) ((R sg).head?.getD blank) ((R cy).head?.getD blank) ::
      (R cy).tail)

/-- Emit the top of `src` plus the carry pair on `cy` onto `dst`. -/
def topEmitF (src dst cy : Fin T) (k : Act T Q A U) : Act T Q A U :=
  .pop (.rt src) (fun v o => { v with sym := o })
    (.pop (.rt cy) (fun v o => { v with scan := Function.update v.scan cy (o.getD blank) })
      (.push (.rt dst) (fun v => topOutSym (v.sym.getD blank) (v.scan cy))
        (.push (.rt cy) (fun v => topCarSym (v.sym.getD blank) (v.scan cy)) k)))

/-- The effect of `topEmitF`. -/
def topEmitFx (src dst cy : Fin T) : Fin (A + 4) → Regs T A → Regs T A :=
  fun _ R => Function.update (Function.update (Function.update R src (R src).tail) cy
      (topCarSym ((R src).head?.getD blank) ((R cy).head?.getD blank) :: (R cy).tail)) dst
    (topOutSym ((R src).head?.getD blank) ((R cy).head?.getD blank) :: R dst)

/-- The final carry of `topEmit`. -/
def topEmitCar : Bool → List Bool → Bool
  | c, [] => c
  | c, b :: bs => topEmitCar (b && c) bs

/-- Drop `sg` and `cy` and record in `flag` whether `src` is nonempty. -/
def topEndAct (sg cy src : Fin T) : Act T Q A U :=
  .pop (.rt sg) (fun v _ => v) (.pop (.rt cy) (fun v _ => v) (peekR src))

lemma regFx_topAbs {src sg cy : Fin T} (hsc : src ≠ cy) (hss : src ≠ sg) (hgc : sg ≠ cy) :
    RegFx (topAbsF (T := T) (Q := Q) (A := A) (U := U) src sg cy) (topAbsFx src sg cy) := by
  intro x k v S _
  refine ⟨{ v with
    sym := (S.R src).head?
    scan := Function.update (Function.update v.scan cy ((S.R cy).head?.getD blank)) sg
      ((S.R sg).head?.getD blank) }, rfl, ?_⟩
  simp only [topAbsF, topAbsFx, Action.run, mk_var, mk_stk, get_rt, update_rt, store_mk,
    Function.update_of_ne hsc.symm, Function.update_of_ne hss.symm, Function.update_of_ne hgc,
    Function.update_of_ne hgc.symm, Function.update_self, Function.update_idem]

lemma frame_topAbs {a src sg cy : Fin T} (has : a ≠ src) (hag : a ≠ sg) (hac : a ≠ cy) :
    Frame a (topAbsFx (A := A) src sg cy) := by
  intro x R l
  funext k
  simp only [topAbsFx, Function.update_apply]
  split_ifs <;> simp_all

lemma regFx_topEmit {src dst cy : Fin T} (hsd : src ≠ dst) (hsc : src ≠ cy) (hdc : dst ≠ cy) :
    RegFx (topEmitF (T := T) (Q := Q) (A := A) (U := U) src dst cy) (topEmitFx src dst cy) := by
  intro x k v S _
  refine ⟨{ v with
    sym := (S.R src).head?
    scan := Function.update v.scan cy ((S.R cy).head?.getD blank) }, rfl, ?_⟩
  simp only [topEmitF, topEmitFx, Action.run, mk_var, mk_stk, get_rt, update_rt, store_mk,
    Function.update_of_ne hsc.symm, Function.update_of_ne hsd.symm, Function.update_of_ne hdc,
    Function.update_of_ne hdc.symm, Function.update_self]
  rw [Function.update_comm hdc, Function.update_idem]

lemma frame_topEmit {a src dst cy : Fin T} (has : a ≠ src) (had : a ≠ dst) (hac : a ≠ cy) :
    Frame a (topEmitFx (A := A) src dst cy) := by
  intro x R l
  funext k
  simp only [topEmitFx, Function.update_apply]
  split_ifs <;> simp_all

lemma foldl_topAbs (hA : 4 ≤ A) {src sg cy : Fin T} (hsc : src ≠ cy) (hss : src ≠ sg)
    (hgc : sg ≠ cy) (σ : Fin (A + 4)) :
    ∀ (l x rest : List (Fin (A + 4))) (R : Regs T A) (cr ci : Bool), l.length = x.length →
      R src = x ++ rest → R cy = [pairSym A cr ci] → R sg = [σ] →
      l.foldl (fun R a => topAbsFx src sg cy a R) R =
        Function.update (Function.update R src rest) cy
          [pairSym A (topAbsorb (pairRe σ) cr (x.map pairRe))
            (topAbsorb (pairIm σ) ci (x.map pairIm))]
  | [], x, rest, R, cr, ci, hl, hs, hc, _ => by
      obtain rfl : x = [] := List.eq_nil_of_length_eq_zero hl.symm
      funext k
      simp only [List.nil_append] at hs
      simp only [List.foldl_nil, Function.update_apply]
      split_ifs with h1 h2 <;> simp_all [topAbsorb]
  | a :: l, e :: x, rest, R, cr, ci, hl, hs, hc, hg => by
      simp only [List.foldl_cons]
      rw [foldl_topAbs hA hsc hss hgc σ l x rest _ (topMaj (pairRe e) (pairRe σ) cr)
        (topMaj (pairIm e) (pairIm σ) ci) (by simpa using hl)
        (by simp [topAbsFx, Function.update_of_ne hsc, hs])
        (by simp [topAbsFx, hs, hc, hg, topAbsSym, pairRe_pairSym hA, pairIm_pairSym hA])
        (by simp [topAbsFx, Function.update_of_ne hss.symm, Function.update_of_ne hgc, hg])]
      funext k
      simp only [topAbsFx, Function.update_apply]
      split_ifs <;> simp_all [topAbsorb]
  | _ :: _, [], _, _, _, _, hl, _, _, _ => by simp at hl

lemma foldl_topEmit (hA : 4 ≤ A) {src dst cy : Fin T} (hsd : src ≠ dst) (hsc : src ≠ cy)
    (hdc : dst ≠ cy) :
    ∀ (l x rest : List (Fin (A + 4))) (R : Regs T A) (cr ci : Bool), l.length = x.length →
      R src = x ++ rest → R cy = [pairSym A cr ci] →
      l.foldl (fun R a => topEmitFx src dst cy a R) R =
        Function.update (Function.update (Function.update R src rest) cy
          [pairSym A (topEmitCar cr (x.map pairRe)) (topEmitCar ci (x.map pairIm))]) dst
          ((List.zipWith (pairSym A) (topEmit cr (x.map pairRe))
            (topEmit ci (x.map pairIm))).reverse ++ R dst)
  | [], x, rest, R, cr, ci, hl, hs, hc => by
      obtain rfl : x = [] := List.eq_nil_of_length_eq_zero hl.symm
      funext k
      simp only [List.nil_append] at hs
      simp only [List.foldl_nil, Function.update_apply]
      split_ifs with h1 h2 h3 <;> simp_all [topEmit, topEmitCar]
  | a :: l, e :: x, rest, R, cr, ci, hl, hs, hc => by
      simp only [List.foldl_cons]
      rw [foldl_topEmit hA hsd hsc hdc l x rest _ (pairRe e && cr) (pairIm e && ci)
        (by simpa using hl)
        (by simp [topEmitFx, Function.update_of_ne hsc, Function.update_of_ne hsd, hs])
        (by simp [topEmitFx, Function.update_of_ne hdc.symm, hs, hc, topCarSym,
          pairRe_pairSym hA, pairIm_pairSym hA])]
      funext k
      simp only [topEmitFx, Function.update_apply]
      split_ifs <;> simp_all [topEmit, topEmitCar, topOutSym, pairRe_pairSym hA,
        pairIm_pairSym hA]
  | _ :: _, [], _, _, _, _, hl, _, _ => by simp at hl

/-- Shift one word of `|cW|` symbols: copy it onto `tmp` and back (the sign pair, its last symbol,
goes onto `sg`, a zero carry pair onto `cy`), absorb `|cS|` symbols, emit `|cE|`, drop `|cD|`,
clear `sg` and `cy`, and record in `flag` whether `src` is nonempty (spare `sp`). -/
def topShiftWord (src dst tmp cW cS cE cD sp sg cy : Fin T) : Pr P T Q A U :=
  .seq (Shift.counted cW sp (Shift.copyStep cW sp src tmp))
  (.seq (.act (topSignAct tmp sg cy))
  (.seq (Shift.counted cW sp (Shift.copyStep cW sp tmp src))
  (.seq (scanR cS sp (topAbsF src sg cy))
  (.seq (scanR cE sp (topEmitF src dst cy))
  (.seq (usub cD src sp) (.act (topEndAct sg cy src)))))))

/-- The registers of the shift pass: `cW`, `cS`, `cE`, `cD` hold `w'`, `s`, `w`, `w' - s - w`
symbols; `sp`, `sg`, `cy`, `tmp` are empty. -/
def topShiftG (tmp cW cS cE cD sp sg cy : Fin T) (w' s w : ℕ) (R : Regs T A) : Prop :=
  (R cW).length = w' ∧ (R cS).length = s ∧ (R cE).length = w ∧ (R cD).length = w' - s - w ∧
    R sp = [] ∧ R sg = [] ∧ R cy = [] ∧ R tmp = []

/-- The step count of one shifted word. -/
def topShiftWordCost (w' s w : ℕ) : ℕ :=
  (4 * w' + 4) + (1 + ((4 * w' + 4) + ((4 * s + 4) + ((4 * w + 4) +
    ((4 * (w' - s - w) + 4) + 1)))))

theorem topShiftWord_spec (hA : 4 ≤ A) {src dst tmp cW cS cE cD sp sg cy : Fin T}
    (hreg : [src, dst, tmp, cW, cS, cE, cD, sp, sg, cy].Nodup) {w' s w : ℕ} (hw' : 1 ≤ w')
    (hsw : s + w ≤ w') :
    TopWordSpec body (topShiftWord src dst tmp cW cS cE cD sp sg cy) src dst
      (topShiftG tmp cW cS cE cD sp sg cy w' s w) w' (topShiftF A s w)
      (topShiftWordCost w' s w) := by
  have hreg' := hreg
  simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil,
    not_false_eq_true, and_true, List.nodup_nil] at hreg'
  obtain ⟨⟨hsd, hst, hsW, hsS, hsE, hsD, hsp, hsg, hsc⟩, ⟨hdt, hdW, hdS, hdE, hdD, hdp, hdg, hdc⟩,
    ⟨htW, htS, htE, htD, htp, htg, htc⟩, ⟨hWS, hWE, hWD, hWp, hWg, hWc⟩,
    ⟨hSE, hSD, hSp, hSg, hSc⟩, ⟨hED, hEp, hEg, hEc⟩, ⟨hDp, hDg, hDc⟩, ⟨hpg, hpc⟩, hgc⟩ := hreg'
  intro x rest v S hx hs ⟨hcW, hcS, hcE, hcD, hsp0, hsg0, hcy0, htmp0⟩
  have hne : x ≠ [] := by rintro rfl; simp at hx; omega
  -- onto `tmp`
  obtain ⟨v₁, hv₁, e₁⟩ := topCopyC_exec body (c := cW) (t := sp) (src := src) (dst := tmp)
    (by simp [hWp, Ne.symm hsW, Ne.symm htW, Ne.symm hsp, Ne.symm htp, hst]) x rest v S
    (by rw [hcW, hx]) hs hsp0
  rw [hx] at e₁
  set R₁ := Function.update (Function.update S.R src rest) tmp (x.reverse ++ S.R tmp) with hR₁
  -- the sign and the carry
  set σ := x.getLast hne with hσ
  have e₂ := Exec.act (body := body) (topSignAct tmp sg cy : Act T Q A U) (mk v₁ { S with R := R₁ })
  have hR₁t : R₁ tmp = x.reverse := by simp [hR₁, htmp0]
  have hR₁g : R₁ sg = [] := by
    simp [hR₁, Function.update_of_ne (Ne.symm hsg), Function.update_of_ne (Ne.symm htg), hsg0]
  have hR₁c : R₁ cy = [] := by
    simp [hR₁, Function.update_of_ne (Ne.symm hsc), Function.update_of_ne (Ne.symm htc), hcy0]
  simp only [topSignAct, Action.run, mk_var, mk_stk, get_rt, update_rt, store_mk, hR₁t,
    List.head?_reverse, List.getLast?_eq_some_getLast hne, Option.getD_some, hR₁g, hR₁c,
    Function.update_of_ne (Ne.symm hgc)] at e₂
  set R₂ := Function.update (Function.update R₁ sg [σ]) cy [pairSym A false false] with hR₂
  -- back onto `src`
  obtain ⟨v₃, hv₃, e₃⟩ := topCopyC_exec body (c := cW) (t := sp) (src := tmp) (dst := src)
    (by simp [hWp, Ne.symm htW, Ne.symm hsW, Ne.symm htp, Ne.symm hsp, Ne.symm hst]) x.reverse []
    _ { S with R := R₂ }
    (by simp [hR₂, hR₁, Function.update_of_ne hWg, Function.update_of_ne hWc,
      Function.update_of_ne (Ne.symm hsW), Function.update_of_ne (Ne.symm htW), hcW, hx])
    (by simp [hR₂, Function.update_of_ne htg, Function.update_of_ne htc, hR₁t])
    (by simp [hR₂, hR₁, Function.update_of_ne hpg, Function.update_of_ne hpc,
      Function.update_of_ne (Ne.symm hsp), Function.update_of_ne (Ne.symm htp), hsp0])
  rw [List.length_reverse, hx, List.reverse_reverse] at e₃
  set R₃ := Function.update (Function.update R₂ tmp []) src (x ++ R₂ src) with hR₃
  have hR₃s : R₃ src = x.take s ++ ((x.drop s).take w ++ ((x.drop s).drop w ++ rest)) := by
    have e1 : x = x.take s ++ ((x.drop s).take w ++ (x.drop s).drop w) := by
      rw [List.take_append_drop, List.take_append_drop]
    simp only [hR₃, Function.update_self, hR₂, hR₁, Function.update_of_ne hsc,
      Function.update_of_ne hsg, Function.update_of_ne hst]
    conv_lhs => rw [e1]
    simp only [List.append_assoc]
  have hR₃c : R₃ cy = [pairSym A false false] := by
    simp [hR₃, hR₂, Function.update_of_ne (Ne.symm hsc), Function.update_of_ne (Ne.symm htc)]
  have hR₃g : R₃ sg = [σ] := by
    simp [hR₃, hR₂, Function.update_of_ne (Ne.symm hsg), Function.update_of_ne (Ne.symm htg),
      Function.update_of_ne hgc]
  have hR₃o : ∀ k, k ≠ src → k ≠ tmp → k ≠ sg → k ≠ cy → R₃ k = S.R k := by
    intro k h1 h2 h3 h4
    simp [hR₃, hR₂, hR₁, h1, h2, h3, h4]
  -- absorb
  obtain ⟨v₄, hu₄, e₄⟩ := scanR_exec' body hSp (regFx_topAbs hsc hsg hgc)
    (frame_topAbs (Ne.symm hsS) hSg hSc) (frame_topAbs (Ne.symm hsp) hpg hpc) v₃
    { S with R := R₃ }
    (by show R₃ sp = []; rw [hR₃o _ (Ne.symm hsp) (Ne.symm htp) hpg hpc]; exact hsp0)
  dsimp only at e₄
  have hlS : (R₃ cS).length = (x.take s).length := by
    rw [hR₃o _ (Ne.symm hsS) (Ne.symm htS) hSg hSc, hcS]; simp [hx]; omega
  rw [foldl_topAbs hA hsc hsg hgc σ (R₃ cS) (x.take s) _ R₃ false false hlS hR₃s hR₃c hR₃g] at e₄
  rw [hR₃o _ (Ne.symm hsS) (Ne.symm htS) hSg hSc, hcS] at e₄
  set cr := topAbsorb (pairRe σ) false ((x.take s).map pairRe) with hcr
  set ci := topAbsorb (pairIm σ) false ((x.take s).map pairIm) with hci
  set R₄ := Function.update (Function.update R₃ src ((x.drop s).take w ++ ((x.drop s).drop w ++
    rest))) cy [pairSym A cr ci] with hR₄
  have hR₄o : ∀ k, k ≠ src → k ≠ tmp → k ≠ sg → k ≠ cy → R₄ k = S.R k := by
    intro k h1 h2 h3 h4
    rw [hR₄, Function.update_of_ne h4, Function.update_of_ne h1, hR₃o k h1 h2 h3 h4]
  -- emit
  obtain ⟨v₅, hu₅, e₅⟩ := scanR_exec' body hEp (regFx_topEmit hsd hsc hdc)
    (frame_topEmit (Ne.symm hsE) (Ne.symm hdE) hEc) (frame_topEmit (Ne.symm hsp) (Ne.symm hdp) hpc)
    v₄ { S with R := R₄ }
    (by show R₄ sp = []; rw [hR₄o _ (Ne.symm hsp) (Ne.symm htp) hpg hpc]; exact hsp0)
  dsimp only at e₅
  have hR₄E : R₄ cE = S.R cE := hR₄o _ (Ne.symm hsE) (Ne.symm htE) hEg hEc
  have hlE : (R₄ cE).length = ((x.drop s).take w).length := by
    rw [hR₄E, hcE]; simp [hx]; omega
  rw [foldl_topEmit hA hsd hsc hdc (R₄ cE) ((x.drop s).take w) ((x.drop s).drop w ++ rest) R₄ cr ci
    hlE (by rw [hR₄, Function.update_of_ne hsc, Function.update_self])
    (by rw [hR₄, Function.update_self])] at e₅
  rw [hR₄E, hcE] at e₅
  set out := List.zipWith (pairSym A) (topEmit cr (((x.drop s).take w).map pairRe))
    (topEmit ci (((x.drop s).take w).map pairIm)) with hout
  set R₅ := Function.update (Function.update (Function.update R₄ src ((x.drop s).drop w ++ rest))
    cy [pairSym A (topEmitCar cr (((x.drop s).take w).map pairRe))
      (topEmitCar ci (((x.drop s).take w).map pairIm))]) dst (out.reverse ++ R₄ dst) with hR₅
  have hR₅o : ∀ k, k ≠ src → k ≠ dst → k ≠ tmp → k ≠ sg → k ≠ cy → R₅ k = S.R k := by
    intro k h1 h2 h3 h4 h5
    rw [hR₅, Function.update_of_ne h2, Function.update_of_ne h5, Function.update_of_ne h1,
      hR₄o k h1 h3 h4 h5]
  -- drop
  obtain ⟨v₆, hu₆, e₆⟩ := usub_exec body (a := cD) (b := src) (t := sp) (Ne.symm hsD) hDp
    hsp v₅ { S with R := R₅ }
    (by show R₅ sp = []; rw [hR₅o _ (Ne.symm hsp) (Ne.symm hdp) (Ne.symm htp) hpg hpc]
        exact hsp0)
  dsimp only at e₆
  have hR₅D : (R₅ cD).length = w' - s - w := by
    rw [hR₅o _ (Ne.symm hsD) (Ne.symm hdD) (Ne.symm htD) hDg hDc, hcD]
  have hdrop : ((x.drop s).drop w ++ rest).drop (w' - s - w) = rest := by
    have hl : ((x.drop s).drop w).length = w' - s - w := by simp [hx]; omega
    rw [← hl, List.drop_left]
  have hR₅s : R₅ src = (x.drop s).drop w ++ rest := by
    rw [hR₅, Function.update_of_ne hsd, Function.update_of_ne hsc, Function.update_self]
  rw [hR₅D, hR₅s, hdrop] at e₆
  set R₆ := Function.update R₅ src rest with hR₆
  have hR₆g : R₆ sg = [σ] := by
    rw [hR₆, Function.update_of_ne (Ne.symm hsg), hR₅, Function.update_of_ne (Ne.symm hdg),
      Function.update_of_ne hgc, Function.update_of_ne (Ne.symm hsg), hR₄,
      Function.update_of_ne hgc, Function.update_of_ne (Ne.symm hsg), hR₃g]
  have hR₆c : R₆ cy = [pairSym A (topEmitCar cr (((x.drop s).take w).map pairRe))
      (topEmitCar ci (((x.drop s).take w).map pairIm))] := by
    rw [hR₆, Function.update_of_ne (Ne.symm hsc), hR₅, Function.update_of_ne (Ne.symm hdc),
      Function.update_self]
  -- clear and flag
  have e₇ := Exec.act (body := body) (topEndAct sg cy src : Act T Q A U) (mk v₆ { S with R := R₆ })
  have hrun : (topEndAct sg cy src : Act T Q A U).run (mk v₆ { S with R := R₆ }) =
      mk { v₆ with flag := rest.head?.isSome }
        { S with R := Function.update (Function.update R₆ sg []) cy [] } := by
    have hR₆s : R₆ src = rest := by rw [hR₆, Function.update_self]
    simp [topEndAct, peekR, Action.run, update_rt, hR₆g, hR₆c, Function.update_of_ne (Ne.symm hgc),
      Function.update_of_ne hsg, Function.update_of_ne hsc, hR₆s]
  rw [hrun] at e₇
  have houtF : out = topShiftF A s w x := by
    rw [hout, hcr, hci, hσ]
    simp only [topShiftF, List.getLast?_eq_some_getLast hne, Option.getD_some]
  refine ⟨{ v₆ with flag := rest.head?.isSome }, by rw [hu₆, hu₅, hu₄, hv₃.user, hv₁.user], rfl,
    Exec.cast (Exec.seq e₁ (Exec.seq e₂ (Exec.seq e₃ (Exec.seq e₄ (Exec.seq e₅
      (Exec.seq e₆ e₇)))))) (by simp [topShiftWordCost]) ?_⟩
  congr 2
  funext k
  by_cases hk4 : k = cy
  · subst hk4
    rw [Function.update_self, Function.update_of_ne (Ne.symm hdc),
      Function.update_of_ne (Ne.symm hsc),
      hcy0]
  rw [Function.update_of_ne hk4]
  by_cases hk3 : k = sg
  · subst hk3
    rw [Function.update_self, Function.update_of_ne (Ne.symm hdg),
      Function.update_of_ne (Ne.symm hsg),
      hsg0]
  rw [Function.update_of_ne hk3]
  by_cases hk1 : k = src
  · subst hk1; rw [hR₆, Function.update_self, Function.update_of_ne hsd, Function.update_self]
  rw [hR₆, Function.update_of_ne hk1]
  by_cases hk2 : k = dst
  · subst hk2
    rw [hR₅, Function.update_self, Function.update_self, houtF,
      hR₄o _ (Ne.symm hsd) hdt hdg hdc]
  rw [Function.update_of_ne hk2, Function.update_of_ne hk1]
  by_cases hk5 : k = tmp
  · subst hk5
    rw [hR₅, Function.update_of_ne hk2, Function.update_of_ne hk4, Function.update_of_ne hk1,
      hR₄, Function.update_of_ne hk4, Function.update_of_ne hk1, hR₃, Function.update_of_ne hk1,
      Function.update_self, htmp0]
  exact hR₅o k hk1 hk2 hk5 hk3 hk4

/-- The last pair of a fitting coefficient's word holds the signs of its parts. -/
lemma topLast_coeffSyms {k : ℕ} (hk : 1 ≤ k) (z : GaussianInt) (hz : TopFitsZ k z) :
    (coeffSyms A k (red k z)).getLast?.getD blank =
      pairSym A (decide (z.re < 0)) (decide (z.im < 0)) := by
  rw [List.getLast?_eq_getElem?]
  simp only [coeffSyms, List.length_ofFn, red]
  rw [List.getElem?_ofFn]
  simp only [show k - 1 < k by omega, dite_true, Option.getD_some]
  rw [topVal_sign hk hz.1, topVal_sign hk hz.2]

/-- **The truncating shift of a word.** For a coefficient `z` fitting `w'` bits and
`s + w ≤ w'`, the shifted word of its `w'`-bit word is the `w`-bit word of `tdivZ s z`. -/
theorem topShiftF_coeffSyms (hA : 4 ≤ A) {w' s w : ℕ} (hw' : 1 ≤ w') (hsw : s + w ≤ w')
    (z : GaussianInt) (hz : TopFitsZ w' z) :
    topShiftF A s w (coeffSyms A w' (red w' z)) = coeffSyms A w (red w (tdivZ s z)) := by
  have hre : (coeffSyms A w' (red w' z)).map pairRe =
      List.ofFn fun t : Fin w' => (z.re : ZMod (2 ^ w')).val.testBit t := by
    simp [coeffSyms, red, List.map_ofFn, Function.comp_def, pairRe_pairSym hA]
  have him : (coeffSyms A w' (red w' z)).map pairIm =
      List.ofFn fun t : Fin w' => (z.im : ZMod (2 ^ w')).val.testBit t := by
    simp [coeffSyms, red, List.map_ofFn, Function.comp_def, pairIm_pairSym hA]
  simp only [topShiftF, topLast_coeffSyms hw' z hz, pairRe_pairSym hA, pairIm_pairSym hA,
    List.map_take, List.map_drop, hre, him]
  rw [topTrunc_bits hw' hsw hz.1, topTrunc_bits hw' hsw hz.2]
  apply List.ext_getElem
  · simp
  · intro t h1 h2
    simp [coeffSyms, red, tdivZ]

/-- The stream of an array as the list of its coefficient words. -/
lemma topEnc_words {R r n : ℕ} (w : ℕ) (Z : ZArr (Fin R × Fin r) n) :
    encZ A w Z = ((cellList R r n).map fun p => coeffSyms A w (red w (Z p))).flatten := by
  rw [encZ, coeffList_eq_map, List.flatMap_def, List.map_map]
  rfl

lemma topEnc_length {R r n : ℕ} (w : ℕ) (Z : ZArr (Fin R × Fin r) n) :
    (encZ A w Z).length = R * 2 ^ n * r * w := by
  rw [encZ, length_flatMap_coeffSyms, length_coeffList]

/-- **Widening.** `src` holding the `w`-bit stream of an array whose coefficients fit `w` signed
bits ends holding its `w'`-bit stream, the counters `c₁`, `c₂` holding `w`, `w' - w` symbols
and the spare `sp` empty; every other register ends as it started (`dst` empty). -/
theorem topWidenP_exec {src dst c₁ c₂ sp : Fin T} (hreg : [src, dst, c₁, c₂, sp].Nodup)
    {R r n w w' : ℕ} (hw : 1 ≤ w) (hww : w ≤ w') (Z : ZArr (Fin R × Fin r) n)
    (hZ : ∀ p, TopFitsZ w (Z p)) (v : HS T Q A U) (S : Stacks T A)
    (hs : S.R src = encZ A w Z) (hd : S.R dst = []) (hg : topWidenG c₁ c₂ sp w w' S.R) :
    ∃ v' : HS T Q A U, v'.user = v.user ∧
      Exec body (topPass src dst (topWidenWord src dst c₁ c₂ sp)) (mk v S)
        (topWidenCost R n r w w')
        (mk v' { S with R := Function.update S.R src (encZ A w' Z) }) := by
  have hreg' := hreg
  simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil,
    not_false_eq_true, and_true, List.nodup_nil] at hreg'
  obtain ⟨⟨hsd, hs1, hs2, hss⟩, ⟨hd1, hd2, hds⟩, _, _⟩ := hreg'
  have hG : TopWordFrame src dst (topWidenG c₁ c₂ sp (A := A) w w') := by
    intro R l l' ⟨h1, h2, h3⟩
    refine ⟨?_, ?_, ?_⟩ <;> simp_all [Ne.symm hs1, Ne.symm hd1,
      Ne.symm hs2, Ne.symm hd2, Ne.symm hss, Ne.symm hds]
  have hmap : ((cellList R r n).map fun p => coeffSyms A w (red w (Z p))).map (topWidenF w w') =
      (cellList R r n).map fun p => coeffSyms A w' (red w' (Z p)) := by
    rw [List.map_map]
    exact List.map_congr_left fun p _ => topWidenF_coeffSyms hw hww (Z p) (hZ p)
  obtain ⟨v', hu, he⟩ := topPass_exec body hsd hG hw (topWidenWord_spec body hreg hw (w' := w'))
    ((cellList R r n).map fun p => coeffSyms A w (red w (Z p))) v S
    (fun x hx => by
      obtain ⟨p, _, rfl⟩ := List.mem_map.1 hx
      simp) (by rw [hs, topEnc_words]) hd hg
  rw [hmap, ← topEnc_words, topEnc_length] at he
  refine ⟨v', hu, Exec.cast he ?_ rfl⟩
  simp [topWidenCost, length_cellList]

/-- The step count of the shift pass. -/
def topShiftCost (R n r w' s w : ℕ) : ℕ :=
  1 + (R * 2 ^ n * r * (topShiftWordCost w' s w + 1) + 1) + (2 * (R * 2 ^ n * r * w) + 2)

/-- **The truncating shift** (`topShift`). `src` holding the `w'`-bit stream of an array whose
coefficients fit `w'` signed bits ends holding the `w`-bit stream of `tdivZ s` applied to every
coefficient, for `s + w ≤ w'`, the counters `cW`, `cS`, `cE`, `cD` holding `w'`, `s`, `w`,
`w' - s - w` symbols and `tmp`, `sp`, `sg`, `cy` empty; every other register ends as it started
(`dst` empty). -/
theorem topShiftP_exec (hA : 4 ≤ A) {src dst tmp cW cS cE cD sp sg cy : Fin T}
    (hreg : [src, dst, tmp, cW, cS, cE, cD, sp, sg, cy].Nodup) {R r n w' s w : ℕ}
    (hw' : 1 ≤ w') (hsw : s + w ≤ w') (Z : ZArr (Fin R × Fin r) n)
    (hZ : ∀ p, TopFitsZ w' (Z p)) (v : HS T Q A U) (S : Stacks T A)
    (hs : S.R src = encZ A w' Z) (hd : S.R dst = [])
    (hg : topShiftG tmp cW cS cE cD sp sg cy w' s w S.R) :
    ∃ v' : HS T Q A U, v'.user = v.user ∧
      Exec body (topPass src dst (topShiftWord src dst tmp cW cS cE cD sp sg cy)) (mk v S)
        (topShiftCost R n r w' s w)
        (mk v' { S with R := Function.update S.R src (encZ A w (fun p => tdivZ s (Z p))) }) := by
  have hreg' := hreg
  simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil,
    not_false_eq_true, and_true, List.nodup_nil] at hreg'
  obtain ⟨⟨hsd, hst, hsW, hsS, hsE, hsD, hsp, hsg, hsc⟩, ⟨hdt, hdW, hdS, hdE, hdD, hdp, hdg, hdc⟩,
    -, -, -, -, -, -, -⟩ := hreg'
  have hG : TopWordFrame src dst (topShiftG tmp cW cS cE cD sp sg cy (A := A) w' s w) := by
    intro R l l' ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp_all [Ne.symm hst, Ne.symm hsW, Ne.symm hsS, Ne.symm hsE,
        Ne.symm hsD, Ne.symm hsp, Ne.symm hsg, Ne.symm hsc, Ne.symm hdt, Ne.symm hdW,
        Ne.symm hdS, Ne.symm hdE, Ne.symm hdD, Ne.symm hdp, Ne.symm hdg, Ne.symm hdc]
  have hmap : ((cellList R r n).map fun p => coeffSyms A w' (red w' (Z p))).map
      (topShiftF A s w) = (cellList R r n).map fun p => coeffSyms A w (red w (tdivZ s (Z p))) := by
    rw [List.map_map]
    exact List.map_congr_left fun p _ => topShiftF_coeffSyms hA hw' hsw (Z p) (hZ p)
  obtain ⟨v', hu, he⟩ := topPass_exec body hsd hG hw' (topShiftWord_spec body hA hreg hw' hsw)
    ((cellList R r n).map fun p => coeffSyms A w' (red w' (Z p))) v S
    (fun x hx => by
      obtain ⟨p, _, rfl⟩ := List.mem_map.1 hx
      simp) (by rw [hs, topEnc_words]) hd hg
  rw [hmap, ← topEnc_words (Z := fun p => tdivZ s (Z p)), topEnc_length] at he
  refine ⟨v', hu, Exec.cast he ?_ rfl⟩
  simp [topShiftCost, length_cellList]

end IntegerMultBounds.MathlibTM2.Node
