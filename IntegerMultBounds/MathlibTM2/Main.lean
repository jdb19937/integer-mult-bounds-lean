module

public import IntegerMultBounds.MathlibTM2.Correct
public import IntegerMultBounds.MathlibTM2.Asymptotics
public import IntegerMultBounds.MathlibTM2.Statement
public import IntegerMultBounds.Machine.ElementaryMultiply

/-!
# From multitape programs to Mathlib's `TM2ComputableInTime`

`tm2_of_runsWithin` turns a multitape multiplication program with a cost bound at every length
into a Mathlib `TM2ComputableInTime` machine for `fun p : ℕ × ℕ => p.1 * p.2` under Mathlib's
encodings, whose time is `bridgeTime` of that cost bound. `mulInTime_of_computesWithin` and
`statement_of_endToEnd` then carry the vendored `EndToEnd` target over to `MathlibTM2.Statement`.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2

open IntegerMultBounds.Machine IntegerMultBounds.Assembly IntegerMultBounds.MathlibTM2.Stack
open Computability Turing
open Asymptotics Filter

variable {t q a : ℕ}


lemma tapeStacks_R (M : Program t q a) (w : List (Fin (a + 4))) :
    (tapeStacks M w : Stacks t a).R = fun i => if i.val = 0 then w else [] := by
  funext i
  simp only [tapeStacks]
  congr 1
  simp [tape0, Fin.ext_iff]

/-- The bridge program run on `(A, B)`, given a halting run of the multitape program on the
padded inputs with a correct output. -/
theorem main_exec (M : Program t q a) (A B k : ℕ) (cf : Config t q a)
    (hrun : run M k (input M (msbWord (padLen A B) A) (msbWord (padLen A B) B)) = some cf)
    (hstep : step M cf = none)
    (hout : outputCorrect M (padLen A B) (msbWord (padLen A B) A) (msbWord (padLen A B) B) cf) :
    ∃ m, m ≤ (34 * t + 100) * ((encodeNat A).length + (encodeNat B).length + 1) +
        (13 * t + 5) * k ∧
      Exec (fun _ => main M) (main M)
        (mk (init M) (inputStacks ((encodingProd encodingNatBool encodingNatBool).encode (A, B)))) m
        (mk (init M) (outputStacks (encodeNat (A * B)))) := by
  set body : Unit → Pr t q a := fun _ => main M
  set n := padLen A B
  set x := msbWord n A
  set y := msbWord n B
  set w : List (Fin (a + 4)) := x.map bitSymbol ++ [separator] ++ y.map bitSymbol
  -- prepare
  obtain ⟨v₁, m₁, k₁, hm₁, e₁⟩ := prepare_exec body M A B (init M)
  -- simulate
  have hrep₀ : Rep (input M x y) (tapeStacks M w : Stacks t a).L (tapeStacks M w : Stacks t a).R := by
    rw [tapeStacks_R]
    exact rep_input M x y
  obtain ⟨v₂, S₂, e₂, hrep, hl₂, hi₂, ho₂, hb0, hb1, hb2, hb3, hsz⟩ :=
    sim_loop body M k (input M x y) { v₁ with flag := true } (tapeStacks M w) hrep₀
      (by simpa [IntegerMultBounds.Machine.input, init] using k₁.2) rfl cf hrun hstep
  have hsim : Exec body (simLoop M) (mk v₁ (tapeStacks M w)) (1 + (k * (t + 5) + 5)) (mk v₂ S₂) :=
    Exec.seq (Exec.act (body := body) (.load (fun v => { v with flag := true }) .done)
      (mk v₁ (tapeStacks M w))) e₂
  -- finish
  obtain ⟨out, hlen, hval, htape⟩ := hout
  have hn1 : 1 ≤ n := le_max_right _ _
  have hne : out ≠ [] := by
    intro h; rw [h] at hlen; simp at hlen; omega
  have hlw : w.length = 2 * n + 1 := by
    have hx : x.length = n := by
      simp only [x, msbWord, List.length_reverse]
      exact length_padTo (le_trans (le_max_left _ _) (le_max_left _ _))
    have hy : y.length = n := by
      simp only [y, msbWord, List.length_reverse]
      exact length_padTo (le_trans (le_max_right _ _) (le_max_left _ _))
    simp [w, hx, hy]; ring
  have hZ : ∀ i, (S₂.L i).length + (S₂.R i).length ≤ 2 * n + 1 + 2 * k := by
    intro i
    have := hsz i
    have h₀ : ((tapeStacks M w : Stacks t a).L i).length + ((tapeStacks M w : Stacks t a).R i).length
        ≤ 2 * n + 1 := by
      simp only [tapeStacks]; split_ifs <;> simp [hlw]
    omega
  obtain ⟨m₃, hm₃, e₃⟩ := finish_exec body M v₂ S₂ cf out
    (by rw [hl₂]; exact k₁.1.trans rfl) hrep
    ⟨by rw [hi₂]; rfl, by rw [ho₂]; rfl, by rw [hb0]; rfl, by rw [hb1]; rfl, by rw [hb2]; rfl,
      by rw [hb3]; rfl⟩ hne htape (2 * n + 1 + 2 * k) hZ
  rw [hval, binaryValue_msbWord, binaryValue_msbWord] at e₃
  refine ⟨_, ?_, Exec.seq e₁ (Exec.seq hsim e₃)⟩
  -- cost
  have hnN : n ≤ (encodeNat A).length + (encodeNat B).length + 1 := by
    simp only [n, padLen]; omega
  set N := (encodeNat A).length + (encodeNat B).length
  have h1 : 6 * t * (2 * n + 1 + 2 * k) = 12 * (t * n) + 6 * t + 12 * (t * k) := by ring
  have h2 : k * (t + 5) = t * k + 5 * k := by ring
  have h3 : (34 * t + 100) * (N + 1) = 34 * (t * N) + 34 * t + 100 * N + 100 := by ring
  have h4 : (13 * t + 5) * k = 13 * (t * k) + 5 * k := by ring
  have h5 : t * n ≤ t * N + t := by
    have := Nat.mul_le_mul_left t hnN; rw [Nat.mul_add, Nat.mul_one] at this; exact this
  omega

/-- The Mathlib machine of the bridge program. -/
def tm (M : Program t q a) : FinTM2 :=
  Stack.machine (fun _ : Unit => main M) () .inp .out (init M)

/-- A multitape multiplier with a cost bound at every length gives a Mathlib `TM2` multiplier
whose time is `bridgeTime` of that bound. -/
theorem tm2_of_runsWithin (M : Program t q a) (total : ℕ → ℝ) (h : RunsWithin M total) :
    ∃ T : TM2ComputableInTime MathlibTM2.pairEnc encodingNatBool.encode
        (fun p : ℕ × ℕ => p.1 * p.2),
      T.time = bridgeTime (34 * t + 102) (13 * t + 5) total := by
  have hrun : ∀ p : ℕ × ℕ, ∃ m, m + 2 ≤ bridgeTime (34 * t + 102) (13 * t + 5) total
      (MathlibTM2.pairEnc p).length ∧
      Exec (fun _ => main M) (main M)
        (Store.only (init M) .inp (MathlibTM2.pairEnc p))  m
        (Store.only (init M) .out (encodeNat (p.1 * p.2))) := by
    rintro ⟨A, B⟩
    set n := padLen A B
    have hn1 : 1 ≤ n := le_max_right _ _
    have hx : (msbWord n A).length = n := by
      simp only [msbWord, List.length_reverse]
      exact length_padTo (le_trans (le_max_left _ _) (le_max_left _ _))
    have hy : (msbWord n B).length = n := by
      simp only [msbWord, List.length_reverse]
      exact length_padTo (le_trans (le_max_right _ _) (le_max_left _ _))
    obtain ⟨k, c, hk, hs, ho, hkt⟩ := h n hn1 _ _ hx hy
    obtain ⟨m, hm, e⟩ := main_exec M A B k c hk hs ho
    have hin : Store.only (init M) (BK.inp (t := t)) (MathlibTM2.pairEnc (A, B)) =
        mk (init M) (inputStacks ((encodingProd encodingNatBool encodingNatBool).encode (A, B))) := by
      simp only [Store.only, mk]
      congr 1
      funext k'
      rcases k' with _ | _ | j | _ | _ <;> (try fin_cases j) <;> simp [inputStacks, Stacks.get]
    have hout : Store.only (init M) (BK.out (t := t)) (encodeNat (A * B)) =
        mk (init M) (outputStacks (encodeNat (A * B))) := by
      simp only [Store.only, mk]
      congr 1
      funext k'
      rcases k' with _ | _ | j | _ | _ <;> (try fin_cases j) <;> simp [outputStacks, Stacks.get]
    refine ⟨m, ?_, hin ▸ hout ▸ e⟩
    -- the length of the encoded input
    have hlen : (MathlibTM2.pairEnc (A, B)).length =
        (encodeNat A).length + (encodeNat B).length := by
      simp [MathlibTM2.pairEnc, encodingProd, encodingNatBool]
    have hnN : n ≤ (MathlibTM2.pairEnc (A, B)).length + 1 := by
      rw [hlen]; simp only [n, padLen]; omega
    have hkc : k ≤ ⌈total n⌉₊ := Nat.cast_le.1 (hkt.trans (Nat.le_ceil (total n)))
    have hsup := le_bridgeTime_sup (34 * t + 102) (13 * t + 5) total hnN
    have := Nat.mul_le_mul_left (13 * t + 5) (hkc.trans hsup)
    simp only [bridgeTime]
    rw [← hlen] at hm
    have : (34 * t + 102) * ((MathlibTM2.pairEnc (A, B)).length + 1) =
        (34 * t + 100) * ((MathlibTM2.pairEnc (A, B)).length + 1) +
          2 * ((MathlibTM2.pairEnc (A, B)).length + 1) := by ring
    omega
  refine ⟨{ tm := tm M
            inputAlphabet := Equiv.refl _
            outputAlphabet := Equiv.refl _
            time := bridgeTime (34 * t + 102) (13 * t + 5) total
            outputsFun := fun p => ?_ }, rfl⟩
  have e := Classical.choose_spec (hrun p)
  have o := Exec.toOutputs (body := fun _ : Unit => main M) () (BK.inp (t := t)) (BK.out (t := t))
    (init M) e.2 e.1
  simp only [Equiv.refl]
  erw [List.map_id, List.map_id]
  exact o

/-- A multitape program meeting the vendored `ComputesWithin` contract gives `MulInTime`. -/
theorem mulInTime_of_computesWithin (M : Program t q a) {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    (h : ComputesWithin M κ) : MathlibTM2.MulInTime κ := by
  obtain ⟨total, C, n₀, hrw, hC⟩ := runsWithin_of_computesWithin h
  obtain ⟨T, hT⟩ := tm2_of_runsWithin M total hrw
  exact ⟨T, by rw [hT]; exact isBigO_bridgeTime _ _ total hκ hκ1 hC⟩

/-- The vendored end-to-end target implies the Mathlib-only statement. -/
theorem statement_of_endToEnd (h : EndToEnd) : MathlibTM2.Statement := by
  obtain ⟨t, q, a, M, hM⟩ := h
  exact ⟨83 / 10 ^ 12, by norm_num, mulInTime_of_computesWithin M (by norm_num) (by norm_num) hM⟩

/-- An unconditional instance of the bridge: the vendored elementary multiplier gives a Mathlib
`TM2` multiplier in quadratic time. -/
theorem mul_quadratic :
    ∃ T : TM2ComputableInTime MathlibTM2.pairEnc encodingNatBool.encode
        (fun p : ℕ × ℕ => p.1 * p.2),
      (fun n : ℕ => (T.time n : ℝ)) =O[atTop] fun n : ℕ => (n : ℝ) ^ 2 := by
  obtain ⟨T, hT⟩ := tm2_of_runsWithin (ElementaryMultiply.program 0) _
    (ElementaryMultiply.runsWithin (a := 0))
  exact ⟨T, by rw [hT]; exact isBigO_bridgeTime_sq _ _⟩

end IntegerMultBounds.MathlibTM2
