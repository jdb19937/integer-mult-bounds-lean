module

public import IntegerMultBounds.Schoenhage.RingHeader
public import IntegerMultBounds.Schoenhage.SigmaConstsTape

/-! The §6 transform parameters read off the transform header on tapes. The
header `Γ(p)Γ(d)Γ(r)Γ(K)Γ(w)Γ(t₁)…Γ(t_D)` is decoded code by code: `p`, `ℓ =
log₂ r`, `K`, `w` and `D = d - 1` as unary registers, and for every axis
length `tᵢ = 2^aᵢ` the flag `ℓ < size tᵢ`, i.e. whether the axis is long, read
from the code's length alone (`runs_decodeParams`). On admissible axis
lengths these are the paper's flags (`flags_paper`). -/

@[expose] public section

set_option maxRecDepth 10000

namespace IntegerMultBounds.Schoenhage

open Machine Strm Tp Schedule Spec.SignedRingProduct TwistDescriptors

namespace TransformParams

/-- One axis length: its code's bit length decides whether the axis is long. -/
noncomputable def flagStep : Cmd 0 𝕌 :=
  .seq codeA <| .seq (op1 geq false (ι sX) iL xA (by decide) (by decide) (by decide)) <|
  .seq (clear (ι sX)) <| .seq (clear (ι tO2)) <| .seq (rewind iL) (skp xB (ι tJ) (by decide))

/-- Lower the register `kN` by one. -/
noncomputable def decN : Cmd 0 𝕌 :=
  .seq (op1 Rules.drop false kN (ι c1) xC (by decide) (by decide) (by decide)) <| .seq (rewind (ι c1)) <|
  .seq (clear kN) <| .seq (rewind xC) <| .seq (cpy xC kN (by decide)) <| .seq (clear xC) (rewind kN)

/-- Decode the header into `p`, `ℓ`, `w`, `K`, `D` and the long-axis flags. -/
noncomputable def decodeParams : Cmd 0 𝕌 :=
  .seq hdrInit <|
  .seq decodeOne <| .seq (regMove (ι tL) iP (by decide)) <|
  .seq decodeOne <| .seq (regMove (ι tL) kN (by decide)) <|
  .seq decodeOne <| .seq logOf <|
  .seq decodeOne <| .seq (regMove (ι tL) kI (by decide)) <|
  .seq decodeOne <| .seq (regMove (ι tL) iW (by decide)) <|
  .seq decN <| .seq (.seq (op0 Rules.ticks false kN xB (by decide)) (.seq (rewind kN) (rewind xB))) <|
  .seq (.loop xB flagStep) <| .seq (clear (ι tX)) (clear (ι c1))

/-- The flag of an axis length: `ℓ < size t`. -/
def lengthFlags (ℓ : ℕ) (ts : List ℕ) : List Bool := ts.map fun t => decide (ℓ < Nat.size t)

set_option maxHeartbeats 8000000 in
theorem runs_flagStep {ℓ t : ℕ} (ht : 1 ≤ t) {rest : List Bool} (τ : Fin 𝕌 → WTape)
    (h1 : τ (ι c1) = reg [true]) (hX : τ (ι tX) = reg (gamma t ++ rest)) (hY : τ (ι tY) = emp)
    (hS : τ (ι sX) = emp) (hD : τ (ι tD) = emp) (hO : τ (ι tO2) = emp) (hL : τ iL = reg (ones ℓ))
    {O : List (List Bool)} (hA : τ xA = ⟨O, []⟩) {LB RB : List (List Bool)} (hB : τ xB = ⟨LB, [] :: RB⟩)
    (hJ : τ (ι tJ) = emp) :
    Runs flagStep τ (· = Function.update (Function.update (Function.update τ (ι tX) (reg rest))
        xA ⟨[decide (ℓ < Nat.size t)] :: O, []⟩) xB ⟨[] :: LB, RB⟩)
      (40 * (gamma t ++ rest).length + 8 * Nat.size t + 4 * ℓ + 400) := by
  have s1 := runs_codeA ht τ h1 hX hY hS hD hO
  set τ₁ := Function.update (Function.update (Function.update τ (ι tX) (reg rest))
    (ι sX) (reg (ones (Nat.size t)))) (ι tO2) (reg (msbBits (Nat.size t) t)) with hτ₁
  have t1 : time geq (ones (Nat.size t)) (fun _ => ones ℓ) ≤ Nat.size t + ℓ + 7 :=
    (time_le geq (ones (Nat.size t)) (fun _ => ones ℓ) ℓ (fun _ => by simp)).trans (by simp)
  have s2 : Runs (.seq (op1 (a := 0) geq false (ι sX) iL xA (by decide) (by decide) (by decide)) <|
      .seq (clear (ι sX)) <| .seq (clear (ι tO2)) <| .seq (rewind iL) (skp xB (ι tJ) (by decide))) τ₁
      (· = Function.update (Function.update (Function.update (Function.update (Function.update τ₁ (ι sX) emp)
        (ι tO2) emp) xA ⟨[decide (ℓ < Nat.size t)] :: O, []⟩) iL (reg (ones ℓ))) xB ⟨[] :: LB, RB⟩)
      (4 * Nat.size t + 4 * ℓ + 4 * (msbBits (Nat.size t) t).length + 60) := by
    apply Runs.of_wp
    simp only [skp, WP, wp_op0, wp_op1, wp_rewind, wp_clear]
    tsimp [hτ₁, hL, hA, hB, hJ, emp, reg, output_geq, Rules.output_skip]
    refine ⟨?_, ?_⟩
    · funext i
      simp only [Function.update_apply]
      split_ifs <;> (try subst_vars) <;> (try tsimp [hL, hA, hB, hJ, emp, reg]) <;> tsimp at *
    · simp [time_skip, clen, WTape.words] at t1 ⊢; omega
  refine (Runs.then s1 s2).mono (fun τ' e => ?_) ?_
  · rw [e]; funext y
    by_cases hm : y ∈ [ι tX, xA, xB, ι sX, ι tO2, iL]
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl | rfl | rfl | rfl | rfl <;> tsimp [hτ₁, hS, hO, hL, emp]
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hm
      obtain ⟨n1, n2, n3, n4, n5, n6⟩ := hm
      simp only [hτ₁, Function.update_apply, n1, n2, n3, n4, n5, n6, ite_false]
  · have hm : (msbBits (Nat.size t) t).length = Nat.size t := by simp
    omega

set_option maxHeartbeats 8000000 in
theorem runs_flagLoop {ℓ H : ℕ} : ∀ (ts : List ℕ) (τ : Fin 𝕌 → WTape) (O LB : List (List Bool)),
    (∀ t ∈ ts, 1 ≤ t) → (ts.flatMap gamma).length ≤ H → τ (ι c1) = reg [true] →
    τ (ι tX) = reg (ts.flatMap gamma) → τ (ι tY) = emp → τ (ι sX) = emp → τ (ι tD) = emp →
    τ (ι tO2) = emp → τ iL = reg (ones ℓ) → τ xA = ⟨O, []⟩ → τ xB = ⟨LB, List.replicate ts.length []⟩ →
    τ (ι tJ) = emp →
    Runs (.loop xB flagStep) τ (· = Function.update (Function.update (Function.update τ (ι tX) (reg []))
        xA ⟨((lengthFlags ℓ ts).map fun b => [b]).reverse ++ O, []⟩) xB ⟨List.replicate ts.length [] ++ LB, []⟩)
      (ts.length * (48 * H + 4 * ℓ + 402))
  | [], τ, O, LB, _, _, h1, hX, hY, hS, hD, hO, hL, hA, hB, hJ => by
    refine (Runs.loop_done (by simp [hB]) rfl).mono (fun τ' e => ?_) (by simp)
    subst e
    funext y
    by_cases hm : y ∈ [ι tX, xA, xB]
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl | rfl <;> tsimp [hX, hA, hB, lengthFlags]
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hm
      obtain ⟨n1, n2, n3⟩ := hm
      simp only [Function.update_apply, n1, n2, n3, ite_false]
  | t :: ts, τ, O, LB, hts, hH, h1, hX, hY, hS, hD, hO, hL, hA, hB, hJ => by
    have ht := hts t (by simp)
    have s1 := runs_flagStep (ℓ := ℓ) ht (rest := ts.flatMap gamma) τ h1 (by rw [hX]; simp) hY hS hD hO hL hA
      (show τ xB = ⟨LB, [] :: List.replicate ts.length []⟩ by rw [hB]; rfl) hJ
    set τ₁ := Function.update (Function.update (Function.update τ (ι tX) (reg (ts.flatMap gamma)))
      xA ⟨[decide (ℓ < Nat.size t)] :: O, []⟩) xB ⟨[] :: LB, List.replicate ts.length []⟩ with hτ₁
    have hH' : (ts.flatMap gamma).length ≤ H := by
      have : (ts.flatMap gamma).length ≤ ((t :: ts).flatMap gamma).length := by simp
      omega
    have ih := runs_flagLoop (ℓ := ℓ) (H := H) ts τ₁ ([decide (ℓ < Nat.size t)] :: O) ([] :: LB)
      (fun u hu => hts u (by simp [hu])) hH' (by tsimp [hτ₁, h1]) (by tsimp [hτ₁]) (by tsimp [hτ₁, hY])
      (by tsimp [hτ₁, hS]) (by tsimp [hτ₁, hD]) (by tsimp [hτ₁, hO]) (by tsimp [hτ₁, hL]) (by tsimp [hτ₁])
      (by tsimp [hτ₁]) (by tsimp [hτ₁, hJ])
    refine (Runs.loop_step (by simp [hB]) (s1.mono (fun τ' h => by rw [h]; exact ih) le_rfl)).mono
      (fun τ' h => ?_) ?_
    · rw [h]
      funext y
      by_cases hm : y ∈ [ι tX, xA, xB]
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
        rcases hm with rfl | rfl | rfl <;> tsimp [hτ₁, lengthFlags, SigmaRowsTape.replicate_cons]
      · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hm
        obtain ⟨n1, n2, n3⟩ := hm
        simp only [hτ₁, Function.update_apply, n1, n2, n3, ite_false]
    · have hlen : (gamma t ++ ts.flatMap gamma).length ≤ H := by simpa using hH
      have hsz : Nat.size t ≤ H := by
        have := length_gamma ht
        have : (gamma t).length ≤ (gamma t ++ ts.flatMap gamma).length := by simp
        omega
      simp only [List.length_cons]
      nlinarith

set_option maxHeartbeats 8000000 in
theorem runs_decN {d : ℕ} (τ : Fin 𝕌 → WTape) (hN : τ kN = reg (ones d)) (h1 : τ (ι c1) = reg [true])
    (hC : τ xC = emp) :
    Runs decN τ (· = Function.update τ kN (reg (ones (d - 1)))) (10 * d + 60) := by
  have t1 : time Rules.drop (ones d) (fun _ => [true]) ≤ d + 1 + 6 :=
    (time_le Rules.drop (ones d) (fun _ => [true]) 1 (fun _ => by simp)).trans (by simp)
  apply Runs.of_wp
  simp only [decN, cpy, WP, wp_op0, wp_op1, wp_rewind, wp_clear]
  tsimp [hN, h1, hC, emp, reg, Rules.output_drop, Rules.output_copy, ones, List.drop_replicate]
  refine ⟨?_, ?_⟩
  · funext y
    simp only [Function.update_apply]
    split_ifs <;> (try subst_vars) <;> (try tsimp [hN, h1, hC, emp, reg, ones])
  · simp [time_copy, clen, ones, WTape.words] at t1 ⊢; omega

/-- A bound on decoding the parameters. -/
def paramsCost (p d r K w H D l : ℕ) : ℕ :=
  6 * (50 * H + 600) + 42 * (Nat.size p * (Nat.size p + p + 10) + Nat.size d * (Nat.size d + d + 10) +
    Nat.size r * (Nat.size r + r + 10) + Nat.size K * (Nat.size K + K + 10) +
    Nat.size w * (Nat.size w + w + 10)) + 200 * r + 20 * (p + w + H + d + K) + 2500 +
    D * (48 * H + 4 * l + 402)

set_option maxHeartbeats 32000000 in
/-- `runs_decodeParams`: from the transform header the program leaves `p`, `ℓ`, `w`, `K` and `D = d - 1`
in unary and the long-axis flags `ℓ < size tᵢ` on `xA`. -/
theorem runs_decodeParams {p d l K w : ℕ} {ts : List ℕ} (hp : 1 ≤ p) (hd : 1 ≤ d) (hK : 1 ≤ K) (hw : 1 ≤ w)
    (hts : ∀ t ∈ ts, 1 ≤ t) (hD : ts.length = d - 1) (τ : Fin 𝕌 → WTape) (hc : Clean τ)
    (hH : τ zH = reg (transformHeader p d (2 ^ l) K w ts))
    (hP : τ iP = emp) (hL : τ iL = emp) (hW : τ iW = emp) (hKI : τ kI = emp) (hN : τ kN = emp)
    (hA : τ xA = emp) (hB : τ xB = emp) (hC : τ xC = emp) :
    Runs decodeParams τ (· = Function.update (Function.update (Function.update (Function.update (Function.update
        (Function.update (Function.update τ iP (reg (ones p))) kN (reg (ones (d - 1)))) iL (reg (ones l)))
        kI (reg (ones K))) iW (reg (ones w))) xB ⟨List.replicate ts.length [] ++ [], []⟩)
        xA ⟨((lengthFlags l ts).map fun b => [b]).reverse, []⟩)
      (paramsCost p d (2 ^ l) K w (transformHeader p d (2 ^ l) K w ts).length ts.length l) := by
  have hz : ∀ i : Fin 𝕋, τ (ι i) = emp := fun i => congrFun hc i
  set hdr := transformHeader p d (2 ^ l) K w ts
  set tsc := ts.flatMap gamma
  set R4 := gamma w ++ tsc
  set R3 := gamma K ++ R4
  set R2 := gamma (2 ^ l) ++ R3
  set R1 := gamma d ++ R2
  have eh : hdr = gamma p ++ R1 := by simp [hdr, transformHeader, tsc, R1, R2, R3, R4]
  set H := hdr.length
  have s0 : Runs hdrInit τ (· = Function.update (Function.update τ (ι c1) (reg [true])) (ι tX) (reg hdr))
      (3 * H + 30) := by
    apply Runs.of_wp
    simp only [hdrInit, regDup, regIn, cpy, WP, wp_op0, wp_rewind, wp_emit]
    tsimp [hz, hH, emp, reg, Rules.output_copy]
    refine ⟨?_, ?_⟩
    · funext y
      simp only [Function.update_apply]
      split_ifs <;> (try subst_vars) <;> (try tsimp [hz, hH, reg, emp]); tsimp at *
    · simp [time_copy]; omega
  set τ₀ := Function.update (Function.update τ (ι c1) (reg [true])) (ι tX) (reg hdr)
  -- p
  have s1 := runs_decodeOne hp (rest := R1) τ₀ (by tsimp [τ₀]) (by tsimp [τ₀, eh])
    (by tsimp [τ₀, hz]) (by tsimp [τ₀, hz]) (by tsimp [τ₀, hz]) (by tsimp [τ₀, hz]) (by tsimp [τ₀, hz])
    (by tsimp [τ₀, hz]) (by tsimp [τ₀, hz]) (by tsimp [τ₀, hz]) (by tsimp [τ₀, hz]) (by tsimp [τ₀, hz])
  set τ₁ := Function.update (Function.update τ₀ (ι tX) (reg R1)) (ι tL) (reg (ones p))
  have s2 := runs_regMove (a := 0) (show ι tL ≠ iP by decide) τ₁ (w := ones p) (by tsimp [τ₁])
    (by tsimp [τ₁, τ₀, hP])
  set τ₂ := Function.update (Function.update τ₁ (ι tL) emp) iP (reg (ones p))
  -- d
  have s3 := runs_decodeOne hd (rest := R2) τ₂ (by tsimp [τ₂, τ₁, τ₀]) (by tsimp [τ₂, τ₁, R1])
    (by tsimp [τ₂, τ₁, τ₀, hz]) (by tsimp [τ₂, τ₁, τ₀, hz]) (by tsimp [τ₂, τ₁, τ₀, hz]) (by tsimp [τ₂, τ₁, τ₀, hz])
    (by tsimp [τ₂, τ₁, τ₀, hz]) (by tsimp [τ₂, τ₁, τ₀, hz]) (by tsimp [τ₂, τ₁, τ₀, hz]) (by tsimp [τ₂, τ₁, τ₀, hz])
    (by tsimp [τ₂, τ₁, τ₀, hz]) (by tsimp [τ₂, τ₁, τ₀, hz])
  set τ₃ := Function.update (Function.update τ₂ (ι tX) (reg R2)) (ι tL) (reg (ones d))
  have s4 := runs_regMove (a := 0) (show ι tL ≠ kN by decide) τ₃ (w := ones d) (by tsimp [τ₃])
    (by tsimp [τ₃, τ₂, τ₁, τ₀, hN])
  set τ₄ := Function.update (Function.update τ₃ (ι tL) emp) kN (reg (ones d))
  -- r
  have s5 := runs_decodeOne (Nat.one_le_two_pow (n := l)) (rest := R3) τ₄ (by tsimp [τ₄, τ₃, τ₂, τ₁, τ₀])
    (by tsimp [τ₄, τ₃, R2])
    (by tsimp [τ₄, τ₃, τ₂, τ₁, τ₀, hz]) (by tsimp [τ₄, τ₃, τ₂, τ₁, τ₀, hz]) (by tsimp [τ₄, τ₃, τ₂, τ₁, τ₀, hz])
    (by tsimp [τ₄, τ₃, τ₂, τ₁, τ₀, hz]) (by tsimp [τ₄, τ₃, τ₂, τ₁, τ₀, hz]) (by tsimp [τ₄, τ₃, τ₂, τ₁, τ₀, hz])
    (by tsimp [τ₄, τ₃, τ₂, τ₁, τ₀, hz]) (by tsimp [τ₄, τ₃, τ₂, τ₁, τ₀, hz]) (by tsimp [τ₄, τ₃, τ₂, τ₁, τ₀, hz])
    (by tsimp [τ₄, τ₃, τ₂, τ₁, τ₀, hz])
  set τ₅ := Function.update (Function.update τ₄ (ι tX) (reg R3)) (ι tL) (reg (ones (2 ^ l)))
  have s6 := runs_logOf (r := 2 ^ l) τ₅ (by tsimp [τ₅]) (by tsimp [τ₅, τ₄, τ₃, τ₂, τ₁, τ₀, hz])
    (by tsimp [τ₅, τ₄, τ₃, τ₂, τ₁, τ₀, hz]) (by tsimp [τ₅, τ₄, τ₃, τ₂, τ₁, τ₀, hz])
    (by tsimp [τ₅, τ₄, τ₃, τ₂, τ₁, τ₀]) (by tsimp [τ₅, τ₄, τ₃, τ₂, τ₁, τ₀, hz])
    (by tsimp [τ₅, τ₄, τ₃, τ₂, τ₁, τ₀, hz]) (by tsimp [τ₅, τ₄, τ₃, τ₂, τ₁, τ₀, hL])
  rw [Nat.size_pow, Nat.add_sub_cancel] at s6
  set τ₆ := Function.update (Function.update τ₅ (ι tL) emp) iL (reg (ones l))
  -- K
  have s7 := runs_decodeOne hK (rest := R4) τ₆ (by tsimp [τ₆, τ₅, τ₄, τ₃, τ₂, τ₁, τ₀]) (by tsimp [τ₆, τ₅, R3])
    (by tsimp [τ₆, τ₅, τ₄, τ₃, τ₂, τ₁, τ₀, hz]) (by tsimp [τ₆, τ₅, τ₄, τ₃, τ₂, τ₁, τ₀, hz])
    (by tsimp [τ₆, τ₅, τ₄, τ₃, τ₂, τ₁, τ₀, hz]) (by tsimp [τ₆, τ₅, τ₄, τ₃, τ₂, τ₁, τ₀, hz])
    (by tsimp [τ₆, τ₅, τ₄, τ₃, τ₂, τ₁, τ₀, hz]) (by tsimp [τ₆, τ₅, τ₄, τ₃, τ₂, τ₁, τ₀, hz])
    (by tsimp [τ₆, τ₅, τ₄, τ₃, τ₂, τ₁, τ₀, hz]) (by tsimp [τ₆, τ₅, τ₄, τ₃, τ₂, τ₁, τ₀, hz])
    (by tsimp [τ₆, τ₅, τ₄, τ₃, τ₂, τ₁, τ₀, hz]) (by tsimp [τ₆, τ₅, τ₄, τ₃, τ₂, τ₁, τ₀, hz])
  set τ₇ := Function.update (Function.update τ₆ (ι tX) (reg R4)) (ι tL) (reg (ones K))
  have s8 := runs_regMove (a := 0) (show ι tL ≠ kI by decide) τ₇ (w := ones K) (by tsimp [τ₇])
    (by tsimp [τ₇, τ₆, τ₅, τ₄, τ₃, τ₂, τ₁, τ₀, hKI])
  set τ₈ := Function.update (Function.update τ₇ (ι tL) emp) kI (reg (ones K))
  -- w
  have s9 := runs_decodeOne hw (rest := tsc) τ₈ (by tsimp [τ₈, τ₇, τ₆, τ₅, τ₄, τ₃, τ₂, τ₁, τ₀])
    (by tsimp [τ₈, τ₇, R4])
    (by tsimp [τ₈, τ₇, τ₆, τ₅, τ₄, τ₃, τ₂, τ₁, τ₀, hz]) (by tsimp [τ₈, τ₇, τ₆, τ₅, τ₄, τ₃, τ₂, τ₁, τ₀, hz])
    (by tsimp [τ₈, τ₇, τ₆, τ₅, τ₄, τ₃, τ₂, τ₁, τ₀, hz]) (by tsimp [τ₈, τ₇, τ₆, τ₅, τ₄, τ₃, τ₂, τ₁, τ₀, hz])
    (by tsimp [τ₈, τ₇, τ₆, τ₅, τ₄, τ₃, τ₂, τ₁, τ₀, hz]) (by tsimp [τ₈, τ₇, τ₆, τ₅, τ₄, τ₃, τ₂, τ₁, τ₀, hz])
    (by tsimp [τ₈, τ₇, τ₆, τ₅, τ₄, τ₃, τ₂, τ₁, τ₀, hz]) (by tsimp [τ₈, τ₇, τ₆, τ₅, τ₄, τ₃, τ₂, τ₁, τ₀, hz])
    (by tsimp [τ₈, τ₇, τ₆, τ₅, τ₄, τ₃, τ₂, τ₁, τ₀, hz]) (by tsimp [τ₈, τ₇, τ₆, τ₅, τ₄, τ₃, τ₂, τ₁, τ₀, hz])
  set τ₉ := Function.update (Function.update τ₈ (ι tX) (reg tsc)) (ι tL) (reg (ones w))
  have s10 := runs_regMove (a := 0) (show ι tL ≠ iW by decide) τ₉ (w := ones w) (by tsimp [τ₉])
    (by tsimp [τ₉, τ₈, τ₇, τ₆, τ₅, τ₄, τ₃, τ₂, τ₁, τ₀, hW])
  set τ₁₀ := Function.update (Function.update τ₉ (ι tL) emp) iW (reg (ones w))
  -- D = d - 1 and its ticks
  have s11 := runs_decN (d := d) τ₁₀ (by tsimp [τ₁₀, τ₉, τ₈, τ₇, τ₆, τ₅, τ₄])
    (by tsimp [τ₁₀, τ₉, τ₈, τ₇, τ₆, τ₅, τ₄, τ₃, τ₂, τ₁, τ₀]) (by tsimp [τ₁₀, τ₉, τ₈, τ₇, τ₆, τ₅, τ₄, τ₃, τ₂, τ₁, τ₀, hC])
  set τ₁₁ := Function.update τ₁₀ kN (reg (ones (d - 1)))
  have s12 : Runs (.seq (op0 (a := 0) Rules.ticks false kN xB (by decide)) (.seq (rewind kN) (rewind xB))) τ₁₁
      (· = Function.update τ₁₁ xB ⟨[], List.replicate (d - 1) []⟩) (4 * (d - 1) + 20) := by
    apply Runs.of_wp
    simp only [WP, wp_op0, wp_rewind]
    tsimp [τ₁₁, τ₁₀, τ₉, τ₈, τ₇, τ₆, τ₅, τ₄, τ₃, τ₂, τ₁, τ₀, hB, emp, reg, Rules.output_ticks]
    refine ⟨?_, ?_⟩
    · funext y
      simp only [Function.update_apply]
      split_ifs <;> (try subst_vars) <;> (try tsimp [hB, emp, reg])
    · simp [time, rest]; omega
  set τ₁₂ := Function.update τ₁₁ xB ⟨[], List.replicate (d - 1) []⟩
  -- the flags
  have s13 := runs_flagLoop (ℓ := l) (H := H) ts τ₁₂ [] [] hts (by
      have : tsc.length ≤ hdr.length := by simp [eh, R1, R2, R3, R4]; omega
      simpa [tsc] using this)
    (by tsimp [τ₁₂, τ₁₁, τ₁₀, τ₉, τ₈, τ₇, τ₆, τ₅, τ₄, τ₃, τ₂, τ₁, τ₀])
    (by tsimp [τ₁₂, τ₁₁, τ₁₀, τ₉, tsc])
    (by tsimp [τ₁₂, τ₁₁, τ₁₀, τ₉, τ₈, τ₇, τ₆, τ₅, τ₄, τ₃, τ₂, τ₁, τ₀, hz])
    (by tsimp [τ₁₂, τ₁₁, τ₁₀, τ₉, τ₈, τ₇, τ₆, τ₅, τ₄, τ₃, τ₂, τ₁, τ₀, hz])
    (by tsimp [τ₁₂, τ₁₁, τ₁₀, τ₉, τ₈, τ₇, τ₆, τ₅, τ₄, τ₃, τ₂, τ₁, τ₀, hz])
    (by tsimp [τ₁₂, τ₁₁, τ₁₀, τ₉, τ₈, τ₇, τ₆, τ₅, τ₄, τ₃, τ₂, τ₁, τ₀, hz])
    (by tsimp [τ₁₂, τ₁₁, τ₁₀, τ₉, τ₈, τ₇, τ₆])
    (by tsimp [τ₁₂, τ₁₁, τ₁₀, τ₉, τ₈, τ₇, τ₆, τ₅, τ₄, τ₃, τ₂, τ₁, τ₀, hA, emp])
    (by tsimp [τ₁₂, hD])
    (by tsimp [τ₁₂, τ₁₁, τ₁₀, τ₉, τ₈, τ₇, τ₆, τ₅, τ₄, τ₃, τ₂, τ₁, τ₀, hz])
  set τ₁₃ := Function.update (Function.update (Function.update τ₁₂ (ι tX) (reg []))
    xA ⟨((lengthFlags l ts).map fun b => [b]).reverse ++ [], []⟩) xB ⟨List.replicate ts.length [] ++ [], []⟩
  have s14 := runs_clear (a := 0) (ι tX) τ₁₃
  have s15 := runs_clear (a := 0) (ι c1) (Function.update τ₁₃ (ι tX) ⟨[], []⟩)
  refine (Runs.then s0 (Runs.then s1 (Runs.then s2 (Runs.then s3 (Runs.then s4 (Runs.then s5 (Runs.then s6
    (Runs.then s7 (Runs.then s8 (Runs.then s9 (Runs.then s10 (Runs.then s11 (Runs.then s12 (Runs.then s13
    (Runs.then s14 s15))))))))))))))).mono (fun τ' h => ?_) ?_
  · clear s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15
    rw [h]; funext y
    by_cases hm : y ∈ [iP, kN, iL, kI, iW, xB, xA, ι c1, ι tX, ι tL]
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp only [τ₁₃, τ₁₂, τ₁₁, τ₁₀, τ₉, τ₈, τ₇, τ₆, τ₅, τ₄, τ₃, τ₂, τ₁, τ₀] <;> tsimp [hz, emp]
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hm
      obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8, n9, n10⟩ := hm
      simp only [τ₁₃, τ₁₂, τ₁₁, τ₁₀, τ₉, τ₈, τ₇, τ₆, τ₅, τ₄, τ₃, τ₂, τ₁, τ₀, Function.update_apply, n1, n2, n3,
        n4, n5, n6, n7, n8, n9, n10, ite_false]
  · clear s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15
    tsimp [τ₁₃, τ₁₂, τ₁₁, τ₁₀, τ₉, τ₈, τ₇, τ₆, τ₅, τ₄, τ₃, τ₂, τ₁, τ₀, hz, emp, reg, WTape.words, clen_cons,
      clen_nil, length_ones, SigmaTableTape.clen_reverse, SigmaConstsTape.clen_flags]
    have l1 : (gamma p).length + R1.length = H := by simp [H, eh]
    have l2 : (gamma d).length + R2.length = R1.length := by simp [R1]
    have l3 : (gamma (2 ^ l)).length + R3.length = R2.length := by simp [R2]
    have l4 : (gamma K).length + R4.length = R3.length := by simp [R3]
    have l5 : (gamma w).length + tsc.length = R4.length := by simp [R4]
    have hfl : (lengthFlags l ts).length = ts.length := by simp [lengthFlags]
    unfold paramsCost
    simp only [Nat.mul_assoc] at *
    generalize p.size * (p.size + p + 10) = A1 at *
    generalize d.size * (d.size + d + 10) = A2 at *
    generalize (2 ^ l).size * ((2 ^ l).size + 2 ^ l + 10) = A3 at *
    generalize K.size * (K.size + K + 10) = A4 at *
    generalize w.size * (w.size + w + 10) = A5 at *
    generalize 2 ^ l = R at *
    clear_value H R1 R2 R3 R4 tsc hdr
    omega

/-- `flags_paper`: on axis lengths `2^(ℓ-1)` or `2^ℓ` the code-length flags are the paper's long-axis
flags. -/
theorem flags_paper {ℓ : ℕ} (hℓ : 1 ≤ ℓ) {ts : List ℕ} (hts : ∀ t ∈ ts, t = 2 ^ (ℓ - 1) ∨ t = 2 ^ ℓ) :
    lengthFlags ℓ ts = SigmaConstsTape.paperFlags ts ℓ := by
  apply List.ext_getElem (by simp [lengthFlags, SigmaConstsTape.paperFlags])
  intro i h1 h2
  have hi : i < ts.length := by simpa [lengthFlags] using h1
  simp only [lengthFlags, SigmaConstsTape.paperFlags, List.getElem_map, List.getElem_range, axLen,
    List.getD_eq_getElem _ _ hi, decide_eq_decide]
  rcases hts _ (List.getElem_mem hi) with e | e <;> rw [e, Nat.size_pow, Nat.log_pow (by norm_num)] <;> omega

end TransformParams

end IntegerMultBounds.Schoenhage
