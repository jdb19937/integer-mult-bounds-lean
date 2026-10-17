module

public import IntegerMultBounds.Schoenhage.RingPointwise
import IntegerMultBounds.Schoenhage.Wp
import Mathlib.Data.Nat.Size

/-! Decoding the signed ring product's own header `Γ(p)Γ(r)Γ(w)` on tapes
into `p`, `log₂ r` and `w` in unary, within the same bound as the transform
header (`hdrDecodes_decodeHeader3`). -/

@[expose] public section

set_option maxRecDepth 10000

namespace IntegerMultBounds.Schoenhage

open Machine Strm Tp Schedule Spec.SignedRingProduct

/-- Decode `Γ(p)Γ(r)Γ(w)` from `zH` into `iP = ones p`, `iL = ones (log₂ r)`, `iW = ones w`. -/
noncomputable def decodeHeader3 : Cmd 0 𝕌 :=
  .seq hdrInit <|
  .seq decodeOne <| .seq (regMove (ι tL) iP (by decide)) <|
  .seq decodeOne <| .seq logOf <|
  .seq decodeOne <| .seq (regMove (ι tL) iW (by decide)) <| .seq (clear (ι tX)) (clear (ι c1))

set_option maxHeartbeats 16000000 in
theorem runs_decodeHeader3 {p l w : ℕ} (hp : 1 ≤ p) (hw : 1 ≤ w)
    (τ : Fin 𝕌 → WTape) (hc : Clean τ) (hH : τ zH = reg (header p (2 ^ l) w))
    (hP : τ iP = emp) (hL : τ iL = emp) (hW : τ iW = emp) :
    Runs decodeHeader3 τ (· = Function.update (Function.update (Function.update τ iP (reg (ones p)))
      iL (reg (ones l))) iW (reg (ones w)))
      (headerCost p (2 ^ l) w (header p (2 ^ l) w).length) := by
  have hz : ∀ i : Fin 𝕋, τ (ι i) = emp := fun i => congrFun hc i
  set hdr := header p (2 ^ l) w
  set R2 := gamma (2 ^ l) ++ gamma w
  have eh : hdr = gamma p ++ R2 := by simp [hdr, header, R2]
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
  have s1 := runs_decodeOne hp (rest := R2) τ₀ (by tsimp [τ₀]) (by tsimp [τ₀, eh])
    (by tsimp [τ₀, hz]) (by tsimp [τ₀, hz]) (by tsimp [τ₀, hz]) (by tsimp [τ₀, hz]) (by tsimp [τ₀, hz])
    (by tsimp [τ₀, hz]) (by tsimp [τ₀, hz]) (by tsimp [τ₀, hz]) (by tsimp [τ₀, hz]) (by tsimp [τ₀, hz])
  set τ₁ := Function.update (Function.update τ₀ (ι tX) (reg R2)) (ι tL) (reg (ones p))
  have s2 := runs_regMove (a := 0) (show ι tL ≠ iP by decide) τ₁ (w := ones p) (by tsimp [τ₁])
    (by tsimp [τ₁, τ₀, hP])
  set τ₂ := Function.update (Function.update τ₁ (ι tL) emp) iP (reg (ones p))
  -- r
  have s5 := runs_decodeOne (Nat.one_le_two_pow (n := l)) (rest := gamma w) τ₂ (by tsimp [τ₂, τ₁, τ₀])
    (by tsimp [τ₂, τ₁, R2])
    (by tsimp [τ₂, τ₁, τ₀, hz]) (by tsimp [τ₂, τ₁, τ₀, hz]) (by tsimp [τ₂, τ₁, τ₀, hz])
    (by tsimp [τ₂, τ₁, τ₀, hz]) (by tsimp [τ₂, τ₁, τ₀, hz]) (by tsimp [τ₂, τ₁, τ₀, hz])
    (by tsimp [τ₂, τ₁, τ₀, hz]) (by tsimp [τ₂, τ₁, τ₀, hz]) (by tsimp [τ₂, τ₁, τ₀, hz])
    (by tsimp [τ₂, τ₁, τ₀, hz])
  set τ₅ := Function.update (Function.update τ₂ (ι tX) (reg (gamma w))) (ι tL) (reg (ones (2 ^ l)))
  have s6 := runs_logOf (r := 2 ^ l) τ₅ (by tsimp [τ₅]) (by tsimp [τ₅, τ₂, τ₁, τ₀, hz])
    (by tsimp [τ₅, τ₂, τ₁, τ₀, hz]) (by tsimp [τ₅, τ₂, τ₁, τ₀, hz])
    (by tsimp [τ₅, τ₂, τ₁, τ₀]) (by tsimp [τ₅, τ₂, τ₁, τ₀, hz])
    (by tsimp [τ₅, τ₂, τ₁, τ₀, hz]) (by tsimp [τ₅, τ₂, τ₁, τ₀, hL])
  rw [Nat.size_pow, Nat.add_sub_cancel] at s6
  set τ₆ := Function.update (Function.update τ₅ (ι tL) emp) iL (reg (ones l))
  -- w
  have s9 := runs_decodeOne hw (rest := []) τ₆ (by tsimp [τ₆, τ₅, τ₂, τ₁, τ₀]) (by tsimp [τ₆, τ₅])
    (by tsimp [τ₆, τ₅, τ₂, τ₁, τ₀, hz]) (by tsimp [τ₆, τ₅, τ₂, τ₁, τ₀, hz])
    (by tsimp [τ₆, τ₅, τ₂, τ₁, τ₀, hz]) (by tsimp [τ₆, τ₅, τ₂, τ₁, τ₀, hz])
    (by tsimp [τ₆, τ₅, τ₂, τ₁, τ₀, hz]) (by tsimp [τ₆, τ₅, τ₂, τ₁, τ₀, hz])
    (by tsimp [τ₆, τ₅, τ₂, τ₁, τ₀, hz]) (by tsimp [τ₆, τ₅, τ₂, τ₁, τ₀, hz])
    (by tsimp [τ₆, τ₅, τ₂, τ₁, τ₀, hz]) (by tsimp [τ₆, τ₅, τ₂, τ₁, τ₀, hz])
  set τ₉ := Function.update (Function.update τ₆ (ι tX) (reg [])) (ι tL) (reg (ones w))
  have s10 := runs_regMove (a := 0) (show ι tL ≠ iW by decide) τ₉ (w := ones w) (by tsimp [τ₉])
    (by tsimp [τ₉, τ₆, τ₅, τ₂, τ₁, τ₀, hW])
  set τ₁₀ := Function.update (Function.update τ₉ (ι tL) emp) iW (reg (ones w))
  have s11 := runs_clear (a := 0) (ι tX) τ₁₀
  have s12 := runs_clear (a := 0) (ι c1) (Function.update τ₁₀ (ι tX) ⟨[], []⟩)
  refine (Runs.then s0 (Runs.then s1 (Runs.then s2 (Runs.then s5 (Runs.then s6
    (Runs.then s9 (Runs.then s10 (Runs.then s11 s12)))))))).mono
    (fun τ' h => ?_) ?_
  · clear s0 s1 s2 s5 s6 s9 s10 s11 s12
    rw [h]; funext y
    by_cases hm : y ∈ [iP, iL, iW, ι c1, ι tX, ι tL]
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp only [τ₁₀, τ₉, τ₆, τ₅, τ₂, τ₁, τ₀] <;> tsimp [hz, emp]
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hm
      obtain ⟨n1, n2, n3, n4, n5, n6⟩ := hm
      simp only [τ₁₀, τ₉, τ₆, τ₅, τ₂, τ₁, τ₀, Function.update_apply, n1, n2, n3, n4, n5, n6,
        ite_false]
  · clear s0 s1 s2 s5 s6 s9 s10 s11 s12
    tsimp [τ₁₀, τ₉, τ₆, τ₅, τ₂, τ₁, τ₀, hz, emp, reg, WTape.words, clen_cons, clen_nil,
      length_ones]
    have l1 : (gamma p).length + R2.length = H := by simp [H, eh]
    have l3 : (gamma (2 ^ l)).length + (gamma w).length = R2.length := by simp [R2]
    unfold headerCost
    simp only [Nat.mul_assoc] at *
    generalize p.size * (p.size + p + 10) = A1 at *
    generalize (2 ^ l).size * ((2 ^ l).size + 2 ^ l + 10) = A3 at *
    generalize w.size * (w.size + w + 10) = A5 at *
    generalize 2 ^ l = R at *
    clear_value H R2 hdr
    omega

theorem hdrDecodes_decodeHeader3 {p l w : ℕ} (hp : 1 ≤ p) (hw : 1 ≤ w) :
    HdrDecodes decodeHeader3 (header p (2 ^ l) w) p l w :=
  fun τ hc hH hP hL hW => runs_decodeHeader3 hp hw τ hc hH hP hL hW

end IntegerMultBounds.Schoenhage
