module

public import IntegerMultBounds.ExactRecoveryOutput

/-! §8 milestone for exact recovery (plan/08-exact-multiplication.md): the error
margins come from the size relations instead of being assumed. -/

@[expose] public section

namespace IntegerMultBounds.ExactRecoveryOutput

open Machine NLogN

/-- For all large digit widths `k`: if the transform pipeline at precision `6k`
has scaled errors at most `9 · 2^γ · T · levels`, with `S ≤ T < 2^k`,
`1 ≤ levels < k` and `γ ≤ k/4`, then the rounded, carried output has exactly
`2n` bits and value `x · y`, and installing it at tape zero satisfies the
`EndToEnd` output contract. -/
theorem eventually_outputCorrect_of_sizes : ∀ᶠ k : ℕ in Filter.atTop,
    ∀ {κ : Type} [Fintype κ] {S T levels γ chunks n : ℕ} [NeZero S]
      (F : (ZMod S → ℂ) →L[ℂ] (κ → ℂ)) (F' : (ZMod S → ℂ) → (κ → ℂ))
      (G : (κ → ℂ) →L[ℂ] (ZMod S → ℂ)) (G' : (κ → ℂ) → (ZMod S → ℂ)) {x y : List Bool},
      (digitsOf k x).length + (digitsOf k y).length ≤ S + 1 →
      ‖F‖ ≤ 1 →
      (∀ u : ZMod S → ℂ, ‖u‖ ≤ 1/2 →
        2^(6*k)*‖F' u - F u‖ ≤ 9*(2 : ℝ)^γ*T*levels) →
      ‖G‖ ≤ 1 →
      (∀ v : κ → ℂ, ‖v‖ ≤ 1/2 →
        2^(6*k)*‖G' v - G v‖ ≤ 9*(2 : ℝ)^γ*T*levels) →
      (∀ u v : ZMod S → ℂ, G (fun j => F u j*F v j) = fun i => cconv u v i/(S : ℂ)^2) →
      S ≤ T → 2 ≤ T → T < 2^k → 1 ≤ levels → levels < k → (γ : ℝ) ≤ k/4 →
      2*n ≤ k*chunks → x.length = n → y.length = n →
      (output k chunks n (coefficients (p := 6*k) (k := k) F' G' x y)).length = 2*n ∧
      binaryValue (output k chunks n (coefficients (p := 6*k) (k := k) F' G' x y)) =
        binaryValue x*binaryValue y ∧
      ∀ {t q a : ℕ} (M : Program t q a) (c : Config t q a),
        c.tape ⟨0, M.tapes_pos⟩ = wordTape
          ((output k chunks n (coefficients (p := 6*k) (k := k) F' G' x y)).map bitSymbol) →
        outputCorrect M n x y c := by
  filter_upwards [ExactRecovery.eventually_threshold] with k hthr
  intro κ _ S T levels γ chunks n _ F F' G G' x y hS hF hF' hG hG' hconv hST hT2 hTk hL1 hLk hγ
    hwidth hx hy
  obtain ⟨hEs, hfinal⟩ := ExactRecovery.margins_of_sizes hST hT2 hTk hL1 hLk hγ hthr
  have hk : 0 < k := by omega
  obtain ⟨hlen, hval⟩ :=
    computed_output_spec F F' G G' hk hS hF hF' hG hG' hEs hconv hfinal hwidth hx hy
  exact ⟨hlen, hval, fun M c htape =>
    outputCorrect_of_computed F F' G G' hk hS hF hF' hG hG' hEs hconv hfinal M c hwidth hx hy htape⟩

end IntegerMultBounds.ExactRecoveryOutput
