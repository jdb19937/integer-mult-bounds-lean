import IntegerMultBounds.Schoenhage.RingLemmaHeader
import IntegerMultBounds.Schoenhage.RingPointwiseTarget

/-! The signed ring product lemma (`lem:signed-ring-product`) on its own
interface: header `Γ(p)Γ(r)Γ(w)` on tape 0, the two records on tapes 1 and 2,
the record `Q_p(fg/r)` written on tape 3 (`ring_meets : Meets`), within
`O(r p log (r p) log log (r p))` steps (`ring_polylog : polylogTarget 1`).
The program is the pointwise-product program with the three-code header
decoder, run on a single record. -/

set_option maxRecDepth 10000

namespace IntegerMultBounds.Schoenhage

open Machine Strm Tp Schedule Spec.SignedRingProduct

/-- The compiled word program with the three-code header decoder. -/
noncomputable def ringCoreProg : Program 𝕌 (compile (a := 0) (by decide) (pwCoreWith decodeHeader3)).1 0 :=
  (compile (a := 0) (by decide) (pwCoreWith decodeHeader3)).2

/-- The signed ring product program on the paper's tapes. -/
noncomputable def ringLemmaProgram := Machine.reindex (pwProg91With ringCoreProg) dataSwap

theorem array_single {r : ℕ} (w : ℕ) (f : Rec r) : array w [f] = record w f.1 f.2 := by
  simp [array]

/-- The time bound: the word-level bound maximized over the admissible widths. -/
def ringLemmaTime (Cw : ℕ) (r p : ℕ) : ℕ :=
  (Finset.range (Cw * p + 1)).sup fun w =>
    pwCost p 0 (Nat.log 2 r) 0 w (header p r w).length 1 (2 * (r * 1) * w) +
      4 * ((header p r w).length + 3 * (2 * (r * 1) * w)) + 60

set_option maxHeartbeats 4000000 in
theorem ring_meets (Cw : ℕ) : Meets ringLemmaProgram Cw (ringLemmaTime Cw) := by
  intro p l w fr fi gr gi hl hp hpr hw hwC hf hg
  set f : Rec (2 ^ l) := (fr, fi)
  set g : Rec (2 ^ l) := (gr, gi)
  have hc := runs_pwCoreWith (fs := [f]) (gs := [g]) (hdrDecodes_decodeHeader3 (l := l) (by omega) (by omega))
    hw rfl (by simpa [f] using hf) (by simpa [g] using hg)
  obtain ⟨σ', k, hx, hq, hk⟩ := hc
  subst hq
  have h4 := (compile_correct (by decide) hx).consequence (fun _ h => h) (fun _ h => h) hk
  have h := (pwProg91With_hoare (core := ringCoreProg) h4).reindex dataSwap
  have eF : array w [f] = record w fr fi := array_single w f
  have eG : array w [g] = record w gr gi := array_single w g
  have eO : array w (List.zipWith (prodRec p) [f] [g]) =
      record w (productRe p (gridPoly p fr fi) (gridPoly p gr gi))
        (productIm p (gridPoly p fr fi) (gridPoly p gr gi)) := by
    simp [array, prodRec, f, g]
  refine h.consequence (fun v hv => ⟨_, rfl, by rw [hv, raw91_reindex, eF, eG]⟩)
    (fun v ⟨o, ho, hv⟩ => by rw [hv, ho, raw91_reindex, eF, eG, eO]) ?_
  have hF : (array w [f]).length = 2 * (2 ^ l * 1) * w := by rw [length_array]; simp
  have hG : (array w [g]).length = 2 * (2 ^ l * 1) * w := by rw [length_array]; simp
  have hO : (array w (List.zipWith (prodRec p) [f] [g])).length = 2 * (2 ^ l * 1) * w := by
    rw [length_array]; simp
  set H := (header p (2 ^ l) w).length
  let G' := fun w' => pwCost p 0 (Nat.log 2 (2 ^ l)) 0 w' (header p (2 ^ l) w').length 1 (2 * (2 ^ l * 1) * w') +
    4 * ((header p (2 ^ l) w').length + 3 * (2 * (2 ^ l * 1) * w')) + 60
  have hle : G' w ≤ (Finset.range (Cw * p + 1)).sup G' := Finset.le_sup (Finset.mem_range.mpr (by omega))
  have hgw : G' w = pwCost p 0 l 0 w H [f].length (array w [f]).length + 4 * (H + 3 * (2 * (2 ^ l * 1) * w)) + 60 := by
    simp only [G', Nat.log_pow (by norm_num : 1 < 2), hF, H, List.length_singleton]
  unfold ringLemmaTime
  refine le_trans ?_ hle
  rw [hgw, hF, hG, hO]
  generalize pwCost p 0 l 0 w H [f].length (2 * (2 ^ l * 1) * w) = P
  omega

theorem length_header_le (p r w : ℕ) : (header p r w).length ≤ 2 * (p + r + w) := by
  simp only [header, List.length_append, gamma, List.length_replicate, length_msbBits]
  have := Nat.size_le.mpr (Nat.lt_two_pow_self (n := p))
  have := Nat.size_le.mpr (Nat.lt_two_pow_self (n := r))
  have := Nat.size_le.mpr (Nat.lt_two_pow_self (n := w))
  omega

theorem ring_polylog : polylogTarget 1 := by
  intro Cw hCw
  refine ⟨𝕌, _, 0, ringLemmaProgram, ptC Cw * (5 + 2 * Cw), by norm_num, ?_⟩
  intro p l w fr fi gr gi hl hp hpr hw hwC hf hg
  refine (ring_meets Cw p l w fr fi gr gi hl hp hpr hw hwC hf hg).consequence
    (fun _ h => h) (fun _ h => h) ?_
  have hlp : l < p := (Nat.pow_lt_pow_iff_right (by norm_num)).mp hpr
  unfold ringLemmaTime
  apply Finset.sup_le
  intro w' hw'
  have hw'' : w' ≤ Cw * p := by simp at hw'; omega
  rw [Nat.log_pow (by norm_num)]
  have t := term_le (M := 1) (H := (header p (2 ^ l) w').length) hp hl hlp le_rfl hw''
  have hH := length_header_le p (2 ^ l) w'
  have hlt : l < 2 ^ l := Nat.lt_two_pow_self
  set X := 2 ^ l * p * (Nat.log 2 (2 ^ l * p) + 1) * (Nat.log 2 (Nat.log 2 (2 ^ l * p) + 1) + 1)
  have hX : 2 ^ l * p ≤ X := by
    simp only [X]
    calc 2 ^ l * p = 2 ^ l * p * 1 * 1 := by ring
      _ ≤ _ := by gcongr <;> omega
  have hH' : (header p (2 ^ l) w').length ≤ (4 + 2 * Cw) * X := by
    have h1 : p ≤ 2 ^ l * p := Nat.le_mul_of_pos_left _ (by positivity)
    have h2 : 2 ^ l ≤ 2 ^ l * p := Nat.le_mul_of_pos_right _ (by omega)
    have h3 : Cw * p ≤ Cw * (2 ^ l * p) := Nat.mul_le_mul_left _ h1
    nlinarith
  simp only [pow_one, Nat.mul_one] at t ⊢
  calc _ ≤ ptC Cw * (X + (header p (2 ^ l) w').length) := by simpa [X, Nat.mul_assoc] using t
    _ ≤ ptC Cw * (X + (4 + 2 * Cw) * X) := by gcongr
    _ = ptC Cw * (5 + 2 * Cw) * X := by ring
    _ = _ := by simp only [X]; ring

end IntegerMultBounds.Schoenhage
