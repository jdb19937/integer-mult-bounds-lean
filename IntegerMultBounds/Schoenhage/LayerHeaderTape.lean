module

public import IntegerMultBounds.Schoenhage.ConvScaleRun
public import IntegerMultBounds.Schoenhage.TransformParams

/-! The header of a simultaneous-layer call written on tapes. The layer header
`Γ(p)Γ(d)Γ(r)Γ(D)Γ(P)Γ(S)Γ(K)Γ(ρ+1)Γ(w)` is built as one word: each code of a
unary register is produced by the width-code program `gammaOut` around which
its two input registers are saved and restored (`runs_encodeAppend`), and each
power of two `2^a` is written directly as `a` zeros, a one and `a` zeros
(`runs_powAppend`, `gamma_two_pow`). With `r = 2^ℓ`, `P = 2^eP` and `S = 2^eS`
the program leaves `layerHeader p d r D P S K ρ w` (`runs_layerHdr`). -/

@[expose] public section

set_option maxRecDepth 10000

namespace IntegerMultBounds.Schoenhage

open Machine Strm Tp Schedule Spec.SignedRingProduct TwistDescriptors

namespace LayerHeaderTape

theorem gamma_two_pow (a : ℕ) : gamma (2 ^ a) = List.replicate a false ++ true :: List.replicate a false := by
  rw [gamma, Nat.size_pow, Nat.add_sub_cancel, msbBits_two_pow]

/-- The header being built. -/
abbrev hO : Fin 𝕌 := zO

/-- Append the code of the unary register `src` to the header word. -/
noncomputable def encodeAppend (src : Fin 𝕌) (h : src ≠ xE) : Cmd 0 𝕌 :=
  .seq (regDup src xE h) <| .seq (regMove iW kW (by decide)) <| .seq (regMove kI kR (by decide)) <|
  .seq (regMove xE iW (by decide)) <| .seq (emit [[]] kI) <| .seq (rewind kI) <| .seq gammaOut <|
  .seq (op0 Rules.copy true zG hO (by decide)) <| .seq (clear zG) <| .seq (clear iW) <| .seq (clear kI) <|
  .seq (regMove kW iW (by decide)) (regMove kR kI (by decide))

/-- Append `Γ(2^a)` for the unary register `src = ones a`: `a` zeros, a one, `a` zeros. -/
noncomputable def powAppend (src : Fin 𝕌) (h : src ≠ hO) (h' : kC ≠ hO) : Cmd 0 𝕌 :=
  .seq (op0 (Rules.fill false) true src hO h) <| .seq (rewind src) <|
  .seq (op0 Rules.copy true kC hO h') <| .seq (rewind kC) <|
  .seq (op0 (Rules.fill false) true src hO h) (rewind src)

set_option maxHeartbeats 8000000 in
theorem runs_powAppend {src : Fin 𝕌} (h : src ≠ hO) (h' : kC ≠ hO) (hsC : src ≠ kC) {a : ℕ} {u : List Bool}
    (τ : Fin 𝕌 → WTape) (hs : τ src = reg (ones a)) (hC : τ kC = reg [true]) (hOut : τ hO = ⟨[u], []⟩) :
    Runs (powAppend src h h') τ (· = Function.update τ hO ⟨[u ++ gamma (2 ^ a)], []⟩) (8 * a + 50) := by
  apply Runs.of_wp
  simp only [powAppend, WP, wp_op0, wp_rewind]
  simp only [Function.update_apply, hs, hC, hOut, h, h', hsC, h.symm, h'.symm, hsC.symm, ↓reduceIte, reg,
    WTape.next_mk, WTape.cur_mk, List.headD_cons, List.tail_cons, Rules.output_copy, Rules.output_fill,
    ↓parse_syms, length_ones]
  refine ⟨⟨by simp, by simp, by simp, fun _ => ⟨by simp, by simp⟩⟩, ⟨by simp, by simp, by simp,
    fun _ => ⟨by simp, by simp⟩⟩, ⟨by simp, by simp, by simp, fun _ => ⟨by simp, by simp⟩⟩, ?_, ?_⟩
  · funext i
    simp only [Function.update_apply]
    split_ifs <;> subst_vars <;> simp_all [WTape.put, reg, gamma_two_pow, List.append_assoc]
  · simp [time, rest, clen]; omega

theorem length_gamma_le (v : ℕ) : (gamma v).length ≤ 2 * v + 1 := by
  rcases Nat.eq_zero_or_pos v with rfl | hv
  · simp [gamma]
  · rw [length_gamma hv]; have := size_le_self v; omega

set_option maxHeartbeats 32000000 in
/-- `runs_encodeAppend`: the code of the unary register `src` is appended to the header word; every
register is restored. -/
theorem runs_encodeAppend {src : Fin 𝕌} (h : src ≠ xE) {v w K : ℕ} {u : List Bool} (τ : Fin 𝕌 → WTape)
    (hc : Clean τ) (hs : τ src = reg (ones v)) (hW : τ iW = reg (ones w)) (hK : τ kI = reg (ones K))
    (hE : τ xE = emp) (hkW : τ kW = emp) (hkR : τ kR = emp) (hG : τ zG = emp) (hOut : τ hO = ⟨[u], []⟩) :
    Runs (encodeAppend src h) τ (· = Function.update τ hO ⟨[u ++ gamma v], []⟩)
      (220 * v + 20 * w + 20 * K + 800) := by
  have hz : ∀ i : Fin 𝕋, τ (ι i) = emp := fun i => congrFun hc i
  have s1 := runs_regDup (a := 0) h τ hs hE
  set τ₁ := Function.update τ xE (reg (ones v)) with hτ₁
  have s2 := runs_regMove (a := 0) (show iW ≠ kW by decide) τ₁ (w := ones w) (by tsimp [hτ₁, hW])
    (by tsimp [hτ₁, hkW])
  set τ₂ := Function.update (Function.update τ₁ iW emp) kW (reg (ones w)) with hτ₂
  have s3 := runs_regMove (a := 0) (show kI ≠ kR by decide) τ₂ (w := ones K) (by tsimp [hτ₂, hτ₁, hK])
    (by tsimp [hτ₂, hτ₁, hkR])
  set τ₃ := Function.update (Function.update τ₂ kI emp) kR (reg (ones K)) with hτ₃
  have s4 := runs_regMove (a := 0) (show xE ≠ iW by decide) τ₃ (w := ones v) (by tsimp [hτ₃, hτ₂, hτ₁])
    (by tsimp [hτ₃, hτ₂, emp])
  set τ₄ := Function.update (Function.update τ₃ xE emp) iW (reg (ones v)) with hτ₄
  have s5 := runs_emit (a := 0) [[]] kI τ₄ (by tsimp [hτ₄, hτ₃, emp])
  set τ₅ := Function.update τ₄ kI ⟨[[]].reverse ++ (τ₄ kI).left, []⟩ with hτ₅
  have s6 := runs_rewind (a := 0) kI τ₅
  set τ₆ := Function.update τ₅ kI ⟨[], (τ₅ kI).left.reverse ++ (τ₅ kI).right⟩ with hτ₆
  have hc₆ : Clean τ₆ := by
    funext i
    simp only [Function.comp_apply, hτ₆, hτ₅, hτ₄, hτ₃, hτ₂, hτ₁, Function.update_apply]
    have : ι i ≠ kI := by intro e; have := congrArg Fin.val e; simp at this; omega
    have : ι i ≠ xE := by intro e; have := congrArg Fin.val e; simp at this; omega
    have : ι i ≠ iW := by intro e; have := congrArg Fin.val e; simp at this; omega
    have : ι i ≠ kW := by intro e; have := congrArg Fin.val e; simp at this; omega
    have : ι i ≠ kR := by intro e; have := congrArg Fin.val e; simp at this; omega
    simp_all
  have s7 := runs_gammaOut (w := v) (k := 0) τ₆ hc₆ (by tsimp [hτ₆, hτ₅, hτ₄])
    (by tsimp [hτ₆, hτ₅, hτ₄, hτ₃, emp, reg, ones]) (by tsimp [hτ₆, hτ₅, hτ₄, hτ₃, hτ₂, hτ₁, hG])
  rw [Nat.add_zero] at s7
  set τ₇ := Function.update τ₆ zG (reg (gamma v)) with hτ₇
  have s8 := runs_op0 (a := 0) Rules.copy true (show zG ≠ hO by decide) τ₇ (by tsimp [hτ₇, reg])
    (by tsimp [hτ₇, hτ₆, hτ₅, hτ₄, hτ₃, hτ₂, hτ₁, hOut]) [gamma v] (by tsimp [hτ₇, reg, Rules.output_copy])
    (fun _ => ⟨by tsimp [hτ₇, hτ₆, hτ₅, hτ₄, hτ₃, hτ₂, hτ₁, hOut], by simp⟩)
  set τ₈ := Function.update (Function.update τ₇ zG (τ₇ zG).next) hO ((τ₇ hO).put true [gamma v]) with hτ₈
  have s9 := runs_clear (a := 0) zG τ₈
  set τ₉ := Function.update τ₈ zG ⟨[], []⟩ with hτ₉
  have s10 := runs_clear (a := 0) iW τ₉
  set τ₁₀ := Function.update τ₉ iW ⟨[], []⟩ with hτ₁₀
  have s11 := runs_clear (a := 0) kI τ₁₀
  set τ₁₁ := Function.update τ₁₀ kI ⟨[], []⟩ with hτ₁₁
  have s12 := runs_regMove (a := 0) (show kW ≠ iW by decide) τ₁₁ (w := ones w)
    (by tsimp [hτ₁₁, hτ₁₀, hτ₉, hτ₈, hτ₇, hτ₆, hτ₅, hτ₄, hτ₃, hτ₂]) (by tsimp [hτ₁₁, hτ₁₀, emp])
  set τ₁₂ := Function.update (Function.update τ₁₁ kW emp) iW (reg (ones w)) with hτ₁₂
  have s13 := runs_regMove (a := 0) (show kR ≠ kI by decide) τ₁₂ (w := ones K)
    (by tsimp [hτ₁₂, hτ₁₁, hτ₁₀, hτ₉, hτ₈, hτ₇, hτ₆, hτ₅, hτ₄, hτ₃]) (by tsimp [hτ₁₂, hτ₁₁, emp])
  refine (Runs.then s1 (Runs.then s2 (Runs.then s3 (Runs.then s4 (Runs.then s5 (Runs.then s6 (Runs.then s7
    (Runs.then s8 (Runs.then s9 (Runs.then s10 (Runs.then s11 (Runs.then s12 s13)))))))))))).mono
    (fun τ' e => ?_) ?_
  · rw [e]; funext y
    by_cases hm : y ∈ [hO, xE, kW, kR, iW, kI, zG]
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp only [hτ₁₂, hτ₁₁, hτ₁₀, hτ₉, hτ₈, hτ₇, hτ₆, hτ₅, hτ₄, hτ₃, hτ₂, hτ₁] <;>
        tsimp [hE, hkW, hkR, hW, hK, hG, hOut, emp, reg, WTape.put]
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hm
      obtain ⟨n1, n2, n3, n4, n5, n6, n7⟩ := hm
      simp only [hτ₁₂, hτ₁₁, hτ₁₀, hτ₉, hτ₈, hτ₇, hτ₆, hτ₅, hτ₄, hτ₃, hτ₂, hτ₁, Function.update_apply, n1, n2,
        n3, n4, n5, n6, n7, ite_false]
  · have hg := length_gamma_le v
    tsimp [hτ₁₂, hτ₁₁, hτ₁₀, hτ₉, hτ₈, hτ₇, hτ₆, hτ₅, hτ₄, hτ₃, hτ₂, hτ₁, hOut, time_copy, clen, emp, reg,
      WTape.words, WTape.put]
    omega

/-- The whole layer header, from the registers `iP = p`, `xP = d`, `iL = ℓ`, `kN = D`, `lR = eP`,
`lI = eS`, `kI = K`, `xQ = ρ + 1`, `iW = w`. -/
noncomputable def layerHdr : Cmd 0 𝕌 :=
  .seq (emit [[]] hO) <| .seq (encodeAppend iP (by decide)) <| .seq (encodeAppend xP (by decide)) <|
  .seq (powAppend iL (by decide) (by decide)) <| .seq (encodeAppend kN (by decide)) <|
  .seq (powAppend lR (by decide) (by decide)) <| .seq (powAppend lI (by decide) (by decide)) <|
  .seq (encodeAppend kI (by decide)) <| .seq (encodeAppend xQ (by decide)) <|
  .seq (encodeAppend iW (by decide)) (rewind hO)

set_option maxHeartbeats 32000000 in
/-- `runs_layerHdr`: the program writes `layerHeader p d (2^ℓ) D (2^eP) (2^eS) K ρ w` on `zO`, all other
tapes unchanged. -/
theorem runs_layerHdr {p d ℓ D eP eS K ρ w : ℕ} (τ : Fin 𝕌 → WTape) (hc : Clean τ)
    (hP : τ iP = reg (ones p)) (hd : τ xP = reg (ones d)) (hL : τ iL = reg (ones ℓ)) (hN : τ kN = reg (ones D))
    (hR : τ lR = reg (ones eP)) (hI : τ lI = reg (ones eS)) (hK : τ kI = reg (ones K))
    (hQ : τ xQ = reg (ones (ρ + 1))) (hW : τ iW = reg (ones w)) (hC : τ kC = reg [true])
    (hE : τ xE = emp) (hkW : τ kW = emp) (hkR : τ kR = emp) (hG : τ zG = emp) (hOut : τ hO = emp) :
    Runs layerHdr τ (· = Function.update τ hO
        (reg (layerHeader p d (2 ^ ℓ) D (2 ^ eP) (2 ^ eS) K ρ w)))
      (220 * (p + d + D + K + (ρ + 1) + w) + 130 * (w + K) + 8 * (ℓ + eP + eS) + 10000 +
        clen [layerHeader p d (2 ^ ℓ) D (2 ^ eP) (2 ^ eS) K ρ w]) := by
  set τ₀ := Function.update τ hO ⟨[[]], []⟩ with hτ₀
  have s0 : Runs (emit (a := 0) [[]] hO) τ (· = τ₀) 1 :=
    (runs_emit (a := 0) [[]] hO τ (by rw [hOut]; rfl)).mono (fun τ' e => by rw [e, hOut]; rfl)
      (by simp [clen])
  have hc₀ : Clean τ₀ := by
    funext i; simp only [Function.comp_apply, hτ₀, Function.update_apply]
    have : ι i ≠ hO := by intro e; have := congrArg Fin.val e; simp at this; omega
    simp only [this, ite_false]; exact congrFun hc i
  -- one encode step keeps everything but the header word
  have enc : ∀ {src : Fin 𝕌} (h : src ≠ xE) {v : ℕ} (u : List Bool) (σ : Fin 𝕌 → WTape), Clean σ →
      σ src = reg (ones v) → σ iW = reg (ones w) → σ kI = reg (ones K) → σ xE = emp → σ kW = emp → σ kR = emp →
      σ zG = emp → σ hO = ⟨[u], []⟩ →
      Runs (encodeAppend src h) σ (· = Function.update σ hO ⟨[u ++ gamma v], []⟩) (220 * v + 20 * w + 20 * K + 800) := by
    intro src h v u σ hcσ hs hW' hK' hE' hkW' hkR' hG' hO'
    exact runs_encodeAppend h σ hcσ hs hW' hK' hE' hkW' hkR' hG' hO'
  have cl : ∀ (σ : Fin 𝕌 → WTape) (W : WTape), Clean σ → Clean (Function.update σ hO W) := by
    intro σ W hcσ
    funext i; simp only [Function.comp_apply, Function.update_apply]
    have : ι i ≠ hO := by intro e; have := congrArg Fin.val e; simp at this; omega
    simp only [this, ite_false]; exact congrFun hcσ i
  have upd2 : ∀ (σ : Fin 𝕌 → WTape) (A B : WTape), Function.update (Function.update σ hO A) hO B =
      Function.update σ hO B := fun σ A B => Function.update_idem _ _ _
  set u1 := [] ++ gamma p
  have s1 := enc (show iP ≠ xE by decide) (v := p) [] τ₀ hc₀ (by tsimp [hτ₀, hP]) (by tsimp [hτ₀, hW])
    (by tsimp [hτ₀, hK]) (by tsimp [hτ₀, hE]) (by tsimp [hτ₀, hkW]) (by tsimp [hτ₀, hkR]) (by tsimp [hτ₀, hG])
    (by tsimp [hτ₀])
  set u2 := u1 ++ gamma d
  have s2 := enc (show xP ≠ xE by decide) (v := d) u1 (Function.update τ₀ hO ⟨[u1], []⟩) (cl _ _ hc₀)
    (by tsimp [hτ₀, hd]) (by tsimp [hτ₀, hW]) (by tsimp [hτ₀, hK]) (by tsimp [hτ₀, hE]) (by tsimp [hτ₀, hkW])
    (by tsimp [hτ₀, hkR]) (by tsimp [hτ₀, hG]) (by tsimp [hτ₀])
  simp only [upd2] at s2
  set u3 := u2 ++ gamma (2 ^ ℓ)
  have s3 := runs_powAppend (src := iL) (by decide) (by decide) (by decide) (a := ℓ) (u := u2)
    (Function.update τ₀ hO ⟨[u2], []⟩) (by tsimp [hτ₀, hL]) (by tsimp [hτ₀, hC]) (by tsimp [hτ₀])
  simp only [upd2] at s3
  set u4 := u3 ++ gamma D
  have s4 := enc (show kN ≠ xE by decide) (v := D) u3 (Function.update τ₀ hO ⟨[u3], []⟩) (cl _ _ hc₀)
    (by tsimp [hτ₀, hN]) (by tsimp [hτ₀, hW]) (by tsimp [hτ₀, hK]) (by tsimp [hτ₀, hE]) (by tsimp [hτ₀, hkW])
    (by tsimp [hτ₀, hkR]) (by tsimp [hτ₀, hG]) (by tsimp [hτ₀])
  simp only [upd2] at s4
  set u5 := u4 ++ gamma (2 ^ eP)
  have s5 := runs_powAppend (src := lR) (by decide) (by decide) (by decide) (a := eP) (u := u4)
    (Function.update τ₀ hO ⟨[u4], []⟩) (by tsimp [hτ₀, hR]) (by tsimp [hτ₀, hC]) (by tsimp [hτ₀])
  simp only [upd2] at s5
  set u6 := u5 ++ gamma (2 ^ eS)
  have s6 := runs_powAppend (src := lI) (by decide) (by decide) (by decide) (a := eS) (u := u5)
    (Function.update τ₀ hO ⟨[u5], []⟩) (by tsimp [hτ₀, hI]) (by tsimp [hτ₀, hC]) (by tsimp [hτ₀])
  simp only [upd2] at s6
  set u7 := u6 ++ gamma K
  have s7 := enc (show kI ≠ xE by decide) (v := K) u6 (Function.update τ₀ hO ⟨[u6], []⟩) (cl _ _ hc₀)
    (by tsimp [hτ₀, hK]) (by tsimp [hτ₀, hW]) (by tsimp [hτ₀, hK]) (by tsimp [hτ₀, hE]) (by tsimp [hτ₀, hkW])
    (by tsimp [hτ₀, hkR]) (by tsimp [hτ₀, hG]) (by tsimp [hτ₀])
  simp only [upd2] at s7
  set u8 := u7 ++ gamma (ρ + 1)
  have s8 := enc (show xQ ≠ xE by decide) (v := ρ + 1) u7 (Function.update τ₀ hO ⟨[u7], []⟩) (cl _ _ hc₀)
    (by tsimp [hτ₀, hQ]) (by tsimp [hτ₀, hW]) (by tsimp [hτ₀, hK]) (by tsimp [hτ₀, hE]) (by tsimp [hτ₀, hkW])
    (by tsimp [hτ₀, hkR]) (by tsimp [hτ₀, hG]) (by tsimp [hτ₀])
  simp only [upd2] at s8
  set u9 := u8 ++ gamma w
  have s9 := enc (show iW ≠ xE by decide) (v := w) u8 (Function.update τ₀ hO ⟨[u8], []⟩) (cl _ _ hc₀)
    (by tsimp [hτ₀, hW]) (by tsimp [hτ₀, hW]) (by tsimp [hτ₀, hK]) (by tsimp [hτ₀, hE]) (by tsimp [hτ₀, hkW])
    (by tsimp [hτ₀, hkR]) (by tsimp [hτ₀, hG]) (by tsimp [hτ₀])
  simp only [upd2] at s9
  have s10 := runs_rewind (a := 0) hO (Function.update τ₀ hO ⟨[u9], []⟩)
  have hu9 : u9 = layerHeader p d (2 ^ ℓ) D (2 ^ eP) (2 ^ eS) K ρ w := by
    simp [u9, u8, u7, u6, u5, u4, u3, u2, u1, layerHeader]
  refine (Runs.then s0 (Runs.then s1 (Runs.then s2 (Runs.then s3 (Runs.then s4 (Runs.then s5 (Runs.then s6
    (Runs.then s7 (Runs.then s8 (Runs.then s9 s10)))))))))).mono (fun τ' e => ?_) ?_
  · rw [e, hτ₀]; simp only [upd2, ← hu9]
    rfl
  · tsimp [hτ₀, ← hu9, clen]
    omega

/-- A chunk-group round's layer shape: with `eS = cDK` and `eP = n - (c+1)DK`, the call covers all
`2^n` records, `P · S · 2^(KD) = 2^n`. -/
theorem layerShape {n c D K : ℕ} (h : (c + 1) * D * K ≤ n) :
    2 ^ (n - (c + 1) * D * K) * 2 ^ (c * D * K) * 2 ^ (K * D) = 2 ^ n := by
  rw [← pow_add, ← pow_add]
  congr 1
  have : (c + 1) * D * K = c * D * K + K * D := by ring
  omega

end LayerHeaderTape

end IntegerMultBounds.Schoenhage
