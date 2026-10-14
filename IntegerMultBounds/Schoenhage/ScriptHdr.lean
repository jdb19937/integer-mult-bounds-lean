module

public import IntegerMultBounds.Schoenhage.LayerHeaderTape
public import IntegerMultBounds.Schoenhage.ScriptOps

/-! The header pass of the round-script writer (§6). On the ring product's bank, for every chunk
group `c < q` and every bit `ρ < K` of the group, the layer-header program
(`LayerHeaderTape.runs_layerHdr`) writes the layer header with `S = 2^(c·DK)` and
`P = 2^(e₀ - c·DK)`, and the header is appended to `rF` (`runs_hdrPass`). The headers come out in
the order of the chunk-group slots. -/

@[expose] public section

set_option maxRecDepth 100000

namespace IntegerMultBounds.Schoenhage

open Machine Strm Tp Spec.SignedRingProduct ScriptOps LayerHeaderTape

namespace ScriptHdr

/-- The headers of chunk group `c`. -/
def groupHdrs (p d ℓ D K w e0 DK c : ℕ) : List (List Bool) :=
  (List.range K).map fun ρ => layerHeader p d (2 ^ ℓ) D (2 ^ (e0 - c * DK)) (2 ^ (c * DK)) K ρ w

/-- The headers of the first `c` chunk groups. -/
def allHdrs (p d ℓ D K w e0 DK c : ℕ) : List (List Bool) :=
  (List.range c).flatMap (groupHdrs p d ℓ D K w e0 DK)

/-- Raise `xQ` by one. -/
noncomputable def incQ : Cmd 0 𝕌 := .seq (skp xQ kS (by decide)) <| .seq (appendReg kC xQ (by decide)) (rewind xQ)

/-- One header: write it, append it to `rF`, raise `ρ`. -/
noncomputable def hdrStep : Cmd 0 𝕌 :=
  .seq layerHdr <| .seq (cpy zO rF (by decide)) <| .seq (clear zO) <| .seq incQ (skp rO kS (by decide))

/-- The headers of one chunk group. -/
noncomputable def hdrInner : Cmd 0 𝕌 := .loop rO hdrStep

/-- One chunk group: `K` ticks, `ρ + 1 = 1`, the group's headers, then `S` and `P` move by `DK`. -/
noncomputable def hdrGroup : Cmd 0 𝕌 :=
  .seq (ticksReg kI rO (by decide)) <| .seq (emit [[true]] xQ) <| .seq (rewind xQ) <| .seq hdrInner <|
  .seq (clear rO) <| .seq (clear xQ) <| .seq (skp lI kS (by decide)) <| .seq (appendReg kO lI (by decide)) <|
  .seq (rewind lI) <| .seq (dropReg lR kO kH (by decide) (by decide) (by decide)) <| .seq (clear lR) <|
  .seq (regMove kH lR (by decide)) (skp rG kS (by decide))

/-- The header pass over the `q` ticks of `rG`. -/
noncomputable def hdrPass : Cmd 0 𝕌 := .loop rG hdrGroup

theorem clean_update {τ : Fin 𝕌 → WTape} (hc : Clean τ) (x : Fin 𝕌) (hx : 64 ≤ x.val) (v : WTape) :
    Clean (Function.update τ x v) := by
  funext i; simp only [Function.comp_apply, Function.update_apply]
  have : ι i ≠ x := by intro e; have := congrArg Fin.val e; simp at this; omega
  simp only [this, ite_false]; exact congrFun hc i

/-- The cost of one header. -/
def hdrCost (p d ℓ D K w eP eS ρ : ℕ) : ℕ :=
  220 * (p + d + D + K + (ρ + 1) + w) + 130 * (w + K) + 8 * (ℓ + eP + eS) + 10000 +
    clen [layerHeader p d (2 ^ ℓ) D (2 ^ eP) (2 ^ eS) K ρ w] + 1 +
    (4 * (layerHeader p d (2 ^ ℓ) D (2 ^ eP) (2 ^ eS) K ρ w).length + 40 + 1 + (5 * (ρ + 1) + 30 + 1 + 5))

/-- The headers of one group: the state with `ρ` headers of the group written. -/
def innerSt (τ : Fin 𝕌 → WTape) (O : List (List Bool)) (K ρ : ℕ) (hs : List (List Bool)) : Fin 𝕌 → WTape :=
  Function.update (Function.update (Function.update τ rF ⟨hs.reverse ++ O, []⟩)
    rO ⟨List.replicate ρ [], List.replicate (K - ρ) []⟩) xQ (reg (ones (ρ + 1)))

set_option maxHeartbeats 32000000 in
theorem runs_hdrStep {p d ℓ D K w eP eS ρ : ℕ} (τ : Fin 𝕌 → WTape) (hc : Clean τ) (hρ : ρ < K)
    (hP : τ iP = reg (ones p)) (hd : τ xP = reg (ones d)) (hL : τ iL = reg (ones ℓ)) (hN : τ kN = reg (ones D))
    (hR : τ lR = reg (ones eP)) (hI : τ lI = reg (ones eS)) (hK : τ kI = reg (ones K)) (hW : τ iW = reg (ones w))
    (hC : τ kC = reg [true]) (hE : τ xE = emp) (hkW : τ kW = emp) (hkR : τ kR = emp) (hG : τ zG = emp)
    (hOut : τ zO = emp) (hS : τ kS = emp) (O hs : List (List Bool)) :
    Runs hdrStep (innerSt τ O K ρ hs)
      (· = innerSt τ O K (ρ + 1) (hs ++ [layerHeader p d (2 ^ ℓ) D (2 ^ eP) (2 ^ eS) K ρ w]))
      (hdrCost p d ℓ D K w eP eS ρ) := by
  set σ := innerSt τ O K ρ hs with hσ
  have hcσ : Clean σ := clean_update (clean_update (clean_update hc rF (by decide) _) rO (by decide) _) xQ
    (by decide) _
  have s1 := runs_layerHdr (p := p) (d := d) (ℓ := ℓ) (D := D) (eP := eP) (eS := eS) (K := K) (ρ := ρ) (w := w)
    σ hcσ (by tsimp [hσ, innerSt, hP]) (by tsimp [hσ, innerSt, hd]) (by tsimp [hσ, innerSt, hL])
    (by tsimp [hσ, innerSt, hN]) (by tsimp [hσ, innerSt, hR]) (by tsimp [hσ, innerSt, hI])
    (by tsimp [hσ, innerSt, hK]) (by tsimp [hσ, innerSt]) (by tsimp [hσ, innerSt, hW])
    (by tsimp [hσ, innerSt, hC]) (by tsimp [hσ, innerSt, hE]) (by tsimp [hσ, innerSt, hkW])
    (by tsimp [hσ, innerSt, hkR]) (by tsimp [hσ, innerSt, hG]) (by tsimp [hσ, innerSt, hOut])
  set H := layerHeader p d (2 ^ ℓ) D (2 ^ eP) (2 ^ eS) K ρ w with hH
  set σ₁ := Function.update σ hO (reg H) with hσ₁
  have s2 := runs_cpy (a := 0) (show zO ≠ rF by decide) σ₁ (by tsimp [hσ₁, reg]) (by tsimp [hσ₁, hσ, innerSt])
  set σ₂ := Function.update (Function.update σ₁ zO ⟨[H], []⟩) rF ⟨H :: (hs.reverse ++ O), []⟩ with hσ₂
  have e2 : Function.update (Function.update σ₁ zO (σ₁ zO).next) rF ((σ₁ rF).put false [(σ₁ zO).cur]) = σ₂ := by
    tsimp [hσ₂, hσ₁, hσ, innerSt, reg]
  rw [e2] at s2
  have s3 := runs_clear' (a := 0) zO σ₂ (T := ⟨[H], []⟩) (by tsimp [hσ₂])
  set σ₃ := Function.update σ₂ zO emp with hσ₃
  have s4a := runs_skp (a := 0) (show xQ ≠ kS by decide) σ₃ (by tsimp [hσ₃, hσ₂, hσ₁, hσ, innerSt, reg])
    (by tsimp [hσ₃, hσ₂, hσ₁, hσ, innerSt, hS])
  set σ₄ := Function.update σ₃ xQ ⟨[ones (ρ + 1)], []⟩ with hσ₄
  have e4 : Function.update σ₃ xQ (σ₃ xQ).next = σ₄ := by tsimp [hσ₄, hσ₃, hσ₂, hσ₁, hσ, innerSt, reg]
  rw [e4] at s4a
  have hq : (σ₃ xQ).cur.length = ρ + 1 := by tsimp [hσ₃, hσ₂, hσ₁, hσ, innerSt, reg]
  have s4a' := s4a.le (show (σ₃ xQ).cur.length + 5 ≤ ρ + 6 by rw [hq])
  have s4b := runs_appendReg (a := 0) (show kC ≠ xQ by decide) σ₄ (u := [true]) (v := ones (ρ + 1)) (M := [])
    (by tsimp [hσ₄, hσ₃, hσ₂, hσ₁, hσ, innerSt, hC]) (by tsimp [hσ₄])
  set σ₅ := Function.update σ₄ xQ ⟨[ones (ρ + 2)], []⟩ with hσ₅
  have e5 : Function.update σ₄ xQ ⟨(ones (ρ + 1) ++ [true]) :: [], []⟩ = σ₅ := by
    rw [hσ₅]; congr 3; simp [ones, List.replicate_succ']
  rw [e5] at s4b
  have s4c := runs_rewind' (a := 0) xQ σ₅ (L := [ones (ρ + 2)]) (R := []) (by tsimp [hσ₅])
  set σ₆ := Function.update σ₅ xQ (reg (ones (ρ + 2))) with hσ₆
  have e6 : Function.update σ₅ xQ ⟨[], [ones (ρ + 2)].reverse ++ []⟩ = σ₆ := by tsimp [hσ₆, reg]
  rw [e6] at s4c
  have hrest : K - ρ = K - (ρ + 1) + 1 := by omega
  have s5 := runs_skp (a := 0) (show rO ≠ kS by decide) σ₆
    (by tsimp [hσ₆, hσ₅, hσ₄, hσ₃, hσ₂, hσ₁, hσ, innerSt, hrest, List.replicate_succ])
    (by tsimp [hσ₆, hσ₅, hσ₄, hσ₃, hσ₂, hσ₁, hσ, innerSt, hS])
  have hc6 : (σ₆ rO).cur.length = 0 := by
    tsimp [hσ₆, hσ₅, hσ₄, hσ₃, hσ₂, hσ₁, hσ, innerSt, hrest, List.replicate_succ]
  have s5' := s5.le (show (σ₆ rO).cur.length + 5 ≤ 5 by rw [hc6])
  refine (Runs.then s1 (Runs.then s2 (Runs.then s3 (Runs.then (Runs.then s4a' (Runs.then s4b s4c)) s5')))).mono
    (fun σ' e => ?_) ?_
  · rw [e]
    funext i; fin_cases i <;> first | rfl | tsimp [hσ₆, hσ₅, hσ₄, hσ₃, hσ₂, hσ₁, hσ, innerSt, hOut, emp,
      hrest, List.replicate_succ, List.replicate_succ', reg]
  · have hz : (σ₁ zO).cur.length = H.length := by tsimp [hσ₁, reg]
    rw [hz]
    simp only [hdrCost, clen, WTape.words, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      List.length_cons, List.length_nil, List.reverse_cons, List.reverse_nil, List.nil_append, List.append_nil,
      length_ones, ← hH]
    omega

/-- The inner loop's cost from bit `ρ`, `r` bits left. -/
def innerCost (p d ℓ D K w eP eS : ℕ) : ℕ → ℕ → ℕ
  | _, 0 => 0
  | ρ, r + 1 => hdrCost p d ℓ D K w eP eS ρ + 2 + innerCost p d ℓ D K w eP eS (ρ + 1) r

theorem runs_hdrInner {p d ℓ D K w eP eS : ℕ} (τ : Fin 𝕌 → WTape) (hc : Clean τ)
    (hP : τ iP = reg (ones p)) (hd : τ xP = reg (ones d)) (hL : τ iL = reg (ones ℓ)) (hN : τ kN = reg (ones D))
    (hR : τ lR = reg (ones eP)) (hI : τ lI = reg (ones eS)) (hK : τ kI = reg (ones K)) (hW : τ iW = reg (ones w))
    (hC : τ kC = reg [true]) (hE : τ xE = emp) (hkW : τ kW = emp) (hkR : τ kR = emp) (hG : τ zG = emp)
    (hOut : τ zO = emp) (hS : τ kS = emp) (O : List (List Bool)) :
    ∀ (r ρ : ℕ) (hs : List (List Bool)), ρ + r = K →
      Runs hdrInner (innerSt τ O K ρ hs)
        (· = innerSt τ O K K (hs ++ (List.range' ρ r).map fun ρ' =>
          layerHeader p d (2 ^ ℓ) D (2 ^ eP) (2 ^ eS) K ρ' w))
        (innerCost p d ℓ D K w eP eS ρ r)
  | 0, ρ, hs, hr => by
    have : ρ = K := by omega
    subst this
    exact Runs.loop_done (by tsimp [innerSt]) (by simp)
  | r + 1, ρ, hs, hr => by
    have s1 := runs_hdrStep (p := p) (d := d) (ℓ := ℓ) (D := D) (K := K) (w := w) (eP := eP) (eS := eS) (ρ := ρ)
      τ hc (by omega) hP hd hL hN hR hI hK hW hC hE hkW hkR hG hOut hS O hs
    have ih := runs_hdrInner τ hc hP hd hL hN hR hI hK hW hC hE hkW hkR hG hOut hS O r (ρ + 1)
      (hs ++ [layerHeader p d (2 ^ ℓ) D (2 ^ eP) (2 ^ eS) K ρ w]) (by omega)
    have := Runs.loop_step (i := rO) (b := hdrStep) (by tsimp [innerSt]; omega)
      (s1.mono (fun σ e => by rw [e]; exact ih) le_rfl)
    refine this.mono (fun σ e => ?_) (by simp [innerCost])
    rw [e]
    simp [List.range'_succ]

/-- The pass state after `c` chunk groups. -/
def passSt (τ : Fin 𝕌 → WTape) (p d ℓ D K w e0 DK q c : ℕ) : Fin 𝕌 → WTape :=
  Function.update (Function.update (Function.update (Function.update τ rF
    ⟨(allHdrs p d ℓ D K w e0 DK c).reverse, []⟩) rG ⟨List.replicate c [], List.replicate (q - c) []⟩)
    lI (reg (ones (c * DK)))) lR (reg (ones (e0 - c * DK)))

/-- The cost of one chunk group. -/
def groupCost (p d ℓ D K w e0 DK c : ℕ) : ℕ :=
  3 * K + 20 + 1 + (2 + 1 + (4 + 1 + (innerCost p d ℓ D K w (e0 - c * DK) (c * DK) 0 K + 1 +
    (2 * K + 2 + 1 + (2 * (K + 2) + 2 + 1 + (c * DK + 5 + 1 + (2 * DK + 10 + 1 + (c * DK + DK + 3 + 1 +
    (4 * (e0 - c * DK) + 4 * DK + 40 + 1 + (2 * (e0 - c * DK + 1) + 2 + 1 + (4 * (e0 - c * DK) + 20 + 1 +
    5)))))))))))

set_option maxHeartbeats 32000000 in
theorem runs_hdrGroup {p d ℓ D K w e0 DK q c : ℕ} (τ : Fin 𝕌 → WTape) (hc : Clean τ) (hcq : c < q)
    (hP : τ iP = reg (ones p)) (hd : τ xP = reg (ones d)) (hL : τ iL = reg (ones ℓ)) (hN : τ kN = reg (ones D))
    (hK : τ kI = reg (ones K)) (hW : τ iW = reg (ones w))
    (hC : τ kC = reg [true]) (hE : τ xE = emp) (hkW : τ kW = emp) (hkR : τ kR = emp) (hG : τ zG = emp)
    (hOut : τ zO = emp) (hS : τ kS = emp) (hO : τ rO = emp) (hQ : τ xQ = emp) (hH : τ kH = emp)
    (hDK : τ kO = reg (ones DK)) :
    Runs hdrGroup (passSt τ p d ℓ D K w e0 DK q c) (· = passSt τ p d ℓ D K w e0 DK q (c + 1))
      (groupCost p d ℓ D K w e0 DK c) := by
  set σ := passSt τ p d ℓ D K w e0 DK q c with hσ
  have hcσ : Clean σ := clean_update (clean_update (clean_update (clean_update hc rF (by decide) _) rG
    (by decide) _) lI (by decide) _) lR (by decide) _
  have s1 := runs_ticksReg (a := 0) (show kI ≠ rO by decide) σ (u := ones K) (by tsimp [hσ, passSt, hK])
    (by tsimp [hσ, passSt, hO])
  set σ₁ := Function.update σ rO ⟨[], List.replicate K []⟩ with hσ₁
  have e1 : Function.update σ rO ⟨[], List.replicate (ones K).length []⟩ = σ₁ := by rw [hσ₁, length_ones]
  rw [e1] at s1
  have s2 := runs_emit (a := 0) [[true]] xQ σ₁ (by tsimp [hσ₁, hσ, passSt, hQ])
  set σ₂ := Function.update σ₁ xQ ⟨[[true]], []⟩ with hσ₂
  have e2 : Function.update σ₁ xQ ⟨[[true]].reverse ++ (σ₁ xQ).left, []⟩ = σ₂ := by
    tsimp [hσ₂, hσ₁, hσ, passSt, hQ]
  rw [e2] at s2
  have s3 := runs_rewind' (a := 0) xQ σ₂ (L := [[true]]) (R := []) (by tsimp [hσ₂])
  have e3 : Function.update σ₂ xQ ⟨[], [[true]].reverse ++ []⟩ =
      innerSt σ (allHdrs p d ℓ D K w e0 DK c).reverse K 0 [] := by
    funext i; fin_cases i <;> tsimp [hσ₂, hσ₁, hσ, innerSt, passSt, reg, ones]
  rw [e3] at s3
  have s4 := runs_hdrInner (p := p) (d := d) (ℓ := ℓ) (D := D) (K := K) (w := w) (eP := e0 - c * DK)
    (eS := c * DK) σ hcσ (by tsimp [hσ, passSt, hP]) (by tsimp [hσ, passSt, hd]) (by tsimp [hσ, passSt, hL])
    (by tsimp [hσ, passSt, hN]) (by tsimp [hσ, passSt]) (by tsimp [hσ, passSt]) (by tsimp [hσ, passSt, hK])
    (by tsimp [hσ, passSt, hW]) (by tsimp [hσ, passSt, hC]) (by tsimp [hσ, passSt, hE])
    (by tsimp [hσ, passSt, hkW]) (by tsimp [hσ, passSt, hkR]) (by tsimp [hσ, passSt, hG])
    (by tsimp [hσ, passSt, hOut]) (by tsimp [hσ, passSt, hS]) (allHdrs p d ℓ D K w e0 DK c).reverse K 0 []
    (by omega)
  set σ₄ := innerSt σ (allHdrs p d ℓ D K w e0 DK c).reverse K K ([] ++ (List.range' 0 K).map fun ρ' =>
    layerHeader p d (2 ^ ℓ) D (2 ^ (e0 - c * DK)) (2 ^ (c * DK)) K ρ' w) with hσ₄
  have s5 := runs_clear' (a := 0) rO σ₄ (T := ⟨List.replicate K [], List.replicate (K - K) []⟩)
    (by tsimp [hσ₄, innerSt])
  set σ₅ := Function.update σ₄ rO emp with hσ₅
  have s6 := runs_clear' (a := 0) xQ σ₅ (T := reg (ones (K + 1))) (by tsimp [hσ₅, hσ₄, innerSt])
  set σ₆ := Function.update σ₅ xQ emp with hσ₆
  have s7 := runs_skp (a := 0) (show lI ≠ kS by decide) σ₆ (by tsimp [hσ₆, hσ₅, hσ₄, hσ, innerSt, passSt, reg])
    (by tsimp [hσ₆, hσ₅, hσ₄, hσ, innerSt, passSt, hS])
  set σ₇ := Function.update σ₆ lI ⟨[ones (c * DK)], []⟩ with hσ₇
  have e7 : Function.update σ₆ lI (σ₆ lI).next = σ₇ := by tsimp [hσ₇, hσ₆, hσ₅, hσ₄, hσ, innerSt, passSt, reg]
  rw [e7] at s7
  have s7' := s7.le (show (σ₆ lI).cur.length + 5 ≤ c * DK + 5 by tsimp [hσ₆, hσ₅, hσ₄, hσ, innerSt, passSt, reg])
  have s8 := runs_appendReg (a := 0) (show kO ≠ lI by decide) σ₇ (u := ones DK) (v := ones (c * DK)) (M := [])
    (by tsimp [hσ₇, hσ₆, hσ₅, hσ₄, hσ, innerSt, passSt, hDK]) (by tsimp [hσ₇])
  set σ₈ := Function.update σ₇ lI ⟨[ones ((c + 1) * DK)], []⟩ with hσ₈
  have e8 : Function.update σ₇ lI ⟨(ones (c * DK) ++ ones DK) :: [], []⟩ = σ₈ := by
    rw [hσ₈, ones_append_ones, Nat.succ_mul]
  rw [e8] at s8
  have s9 := runs_rewind' (a := 0) lI σ₈ (L := [ones ((c + 1) * DK)]) (R := []) (by tsimp [hσ₈])
  set σ₉ := Function.update σ₈ lI (reg (ones ((c + 1) * DK))) with hσ₉
  have e9 : Function.update σ₈ lI ⟨[], [ones ((c + 1) * DK)].reverse ++ []⟩ = σ₉ := by tsimp [hσ₉, reg]
  rw [e9] at s9
  have s10 := runs_dropReg (a := 0) (show lR ≠ kO by decide) (show lR ≠ kH by decide) (show kO ≠ kH by decide) σ₉
    (u := ones (e0 - c * DK)) (v := ones DK) (by tsimp [hσ₉, hσ₈, hσ₇, hσ₆, hσ₅, hσ₄, hσ, innerSt, passSt])
    (by tsimp [hσ₉, hσ₈, hσ₇, hσ₆, hσ₅, hσ₄, hσ, innerSt, passSt, hDK])
    (by tsimp [hσ₉, hσ₈, hσ₇, hσ₆, hσ₅, hσ₄, hσ, innerSt, passSt, hH])
  set σ₁₀ := Function.update σ₉ kH (reg (ones (e0 - (c + 1) * DK))) with hσ₁₀
  have e10 : Function.update σ₉ kH (reg ((ones (e0 - c * DK)).drop (ones DK).length)) = σ₁₀ := by
    rw [hσ₁₀, length_ones, drop_ones, Nat.sub_sub, Nat.succ_mul]
  rw [e10] at s10
  have s11 := runs_clear' (a := 0) lR σ₁₀ (T := reg (ones (e0 - c * DK)))
    (by tsimp [hσ₁₀, hσ₉, hσ₈, hσ₇, hσ₆, hσ₅, hσ₄, hσ, innerSt, passSt])
  set σ₁₁ := Function.update σ₁₀ lR emp with hσ₁₁
  have s12 := runs_regMove (a := 0) (show kH ≠ lR by decide) σ₁₁ (w := ones (e0 - (c + 1) * DK))
    (by tsimp [hσ₁₁, hσ₁₀]) (by tsimp [hσ₁₁])
  set σ₁₂ := Function.update (Function.update σ₁₁ kH emp) lR (reg (ones (e0 - (c + 1) * DK))) with hσ₁₂
  have hq : q - c = q - (c + 1) + 1 := by omega
  have s13 := runs_skp (a := 0) (show rG ≠ kS by decide) σ₁₂
    (by tsimp [hσ₁₂, hσ₁₁, hσ₁₀, hσ₉, hσ₈, hσ₇, hσ₆, hσ₅, hσ₄, hσ, innerSt, passSt, hq, List.replicate_succ])
    (by tsimp [hσ₁₂, hσ₁₁, hσ₁₀, hσ₉, hσ₈, hσ₇, hσ₆, hσ₅, hσ₄, hσ, innerSt, passSt, hS])
  have s13' := s13.le (show (σ₁₂ rG).cur.length + 5 ≤ 5 by
    tsimp [hσ₁₂, hσ₁₁, hσ₁₀, hσ₉, hσ₈, hσ₇, hσ₆, hσ₅, hσ₄, hσ, innerSt, passSt, hq, List.replicate_succ])
  refine (Runs.then s1 (Runs.then s2 (Runs.then s3 (Runs.then s4 (Runs.then s5 (Runs.then s6 (Runs.then s7' (Runs.then s8 (Runs.then s9 (Runs.then s10 (Runs.then s11 (Runs.then s12 s13')))))))))))).mono
    (fun σ' e => ?_) ?_
  · rw [e]
    have hall : (allHdrs p d ℓ D K w e0 DK (c + 1)).reverse =
        ((List.range' 0 K).map fun ρ' => layerHeader p d (2 ^ ℓ) D (2 ^ (e0 - c * DK)) (2 ^ (c * DK)) K ρ' w).reverse ++
          (allHdrs p d ℓ D K w e0 DK c).reverse := by
      simp [allHdrs, groupHdrs, List.range_succ, List.flatMap_append, List.range_eq_range']
    funext i; fin_cases i <;> first | rfl | tsimp [hσ₁₂, hσ₁₁, hσ₁₀, hσ₉, hσ₈, hσ₇, hσ₆, hσ₅, hσ₄, hσ, innerSt,
      passSt, hall, hq, List.replicate_succ, List.replicate_succ', hO, hQ, hH, emp, reg]
  · simp only [groupCost, clen, WTape.words, reg, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      List.length_cons, List.length_nil, List.reverse_nil, List.nil_append, List.append_nil, length_ones,
      List.map_replicate, List.sum_replicate, smul_eq_mul, Nat.sub_self,
      List.replicate_zero, List.reverse_replicate, Nat.zero_add]
    have hstep : e0 - (c + 1) * DK ≤ e0 - c * DK := Nat.sub_le_sub_left (Nat.mul_le_mul_right _ (Nat.le_succ c)) e0
    generalize e0 - (c + 1) * DK = nextExp at hstep ⊢
    have hsucc : (c + 1) * DK = c * DK + DK := Nat.succ_mul c DK
    generalize c * DK = shift at hstep hsucc ⊢
    generalize innerCost p d ℓ D K w (e0 - shift) shift 0 K = inner
    omega

/-- The pass's cost from group `c`, `r` groups left. -/
def passCost (p d ℓ D K w e0 DK : ℕ) : ℕ → ℕ → ℕ
  | _, 0 => 0
  | c, r + 1 => groupCost p d ℓ D K w e0 DK c + 2 + passCost p d ℓ D K w e0 DK (c + 1) r

theorem runs_hdrPass {p d ℓ D K w e0 DK q : ℕ} (τ : Fin 𝕌 → WTape) (hc : Clean τ)
    (hP : τ iP = reg (ones p)) (hd : τ xP = reg (ones d)) (hL : τ iL = reg (ones ℓ)) (hN : τ kN = reg (ones D))
    (hK : τ kI = reg (ones K)) (hW : τ iW = reg (ones w))
    (hC : τ kC = reg [true]) (hE : τ xE = emp) (hkW : τ kW = emp) (hkR : τ kR = emp) (hG : τ zG = emp)
    (hOut : τ zO = emp) (hS : τ kS = emp) (hO : τ rO = emp) (hQ : τ xQ = emp) (hH : τ kH = emp)
    (hDK : τ kO = reg (ones DK)) :
    ∀ (r c : ℕ), c + r = q →
      Runs hdrPass (passSt τ p d ℓ D K w e0 DK q c) (· = passSt τ p d ℓ D K w e0 DK q q)
        (passCost p d ℓ D K w e0 DK c r)
  | 0, c, hr => by
    have : c = q := by omega
    subst this
    exact Runs.loop_done (by tsimp [passSt]) rfl
  | r + 1, c, hr => by
    have s1 := runs_hdrGroup (p := p) (d := d) (ℓ := ℓ) (D := D) (K := K) (w := w) (e0 := e0) (DK := DK) (q := q)
      (c := c) τ hc (by omega) hP hd hL hN hK hW hC hE hkW hkR hG hOut hS hO hQ hH hDK
    have ih := runs_hdrPass (p := p) (d := d) (ℓ := ℓ) (D := D) (K := K) (w := w) (e0 := e0) (DK := DK) (q := q)
      τ hc hP hd hL hN hK hW hC hE hkW hkR hG hOut hS hO hQ hH hDK r (c + 1) (by omega)
    have := Runs.loop_step (i := rG) (b := hdrGroup) (by tsimp [passSt]; omega)
      (s1.mono (fun σ e => by rw [e]; exact ih) le_rfl)
    exact this.mono (fun σ e => e) (by simp [passCost])

theorem passSt_zero {p d ℓ D K w e0 DK q : ℕ} (τ : Fin 𝕌 → WTape) (hF : τ rF = emp)
    (hG : τ rG = ⟨[], List.replicate q []⟩) (hI : τ lI = reg []) (hR : τ lR = reg (ones e0)) :
    passSt τ p d ℓ D K w e0 DK q 0 = τ := by
  funext i
  simp only [passSt, Function.update_apply]
  split_ifs with h1 h2 h3 h4 <;> subst_vars <;> simp_all [allHdrs, emp, ones]

end ScriptHdr

end IntegerMultBounds.Schoenhage
