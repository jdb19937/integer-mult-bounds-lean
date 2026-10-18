module

public import IntegerMultBounds.MathlibTM2.Node.CompactFactorBasis
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import IntegerMultBounds.MathlibTM2.Node.Factor

/-! Actual compact factor sequence with generic child-call semantics. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds IntegerMultBounds.Networks IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Layer
open IntegerMultBounds.MathlibTM2.Node hiding LReg
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
open CompactGadgetReservationShape (Shape)
noncomputable section
variable {Q Ka : ℕ} {U P : Type} (body : P → Pr P (nT CompactBReg) Q (prime+Ka) U)
local macro "fupd" : tactic => `(tactic| (simp only [Function.update_apply, reg_inj, reduceCtorEq,
  ↓reduceIte, eq_self_iff_true, LReg.sc.injEq, LReg.wire.injEq, LReg.wtmp.injEq, LReg.bc.injEq,
  LReg.ph.injEq, LReg.lf.injEq, Fin.reduceEq, Fin.isValue, movedR, List.map_id, id]) <;> try rfl)

noncomputable def compactFactorProg (hQ : compactRuntimeStates ≤ Q)
    (cp : Pr P (nT CompactBReg) Q (prime + Ka) U) (ds : ComplexFramedExecution.Directions)
    (fw : NWire) (g : ZMod 4 × BinaryWalsh.Address m) : Pr P (nT CompactBReg) Q (prime + Ka) U :=
  if h : ∃ i, g.2 i = 1 then
    .seq (saveDiv NW .rows)
    (.seq (saveDiv m .L)
    (.seq (compactBasisW hQ fw g.2 (Fin.find _ h))
    (.seq (condConj g.1 fw)
    (.seq (childCall fw (Fin.find _ h) (gateCount (program ds)) (factorCount (program ds)) cp)
    (.seq (condConj g.1 fw)
    (.seq (compactBasisW hQ fw g.2 (Fin.find _ h))
    (.seq (restoreMul m .L)
    (.seq (restoreMul NW .rows)
      (shiftTc (otherW fw))))))))))
  else shiftTc allW

noncomputable def compactFactorCost (_T : ℕ) (ds : ComplexFramedExecution.Directions)
    (j u K _ρ _a₀ R₀ n r w : ℕ) (g : ZMod 4 × BinaryWalsh.Address m) (cc : ℕ) (basisBound : Fin m → ℕ) : ℕ :=
  if h : ∃ i, g.2 i = 1 then
    (8 * (NW * rowsAt R₀ j) + 8) + (8 * (K * bits u (j + 1)) + 8) +
      basisBound (Fin.find _ h) +
      (conjCost (rowsAt R₀ j) n r w + 1) +
      childCost (rowsAt R₀ j * 2 ^ n * (r * w)) (gateCount (program ds))
        (factorCount (program ds)) u j (K * bits u j) (Fin.find _ h) (expZ u ds j) cc +
      (conjCost (rowsAt R₀ j) n r w + 1) +
      basisBound (Fin.find _ h) +
      (6 * (K * bits u j) + 6 * (K * bits u (j + 1)) + 13) +
      (6 * rowsAt R₀ j + 6 * (NW * rowsAt R₀ j) + 13) +
      shiftCost NB (rowsAt R₀ j) n r w (expZ u ds j)
  else shiftCost NB (rowsAt R₀ j) n r w (expZ u ds j)

/-- The complete factor, using the computed compact basis on both sides of the
existing child call. The global reservation is fixed and its counters persist. -/
theorem compactFactorProg_spec (hQ : compactRuntimeStates ≤ Q)
    (cp : Pr P (nT CompactBReg) Q (prime+Ka) U) (ds : ComplexFramedExecution.Directions)
    (hA : 14 ≤ prime+Ka) {shape : Shape} {R₀ j u ρ a₀ n o r w left right : ℕ}
    (hr : 1 ≤ r) (hw : 1 ≤ w) (hu : 1 ≤ u) (hR₀ : 1 ≤ R₀)
    (layout : CompactRecursiveLayout shape n a₀ (bits u j) ρ left right)
    (hGuard : 1 ≤ shape.guard) (hGuardChunk : shape.guard+1 ≤ shape.chunk)
    (hRecord : shape.bits+1 ≤ shape.payload) (hPayload : shape.payload=2^o*(3*(r*w))) (D : ℕ)
    (hp : ∀ x y (hxy : x≠y),1<bits u j → ActivePrefixStageRuntimeData.Packed
      (compactSlotComputedInputs layout x y hxy (rowsAt R₀ j) hGuard hGuardChunk (rowsAt_pos hR₀ j) hRecord) D)
    (hfit : ∀ i<bits u (j+1),(o+a₀)+ρ+shape.chunk*i<o+n)
    (hfitL : (o+a₀)+shape.chunk*bits u (j+1) ≤ o+n)
    (hTw : expZ u ds j ≤ w) (fw : NWire) (g : ZMod 4 × BinaryWalsh.Address m) (cc : ℕ)
    (hcall : ∀ (hs : ∃ i,g.2 i=1)
      (hfit' : ∀ i<bits u j,(o+a₀)+(Fin.find _ hs : ℕ)*(shape.chunk*bits u j)+ρ+shape.chunk*i<o+n),
      CallSpec body cp (compactBasisRest shape o r) ds R₀ j u shape.chunk ρ
        ((o+a₀)+(Fin.find _ hs : ℕ)*(shape.chunk*bits u j)) (shape.chunk*bits u j)
        (o+n) r w hfit' cc) :
    FactorSpecL body (compactFactorProg hQ cp ds fw g) (compactBasisRest shape o r)
      j u shape.chunk ρ (o+a₀) (shape.chunk*bits u (j+1)) (rowsAt R₀ (j+1)) (o+n) r w
      (k:=bits u j) (actMap (o+a₀) ρ shape.chunk (bits u (j+1)) (o+n) hfit)
      (fun z => layerZ u ds R₀ j fun c => actMap (o+a₀) ρ shape.chunk (bits u (j+1)) (o+n) hfit (bitIdx z c))
      (expZ u ds j) fw g
      (compactFactorCost (nT CompactBReg) ds j u shape.chunk ρ (o+a₀) R₀ (o+n) r w g cc
        (compactFactorBasisCost layout hGuard hGuardChunk (rowsAt_pos hR₀ j) hRecord D hp (nT CompactBReg) Ka o r w g.2)) := by
  intro B v S hL hN hB
  let basisBound := compactFactorBasisCost layout hGuard hGuardChunk (rowsAt_pos hR₀ j) hRecord D hp (nT CompactBReg) Ka o r w g.2
  set Lc := shape.chunk * bits u j with hLc
  set Tc := expZ u ds j with hTcd
  set e := actMap (o+a₀) ρ shape.chunk (bits u (j + 1)) (o+n) hfit with he_def
  have hs : ∀ i, S.R (reg (.sc i)) = [] := fun i => hN.rest (.sc i) (by simp)
  have hrs : ∀ x : LReg CompactBReg, (∀ y, x ≠ .wire y) → x ≠ .Tc →
      restSpec (compactBasisRest shape o r) (o+n) r w x (S.R (reg x)) := fun x h1 h2 =>
    hN.rest x (by rintro (⟨y, hy⟩ | hy); exacts [h1 y hy, h2 hy])
  have hTcS : (S.R (reg .Tc)).length = Tc := hN.tc
  have hwS : (S.R (reg .w)).length = w := hN.par .w
  by_cases hpiv : ∃ i, g.2 i = 1
  swap
  · -- no pivot: every wire is multiplied by `2 ^ Tc`
    obtain ⟨v₁, c₁, R₁, hu₁, hc₁, he₁, hw₁, ho₁⟩ := shiftTc_exec body hw hTw allW nodup_allW B v S
      hwS hTcS (hs 0) (hs 1) (hrs .tS (by simp) (by simp)) (hrs .tR (by simp) (by simp))
      (fun x _ => hrs (.wtmp x) (by simp) (by simp)) (fun x _ => hB x)
    refine ⟨v₁, c₁, R₁, hu₁, ?_, ?_, ?_, ?_⟩
    · simp only [compactFactorCost, hpiv, ↓reduceDIte]; rw [← length_allW]; exact hc₁
    · simpa only [compactFactorProg, hpiv, ↓reduceDIte] using he₁
    · intro x
      rw [hw₁ x (mem_allW x)]
      congr 1
      by_cases hx : x = fw
      · subst hx; simp only [execM, ↓reduceIte, facM, hpiv, ↓reduceDIte]
      · simp only [execM, hx, ↓reduceIte]
    · intro i hi
      exact ho₁ i (fun x _ => hi x)
  -- the pivot
  set s := Fin.find _ hpiv with hsdef
  have hvs : g.2 s = 1 := Fin.find_spec hpiv
  have hk1 : 1 ≤ bits u j := bits_pos hu j
  have hRw1 : 1 ≤ (rowsAt R₀ j) := rowsAt_pos hR₀ j
  have hrw : 1 ≤ r * w := Nat.mul_pos hr hw
  have hm1 : 1 ≤ m := by norm_num [m]
  have hL₁ : shape.chunk * bits u (j + 1) = m * Lc := by
    rw [hLc, show bits u (j + 1) = m * bits u j from rfl]; ring
  have hfitm : (o+a₀) + m * Lc ≤ (o+n) := by rw [← hL₁]; exact hfitL
  have he : ∀ i : Fin (m * bits u j), (e i : ℕ) = (o+a₀) + ρ + shape.chunk * i := fun i => rfl
  have hfit' : ∀ i < bits u j, (o+a₀) + (s : ℕ) * Lc + ρ + shape.chunk * i < (o+n) := by
    intro i hi
    have hs' := s.2
    have h1 : i + bits u j * s < bits u (j + 1) := by
      show i + bits u j * s < m * bits u j
      nlinarith
    have := hfit _ h1
    have h2 : shape.chunk * (i + bits u j * s) = shape.chunk * i + s * Lc := by rw [hLc]; ring
    omega
  have heS : (fun c => e (bitIdx s c)) = actMap ((o+a₀) + (s : ℕ) * Lc) ρ shape.chunk (bits u j) (o+n) hfit' := by
    funext c
    apply Fin.ext
    simp only [he_def, actMap, bitIdx, finProdFinEquiv_apply_val, hLc]
    ring
  set rows₀ := S.R (reg .rows) with hrows₀
  set L₀ := S.R (reg .L) with hL₀
  set park₀ := S.R (reg .park) with hpark₀
  have hrows₀l : rows₀.length = NW * (rowsAt R₀ j) := hN.par .rows
  have hL₀l : L₀.length = m * Lc := (hN.par .L).trans hL₁
  -- save `rows` and `L`
  obtain ⟨v₁, c₁, hu₁, hc₁, he₁⟩ := saveDiv_exec body one_le_NW (X := .rows) (by simp) (by simp)
    (by simp) v S (hs 0) (hs 1)
  set R₁ := Function.update (Function.update S.R (reg .park) (rows₀.reverse ++ park₀))
    (reg .rows) (List.replicate (rows₀.length / NW) tick) with hR₁
  obtain ⟨v₂, c₂, hu₂, hc₂, he₂⟩ := saveDiv_exec body hm1 (X := .L) (by simp) (by simp)
    (by simp) v₁ { S with R := R₁ } (by dsimp only; rw [hR₁]; fupd; exact hs 0)
    (by dsimp only; rw [hR₁]; fupd; exact hs 1)
  dsimp only at hc₂ he₂
  have h1L : R₁ (reg .L) = L₀ := by rw [hR₁]; fupd
  have h1p : R₁ (reg .park) = rows₀.reverse ++ park₀ := by rw [hR₁]; fupd
  rw [h1L, h1p] at he₂
  rw [h1L] at hc₂
  set R₂ := Function.update (Function.update R₁ (reg .park) (L₀.reverse ++
    (rows₀.reverse ++ park₀))) (reg .L) (List.replicate (L₀.length / m) tick) with hR₂
  have h2o : ∀ x : LReg CompactBReg, x ≠ .park → x ≠ .L → x ≠ .rows → R₂ (reg x) = S.R (reg x) := by
    intro x h1 h2 h3
    rw [hR₂, Function.update_of_ne (reg_ne h2), Function.update_of_ne (reg_ne h1), hR₁,
      Function.update_of_ne (reg_ne h3), Function.update_of_ne (reg_ne h1)]
  have h2L : R₂ (reg .L) = List.replicate Lc tick := by
    rw [hR₂, Function.update_self, hL₀l, Nat.mul_div_cancel_left _ (by norm_num [m])]
  have h2r : R₂ (reg .rows) = List.replicate (rowsAt R₀ j) tick := by
    rw [hR₂]; fupd; rw [hR₁]; fupd
    rw [hrows₀l, Nat.mul_div_cancel_left _ (Nat.pos_of_neZero NW)]
  have h2p : R₂ (reg .park) = L₀.reverse ++ (rows₀.reverse ++ park₀) := by rw [hR₂]; fupd
  -- the first basis change
  have hpar2 : ∀ x : LReg CompactBReg, x ∈ [.K, .ρ, .a₀, .n, .rw, .w, .u, .lev] →
      R₂ (reg x) = S.R (reg x) := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    apply h2o <;> rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  obtain ⟨v₃, c₃, hu₃, hc₃, he₃⟩ := compactBasisW_factor_exec body hQ (by omega)
    layout hGuard hGuardChunk hRw1 hRecord hPayload D hp he fw g.2 s hvs (B fw) v₂ {S with R:=R₂} hL
    (by dsimp only; rw [h2o _ (by simp) (by simp) (by simp)]; exact hB fw)
    (by dsimp only; rw [hpar2 .K (by simp)]; exact hN.par .K)
    (by dsimp only; rw [hpar2 .ρ (by simp)]; exact hN.par .ρ)
    (by dsimp only; rw [hpar2 .a₀ (by simp)]; exact hN.par .a₀)
    (by dsimp only; rw [h2L,List.length_replicate])
    (by dsimp only; rw [h2r,List.length_replicate])
    (by dsimp only; rw [hpar2 .n (by simp)]; exact hN.par .n)
    (by dsimp only; rw [hpar2 .rw (by simp)]; exact hN.par .rw)
    (by dsimp only; rw [hpar2 .w (by simp)]; exact hN.par .w)
    (fun y => by dsimp only; rw [h2o _ (by simp) (by simp) (by simp)]; exact hrs (.bc y) (by simp) (by simp))
    (by dsimp only; rw [h2o _ (by simp) (by simp) (by simp)]; exact hrs .tmp (by simp) (by simp))
  set Z₁ := pullM e (basisMap g.2 s) (B fw) with hZ₁
  set R₃ := Function.update R₂ (reg (.wire fw)) (encZ (prime + Ka) w Z₁) with hR₃
  have h3o : ∀ x : LReg CompactBReg, x ≠ .park → x ≠ .L → x ≠ .rows → x ≠ .wire fw →
      R₃ (reg x) = S.R (reg x) := fun x h1 h2 h3 h4 => by
    rw [hR₃, Function.update_of_ne (reg_ne h4), h2o x h1 h2 h3]
  -- the first conjugation
  obtain ⟨v₄, c₄, hu₄, hc₄, he₄⟩ := condConj_exec body (by omega) hw g.1 fw Z₁ v₃
    { S with R := R₃ }
    (by dsimp only; rw [h3o _ (by simp) (by simp) (by simp) (by simp)]
        exact hwS ▸ hrs .ctr (by simp) (by simp))
    (by dsimp only
        rw [h3o _ (by simp) (by simp) (by simp) (by simp)]
        exact hrs .tmp (by simp) (by simp))
    (by dsimp only
        rw [h3o _ (by simp) (by simp) (by simp) (by simp)]
        exact hrs (.wtmp fw) (by simp) (by simp))
    (by dsimp only; rw [hR₃, Function.update_self])
  set Z₂ := cconj g.1 Z₁ with hZ₂
  set R₄ := Function.update R₃ (reg (.wire fw)) (encZ (prime + Ka) w Z₂) with hR₄
  have hR₄' : R₄ = Function.update R₂ (reg (.wire fw)) (encZ (prime + Ka) w Z₂) := by
    rw [hR₄, hR₃, Function.update_idem]
  have h4o : ∀ x : LReg CompactBReg, x ≠ .park → x ≠ .L → x ≠ .rows → (∀ y, x ≠ .wire y) →
      R₄ (reg x) = S.R (reg x) := fun x h1 h2 h3 h4 => by
    rw [hR₄', Function.update_of_ne (reg_ne (h4 fw)), h2o x h1 h2 h3]
  -- the child call
  set B' := Function.update B fw Z₂ with hB'
  set G := gateCount (program ds) with hG
  set F := factorCount (program ds) with hF
  obtain ⟨v₅, c₅, hu₅, hc₅, he₅⟩ := childCall_exec body ds G F cp hfit' (hcall hpiv hfit') fw B'
    v₄ { S with R := R₄ } hL
    (by
      intro x
      by_cases hxL : x = .L
      · subst hxL; show (R₄ (reg .L)).length = Lc
        rw [hR₄', Function.update_of_ne (reg_ne (by simp)), h2L, List.length_replicate]
      by_cases hxr : x = .rows
      · subst hxr; show (R₄ (reg .rows)).length = (rowsAt R₀ j)
        rw [hR₄', Function.update_of_ne (reg_ne (by simp)), h2r, List.length_replicate]
      by_cases hxp : x = .park
      · subst hxp; exact trivial
      by_cases hxw : ∃ y, x = .wire y
      · obtain ⟨y, rfl⟩ := hxw; exact trivial
      push Not at hxw
      have h := hN.par x
      dsimp only
      rw [← h4o x hxp hxL hxr hxw] at h
      cases x <;> first | exact trivial | exact absurd rfl hxL | exact absurd rfl hxr | exact h)
    (by
      intro x hx
      have hxw : ∀ y, x ≠ .wire y := fun y h => hx (Or.inl ⟨y, h⟩)
      have hxT : x ≠ .Tc := fun h => hx (Or.inr h)
      by_cases hxL : x = .L
      · subst hxL; exact trivial
      by_cases hxr : x = .rows
      · subst hxr; exact trivial
      by_cases hxp : x = .park
      · subst hxp; exact trivial
      dsimp only
      rw [h4o x hxp hxL hxr hxw]
      exact hrs x hxw hxT)
    (by dsimp only; rw [h4o _ (by simp) (by simp) (by simp) (by simp)]; exact hN.io)
    (by dsimp only; rw [h4o _ (by simp) (by simp) (by simp) (by simp), hTcS, hTcd,
          expZ_eq_expSeq])
    (fun x => by
      dsimp only
      by_cases hx : x = fw
      · subst hx; rw [hR₄', Function.update_self, hB', Function.update_self]
      · rw [hR₄', Function.update_of_ne (reg_ne (by simp [hx])), h2o _ (by simp) (by simp)
          (by simp), hB x, hB', Function.update_of_ne hx])
  dsimp only at he₅ hc₅
  have hB'fw : B' fw = Z₂ := by rw [hB', Function.update_self]
  rw [hB'fw] at he₅
  set Z₃ := layerZ u ds R₀ j (actMap ((o+a₀) + (s : ℕ) * Lc) ρ shape.chunk (bits u j) (o+n) hfit') Z₂ with hZ₃
  set R₅ := Function.update R₄ (reg (.wire fw)) (encZ (prime + Ka) w Z₃) with hR₅
  have hR₅' : R₅ = Function.update R₂ (reg (.wire fw)) (encZ (prime + Ka) w Z₃) := by
    rw [hR₅, hR₄', Function.update_idem]
  -- the second conjugation
  obtain ⟨v₆, c₆, hu₆, hc₆, he₆⟩ := condConj_exec body (by omega) hw g.1 fw Z₃ v₅
    { S with R := R₅ }
    (by dsimp only
        rw [hR₅', Function.update_of_ne (reg_ne (by simp)), h2o _ (by simp) (by simp) (by simp)]
        exact hwS ▸ hrs .ctr (by simp) (by simp))
    (by dsimp only
        rw [hR₅', Function.update_of_ne (reg_ne (by simp)), h2o _ (by simp) (by simp) (by simp)]
        exact hrs .tmp (by simp) (by simp))
    (by dsimp only
        rw [hR₅', Function.update_of_ne (reg_ne (by simp)), h2o _ (by simp) (by simp) (by simp)]
        exact hrs (.wtmp fw) (by simp) (by simp))
    (by dsimp only; rw [hR₅', Function.update_self])
  set Z₄ := cconj g.1 Z₃ with hZ₄
  set R₆ := Function.update R₅ (reg (.wire fw)) (encZ (prime + Ka) w Z₄) with hR₆
  have hR₆' : R₆ = Function.update R₂ (reg (.wire fw)) (encZ (prime + Ka) w Z₄) := by
    rw [hR₆, hR₅', Function.update_idem]
  -- the second basis change
  obtain ⟨v₇, c₇, hu₇, hc₇, he₇⟩ := compactBasisW_factor_exec body hQ (by omega)
    layout hGuard hGuardChunk hRw1 hRecord hPayload D hp he fw g.2 s hvs Z₄ v₆ {S with R:=R₆} hL
    (by dsimp only; rw [hR₆',Function.update_self])
    (by dsimp only; rw [hR₆',Function.update_of_ne (reg_ne (by simp)),hpar2 .K (by simp)]; exact hN.par .K)
    (by dsimp only; rw [hR₆',Function.update_of_ne (reg_ne (by simp)),hpar2 .ρ (by simp)]; exact hN.par .ρ)
    (by dsimp only; rw [hR₆',Function.update_of_ne (reg_ne (by simp)),hpar2 .a₀ (by simp)]; exact hN.par .a₀)
    (by dsimp only; rw [hR₆',Function.update_of_ne (reg_ne (by simp)),h2L,List.length_replicate])
    (by dsimp only; rw [hR₆',Function.update_of_ne (reg_ne (by simp)),h2r,List.length_replicate])
    (by dsimp only; rw [hR₆',Function.update_of_ne (reg_ne (by simp)),hpar2 .n (by simp)]; exact hN.par .n)
    (by dsimp only; rw [hR₆',Function.update_of_ne (reg_ne (by simp)),hpar2 .rw (by simp)]; exact hN.par .rw)
    (by dsimp only; rw [hR₆',Function.update_of_ne (reg_ne (by simp)),hpar2 .w (by simp)]; exact hN.par .w)
    (fun y => by dsimp only; rw [hR₆',Function.update_of_ne (reg_ne (by simp)),h2o _ (by simp) (by simp) (by simp)]; exact hrs (.bc y) (by simp) (by simp))
    (by dsimp only; rw [hR₆',Function.update_of_ne (reg_ne (by simp)),h2o _ (by simp) (by simp) (by simp)]; exact hrs .tmp (by simp) (by simp))
  set Z₅ := pullM e (basisMap g.2 s) Z₄ with hZ₅
  set R₇ := Function.update R₆ (reg (.wire fw)) (encZ (prime + Ka) w Z₅) with hR₇
  have hR₇' : R₇ = Function.update R₂ (reg (.wire fw)) (encZ (prime + Ka) w Z₅) := by
    rw [hR₇, hR₆', Function.update_idem]
  -- restore `L` and `rows`
  obtain ⟨v₈, c₈, hu₈, hc₈, he₈⟩ := restoreMul_exec body (c := m) (X := .L) (by simp) (by simp)
    (by simp) L₀.reverse (rows₀.reverse ++ park₀) v₇ { S with R := R₇ }
    (by dsimp only
        rw [hR₇', Function.update_of_ne (reg_ne (by simp)), h2o _ (by simp) (by simp) (by simp)]
        exact hrs .lenctr (by simp) (by simp))
    (by dsimp only
        rw [hR₇', Function.update_of_ne (reg_ne (by simp)), h2o _ (by simp) (by simp) (by simp)]
        exact hs 1)
    (by dsimp only; rw [hR₇', Function.update_of_ne (reg_ne (by simp)), h2L, List.length_replicate,
          List.length_reverse, hL₀l])
    (by dsimp only; rw [hR₇', Function.update_of_ne (reg_ne (by simp)), h2p])
  dsimp only at he₈ hc₈
  set R₈ := Function.update (Function.update R₇ (reg .park) (rows₀.reverse ++ park₀)) (reg .L)
    L₀.reverse.reverse with hR₈
  obtain ⟨v₉, c₉, hu₉, hc₉, he₉⟩ := restoreMul_exec body (c := NW) (X := .rows) (by simp)
    (by simp) (by simp) rows₀.reverse park₀ v₈ { S with R := R₈ }
    (by dsimp only
        rw [hR₈]
        fupd
        rw [hR₇']
        fupd
        rw [h2o _ (by simp) (by simp) (by simp)]
        exact hrs .lenctr (by simp) (by simp))
    (by dsimp only
        rw [hR₈]
        fupd
        rw [hR₇']
        fupd
        rw [h2o _ (by simp) (by simp) (by simp)]
        exact hs 1)
    (by dsimp only; rw [hR₈]; fupd; rw [hR₇']; fupd; rw [h2r, List.length_replicate,
          List.length_reverse, hrows₀l])
    (by dsimp only; rw [hR₈]; fupd)
  dsimp only at he₉ hc₉
  set R₉ := Function.update (Function.update R₈ (reg .park) park₀) (reg .rows)
    rows₀.reverse.reverse with hR₉
  have hR₉' : R₉ = Function.update S.R (reg (.wire fw)) (encZ (prime + Ka) w Z₅) := by
    funext k
    by_cases h1 : k = reg .rows
    · subst h1; rw [hR₉]; fupd; rw [List.reverse_reverse]
    by_cases h2 : k = reg .park
    · subst h2; rw [hR₉]; fupd
    by_cases h3 : k = reg .L
    · subst h3; rw [hR₉]; fupd; rw [hR₈]; fupd; rw [List.reverse_reverse]
    rw [hR₉, Function.update_of_ne h1, Function.update_of_ne h2, hR₈, Function.update_of_ne h3,
      Function.update_of_ne h2, hR₇', Function.update_apply, Function.update_apply]
    split_ifs with h4
    · rfl
    · obtain ⟨x, rfl⟩ := (regEquiv CompactBReg).surjective k
      exact h2o x (fun h => h2 (by rw [h]; rfl)) (fun h => h3 (by rw [h]; rfl))
        (fun h => h1 (by rw [h]; rfl))
  -- the other wires
  obtain ⟨v₁₀, c₁₀, R₁₀, hu₁₀, hc₁₀, he₁₀, hw₁₀, ho₁₀⟩ := shiftTc_exec body hw hTw (otherW fw)
    (nodup_otherW fw) B v₉ { S with R := R₉ }
    (by dsimp only; rw [hR₉', Function.update_of_ne (reg_ne (by simp))]; exact hwS)
    (by dsimp only; rw [hR₉', Function.update_of_ne (reg_ne (by simp))]; exact hTcS)
    (by dsimp only; rw [hR₉', Function.update_of_ne (reg_ne (by simp))]; exact hs 0)
    (by dsimp only; rw [hR₉', Function.update_of_ne (reg_ne (by simp))]; exact hs 1)
    (by dsimp only
        rw [hR₉', Function.update_of_ne (reg_ne (by simp))]
        exact hrs .tS (by simp) (by simp))
    (by dsimp only
        rw [hR₉', Function.update_of_ne (reg_ne (by simp))]
        exact hrs .tR (by simp) (by simp))
    (fun x _ => by
      dsimp only; rw [hR₉', Function.update_of_ne (reg_ne (by simp))]
      exact hrs (.wtmp x) (by simp) (by simp))
    (fun x hx => by
      dsimp only
      rw [hR₉', Function.update_of_ne (reg_ne (by simp [mem_otherW.1 hx])), hB x])
  have ho₁₀' : ∀ k, (∀ x ∈ otherW fw, k ≠ reg (.wire x)) → R₁₀ k = R₉ k := ho₁₀
  have he := Exec.seq he₁ (Exec.seq he₂ (Exec.seq he₃ (Exec.seq he₄ (Exec.seq he₅
    (Exec.seq he₆ (Exec.seq he₇ (Exec.seq he₈ (Exec.seq he₉ he₁₀))))))))
  have he' : Exec body (compactFactorProg hQ cp ds fw g) (mk v S)
      (c₁ + (c₂ + (c₃ + (c₄ + (c₅ + (c₆ + (c₇ + (c₈ + (c₉ + c₁₀)))))))))
      (mk v₁₀ { S with R := R₁₀ }) := by
    simpa only [compactFactorProg, hpiv, ↓reduceDIte] using he
  refine ⟨v₁₀, _, R₁₀, by rw [hu₁₀, hu₉, hu₈, hu₇, hu₆, hu₅, hu₄, hu₃, hu₂, hu₁], ?_, he', ?_, ?_⟩
  · -- the step bound
    have hc₁₀' := hc₁₀.trans (shiftCost_mono (length_otherW_le fw))
    have hc₅' : c₅ ≤ childCost ((rowsAt R₀ j) * 2 ^ (o+n) * (r * w)) G F u j Lc s Tc cc := by
      rw [hTcd, expZ_eq_expSeq]; exact hc₅
    rw [hrows₀l] at hc₁
    rw [hR₇', Function.update_of_ne (reg_ne (by simp)), h2L, List.length_replicate,
      List.length_reverse, hL₀l] at hc₈
    rw [hR₈] at hc₉
    simp only [Function.update_apply, reg_inj, reduceCtorEq, ↓reduceIte, hR₇'] at hc₉
    rw [h2r, List.length_replicate, List.length_reverse, hrows₀l] at hc₉
    have hfc : compactFactorCost (nT CompactBReg) ds j u shape.chunk ρ (o+a₀) R₀ (o+n) r w g cc basisBound =
        (8 * (NW * (rowsAt R₀ j)) + 8) + (8 * (shape.chunk * bits u (j + 1)) + 8) +
        basisBound s +
        (conjCost (rowsAt R₀ j) (o+n) r w + 1) +
        childCost ((rowsAt R₀ j) * 2 ^ (o+n) * (r * w)) G F u j Lc s Tc cc +
        (conjCost (rowsAt R₀ j) (o+n) r w + 1) +
        basisBound s +
        (6 * Lc + 6 * (shape.chunk * bits u (j + 1)) + 13) +
        (6 * (rowsAt R₀ j) + 6 * (NW * (rowsAt R₀ j)) + 13) +
        shiftCost NB (rowsAt R₀ j) (o+n) r w Tc := by
      simp only [compactFactorCost, hpiv, ↓reduceDIte]; rfl
    rw [hfc, hL₁]
    rw [hL₀l] at hc₂
    change c₃ ≤ basisBound s at hc₃
    change c₇ ≤ basisBound s at hc₇
    omega
  · -- the wires
    intro x
    by_cases hx : x = fw
    · have hfw : ∀ y ∈ otherW fw, reg (BReg := CompactBReg) (.wire x) ≠ reg (.wire y) := by
        intro y hy h
        rw [reg_inj, LReg.wire.injEq] at h
        exact mem_otherW.1 hy (h ▸ hx)
      rw [ho₁₀' _ hfw, hR₉', hx, Function.update_self]
      apply congrArg (encZ (prime + Ka) w)
      simp only [execM, ↓reduceIte]
      rw [facM_pivot e _ Tc g hpiv, ← hsdef]
      simp only [hZ₅, hZ₄, hZ₃, hZ₂, hZ₁, heS]
    · rw [hw₁₀ x (mem_otherW.2 hx)]
      apply congrArg (encZ (prime + Ka) w)
      simp only [execM, hx, ↓reduceIte]
  · intro i hi
    rw [ho₁₀' i (fun x _ => hi x), hR₉', Function.update_of_ne (hi fw)]

end
end IntegerMultBounds.MathlibTM2.LayerMachine
