module

public import IntegerMultBounds.MathlibTM2.Node.CompactFactorR
public import IntegerMultBounds.MathlibTM2.Node.CompactLayerProc
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

/-!
# The rounded compact layer

The compact layer procedure with rounded children: the node body runs without the child exponent
(`nodeBodyR`: no `tcBuild`, `Tc` stays empty), the factors are `compactFactorProgR`, and every
child call is followed by the truncation `truncP` by `2 ^ scaleR u ds j`.

**Semantics** (`layerRW`). The tape computes `layerR` (`Layer/LayerR.lean`) with every child
result replaced by its symmetric representative modulo `2 ^ w` before the truncation:
`layerRW w u ds R₀ (j + 1) e f` is the node `nodeM e child 0 ds` with
`child s g = tdivArr (scaleR u ds j) (symArr w (layerRW … j (e ∘ bitIdx s) g))`.
It is `layerR` whenever the child results fit `w` signed bits (`symZ_eq`).

**Main theorem** (`compactLayerR_exec`, by induction on `j`). With `scaleR u ds i < w` for every
child level `i < j` and the layout conditions `CompactLayerReady`, the call of the layer procedure
satisfies `CallSpecF` with result `layerRW w u ds R₀ j (actMap …)` within
`compactLayerCostR … j a` steps.
-/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds IntegerMultBounds.Networks IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Layer
open IntegerMultBounds.MathlibTM2.Node hiding LReg
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
open CompactGadgetReservationShape (Shape)

/-! ### The node body without the child exponent -/

section NodeR

variable {BReg : Type} [Fintype BReg] {Q A : ℕ} {U P : Type}
  (body : P → Pr P (nT BReg) Q A U)

/-- The node body with an empty `Tc`: `nodeBody` without building and clearing `Tc`. -/
noncomputable def nodeBodyR (ds : ComplexFramedExecution.Directions)
    (fp : NWire → ZMod 4 × BinaryWalsh.Address m → Pr P (nT BReg) Q A U)
    (mp : Instr → Pr P (nT BReg) Q A U) :
    Pr P (nT BReg) Q A U :=
  .seq splitProg
    (.seq zeroCentres
      (.seq (Prog.seqList ((program ds).map (instrProg fp mp)))
        (.seq clearCentres mergeProg)))

/-- The step bound of `nodeBodyR`: `nodeCost` without the `Tc` stages. -/
noncomputable def nodeCostR (ds : ComplexFramedExecution.Directions)
    (_u _j _K _ρ _a₀ R n r w cf cm : ℕ) : ℕ :=
  (6 * (NW * (R * 2 ^ n * (r * w))) + 6 * (NW * R) + 2 * NW + 3) +
    (8 * (4 * (R * 2 ^ n * r * w) + 4) + 1) +
    (gateCount (program ds) * gateCost R n r w + factorCount (program ds) * cf +
      monoCount (program ds) * cm + 1) +
    (8 * (2 * (R * 2 ^ n * r * w) + 2) + 1) +
    (6 * (NW * (R * 2 ^ n * (r * w))) + 8 * (NW * R) + 6)

/-- **The node body with an empty `Tc`** on empty left stacks: with every factor implemented in
the sense of `FactorSpecL` and every exact instruction in the sense of `MonoSpecL`, with child
semantics `child` and child exponent `0`, `nodeBodyR` leaves on `io` the stream of
`ofBank (rowsAt R₀ j) (nodeM e child 0 ds (toBank (rowsAt R₀ j) Z))`. -/
theorem nodeBodyR_execL (ds : ComplexFramedExecution.Directions)
    (fp : NWire → ZMod 4 × BinaryWalsh.Address m → Pr P (nT BReg) Q A U)
    (mp : Instr → Pr P (nT BReg) Q A U)
    {bcRest : BReg → List (Fin (A + 4)) → Prop} {R₀ j u K ρ a₀ L n r w cf cm : ℕ}
    (hA : 5 ≤ A) (hNW : NW ≤ A + 4)
    (hgate : ∀ g, Instr.gate g ∈ program ds →
      (2 * gateBound g + 1) ^ (2 * (gateWires g).length) ≤ A + 4)
    (hr : 1 ≤ r) (hw : 1 ≤ w) (_hK : 1 ≤ K) (hfit : ∀ i < bits u (j + 1), a₀ + ρ + K * i < n)
    (child : Fin m → ZArr (Fin (rowsAt R₀ j) × Fin r) n → ZArr (Fin (rowsAt R₀ j) × Fin r) n)
    (hfac : ∀ fw g, Instr.factor fw g ∈ program ds →
      FactorSpecL body (fp fw g) bcRest j u K ρ a₀ L (rowsAt R₀ (j + 1)) n r w (k := bits u j)
        (actMap a₀ ρ K (bits u (j + 1)) n hfit) child 0 fw g cf)
    (hmono : ∀ i ∈ program ds, i.IsMono →
      MonoSpecL body (mp i) bcRest j u K ρ a₀ L (rowsAt R₀ (j + 1)) n r w (k := bits u j)
        (actMap a₀ ρ K (bits u (j + 1)) n hfit) child 0 i cm)
    (Z : ZArr (Fin (rowsAt R₀ (j + 1)) × Fin r) n) (v : HS (nT BReg) Q A U)
    (S : Stacks (nT BReg) A) (hL : ∀ y, S.L y = [])
    (hpar : ParState S.R (j + 1) u K ρ a₀ L (rowsAt R₀ (j + 1)) n w (r * w))
    (hrest : Rest bcRest n r w S.R) (hio : S.R (reg .io) = encZ A w Z) :
    ∃ (v' : HS (nT BReg) Q A U) (c : ℕ), v'.user = v.user ∧
      c ≤ nodeCostR ds u j K ρ a₀ (rowsAt R₀ j) n r w cf cm ∧
      Exec body (nodeBodyR ds fp mp) (mk v S) c (mk v' { S with
        R := Function.update S.R (reg .io) (encZ A w (ofBank (rowsAt R₀ j)
          (nodeM (k := bits u j) (actMap a₀ ρ K (bits u (j + 1)) n hfit) child 0 ds
            (toBank (rowsAt R₀ j) Z)))) }) := by
  set B₀ := bankZ (toBank (rowsAt R₀ j) Z)
  -- the row split
  have hsplit := splitProg_exec body hNW hr hw (R := rowsAt R₀ j) Z v S hio (hrest .rowctr)
    (hrest .rowtmp) (fun x => hrest (.wtmp x)) (fun x => hrest (.wire x))
  obtain ⟨v₁, m₁, R₁, hu₁, hm₁, he₁, hio₁, hw₁, hfr₁⟩ := hsplit
  have h₁ : ∀ x : LReg BReg, x ≠ .io → (∀ y : DWire, x ≠ .wire (.inl y)) →
      R₁ (reg x) = S.R (reg x) :=
    fun x h1 h2 => hfr₁ _ (reg_ne h1) (fun y => reg_ne (h2 y))
  -- the zero centres
  obtain ⟨v₂, m₂, R₂, hu₂, hm₂, he₂, hc₂, hfr₂⟩ := zeroCentres_exec body (B₀ (.inl 0)) v₁
    { S with R := R₁ } (hw₁ 0) (by dsimp only; rw [h₁ _ (by simp) (by simp)]; exact hrest .tmp)
    (fun c => by dsimp only; rw [h₁ _ (by simp) (by simp)]; exact hrest (.wire (.inr c)))
  have hw₂ : ∀ x, R₂ (reg (.wire x)) = encZ A w (B₀ x) := by
    intro x
    rcases x with d | c
    · rw [hfr₂ _ (fun c => reg_ne (by simp))]; exact hw₁ d
    · exact hc₂ c
  have h₂ : ∀ x : LReg BReg, x ≠ .io → (∀ y, x ≠ .wire y) → R₂ (reg x) = S.R (reg x) :=
    fun x h1 h2 => (hfr₂ _ fun c => reg_ne (h2 _)).trans (h₁ x h1 fun y => h2 _)
  -- the instructions
  have hN₂ : NodeRegs bcRest R₂ j u K ρ a₀ L (rowsAt R₀ (j + 1)) n r w 0 :=
    { par := hpar.congr fun x hx => h₂ x (parRegs_ne hx).1 (parRegs_ne hx).2.1
      rest := hrest.restBut_of_frame _ fun x hx hx' => by
        rw [h₂ x hx (fun y h => hx' (Or.inl ⟨y, h⟩))]
      io := by rw [hfr₂ _ (fun c => reg_ne (by simp))]; exact hio₁
      tc := by rw [h₂ _ (by simp) (by simp), hrest .Tc]; rfl }
  obtain ⟨v₄, m₄, R₄, hu₄, hm₄, he₄, hw₄, hfr₄⟩ := instrs_execL body ds fp mp (by omega) hgate
    (k := bits u j) hw (actMap a₀ ρ K (bits u (j + 1)) n hfit) child hfac hmono (program ds)
    (fun i hi => hi) B₀ v₂ { S with R := R₂ } hL hN₂ hw₂
  set Bf := runM (actMap a₀ ρ K (bits u (j + 1)) n hfit) child 0 (program ds) B₀
  have h₄ : ∀ x : LReg BReg, x ≠ .io → (∀ y, x ≠ .wire y) → R₄ (reg x) = S.R (reg x) :=
    fun x h1 hx => (hfr₄ _ (fun y => reg_ne (hx y))).trans (h₂ x h1 hx)
  have hio₄ : R₄ (reg .io) = [] := by
    rw [hfr₄ _ (fun y => reg_ne (by simp))]; exact hN₂.io
  -- clearing the centres
  obtain ⟨v₆, m₆, R₆, hu₆, hm₆, he₆, hc₆, hfr₆⟩ := clearCentres_exec body
    (rowsAt R₀ j * 2 ^ n * r * w) v₄ { S with R := R₄ }
    (fun c => by dsimp only; rw [hw₄, length_encZ]; ring)
  dsimp only at hc₆ hfr₆
  -- the row merge
  obtain ⟨v₈, m₈, R₈, hu₈, hm₈, he₈, hio₈, hw₈, hfr₈⟩ := mergeProg_exec body hNW
    (R := rowsAt R₀ j) Bf v₆ { S with R := R₆ }
    (fun d => by dsimp only; rw [hfr₆ _ (fun c => reg_ne (by simp))]; exact hw₄ _)
    (by dsimp only; rw [hfr₆ _ (fun c => reg_ne (by simp)), h₄ _ (by simp) (by simp)];
        exact hrest .rowctr)
    (by dsimp only; rw [hfr₆ _ (fun c => reg_ne (by simp)), h₄ _ (by simp) (by simp)];
        exact hrest .rowtmp)
    (by dsimp only; rw [hfr₆ _ (fun c => reg_ne (by simp)), h₄ _ (by simp) (by simp)];
        exact hpar .rows)
    (by dsimp only; rw [hfr₆ _ (fun c => reg_ne (by simp)), h₄ _ (by simp) (by simp)];
        exact hrest .rctmp)
    (by dsimp only; rw [hfr₆ _ (fun c => reg_ne (by simp)), h₄ _ (by simp) (by simp)];
        exact hrest .racc)
    (by dsimp only; rw [hfr₆ _ (fun c => reg_ne (by simp))]; exact hio₄)
  dsimp only at hio₈ hw₈ hfr₈
  -- the final registers
  have hfin : R₈ = Function.update S.R (reg .io) (encZ A w (ofBank (rowsAt R₀ j)
      (nodeM (k := bits u j) (actMap a₀ ρ K (bits u (j + 1)) n hfit) child 0 ds
        (toBank (rowsAt R₀ j) Z)))) := by
    funext q
    by_cases hq : q = reg .io
    · rw [hq, Function.update_self, hio₈]
      rfl
    rw [Function.update_of_ne hq]
    by_cases hqw : ∃ d : DWire, q = reg (.wire (.inl d))
    · obtain ⟨d, rfl⟩ := hqw
      rw [hw₈ d]
      exact (hrest (.wire (.inl d))).symm
    push Not at hqw
    rw [hfr₈ q hq hqw]
    by_cases hqc : ∃ c, q = reg (.wire (.inr c))
    · obtain ⟨c, rfl⟩ := hqc
      rw [hc₆ c]
      exact (hrest (.wire (.inr c))).symm
    push Not at hqc
    rw [hfr₆ q hqc]
    obtain ⟨x, rfl⟩ := (regEquiv BReg).surjective q
    refine h₄ x (fun h => hq (by rw [h]; rfl)) fun y h => ?_
    rcases y with d | c
    · exact hqw d (by rw [h]; rfl)
    · exact hqc c (by rw [h]; rfl)
  refine ⟨v₈, m₁ + (m₂ + (m₄ + (m₆ + m₈))), by rw [hu₈, hu₆, hu₄, hu₂, hu₁], ?_,
    Exec.cast (Exec.seq he₁ (Exec.seq he₂ (Exec.seq he₄ (Exec.seq he₆ he₈)))) rfl (by rw [hfin])⟩
  unfold nodeCostR
  omega

end NodeR

/-! ### The semantics -/

/-- The rounded layer as the tape computes it: `layerR` with the symmetric representative modulo
`2 ^ w` of every child result before its truncation. -/
noncomputable def layerRW {r n : ℕ} (w u : ℕ) (ds : ComplexFramedExecution.Directions) (R₀ : ℕ) :
    (j : ℕ) → (Fin (bits u j) → Fin n) → ZArr (Fin (rowsAt R₀ j) × Fin r) n →
      ZArr (Fin (rowsAt R₀ j) × Fin r) n
  | 0, e, f => k2s ((List.finRange u).map e) f
  | j + 1, e, f =>
      ofBank (rowsAt R₀ j) (nodeM (k := bits u j) e
        (fun s g => tdivArr (scaleR u ds j)
          (symArr w (layerRW w u ds R₀ j (fun c => e (bitIdx s c)) g))) 0 ds
        (toBank (rowsAt R₀ j) f))

/-! ### The procedure -/

noncomputable section
variable {Q Ka : ℕ} {U : Type}

/-- The rounded compact layer body: the leaf, or the node with rounded factors whose child calls
are followed by the truncation. -/
noncomputable def compactLayerBodyR (hQ : compactRuntimeStates ≤ Q)
    (ds : ComplexFramedExecution.Directions) : Pr LProc (nT CompactBReg) Q (prime+Ka) U :=
  .seq (.act (peekR (reg .lev)))
    (.cond (fun v => !v.flag) leafP
      (nodeBodyR ds (compactFactorProgR hQ (.seq (.call .layer) (truncP (gateCount (program ds)))))
        (monoProgC hQ)))

noncomputable def compactLayerTableR (hQ : compactRuntimeStates ≤ Q)
    (ds : ComplexFramedExecution.Directions) : LProc → Pr LProc (nT CompactBReg) Q (prime+Ka) U :=
  fun _ => compactLayerBodyR hQ ds

/-- The step bound of the rounded compact layer at level `j`, offset `a`. -/
noncomputable def compactLayerCostR (ds : ComplexFramedExecution.Directions)
    (u K ρ R₀ n o r w : ℕ) (budget : CompactBasisBudget) : ℕ → ℕ → ℕ
  | 0, a => leafCost u K ρ (o+a) R₀ (o+n) r w+4
  | j+1, a => nodeCostR ds u j K ρ (o+a) (rowsAt R₀ j) (o+n) r w
      (facMax ds fun _ g => compactFactorCostR j u K R₀ (o+n) r w g
        (compactLayerCostR ds u K ρ R₀ n o r w budget j (a+pivotOf g.2*(K*bits u j)) +
          truncCost (gateCount (program ds)) u j (rowsAt R₀ j) (o+n) r w)
        (budget j a g.2))
      (monoMax ds (monoCostB (budget j a) j u K (o+a) R₀ (o+n) o r w ρ (rowsAt R₀ j))) + 4

/-- **The rounded compact layer.** The call of the rounded procedure at level `j` computes
`layerRW w u ds R₀ j` on the active bits `o + a + ρ + K i`, provided every child level `i < j`
truncates by fewer than `w` bits. -/
theorem compactLayerR_exec (hQ : compactRuntimeStates ≤ Q)
    (ds : ComplexFramedExecution.Directions) (hA : 14 ≤ prime+Ka)
    (hA9 : 9^4 ≤ prime+Ka+4) (hNW : NW ≤ prime+Ka+4)
    (hgate : ∀ g, Instr.gate g ∈ program ds →
      (2*gateBound g+1)^(2*(gateWires g).length) ≤ prime+Ka+4)
    {shape : Shape} {u ρ R₀ n o r w D : ℕ}
    (hr : 1 ≤ r) (hw : 1 ≤ w) (hu : 1 ≤ u) (hR₀ : 1 ≤ R₀)
    (hG : 1 ≤ shape.guard) (hGK : shape.guard+1 ≤ shape.chunk)
    (hrecord : shape.bits+1 ≤ shape.payload) (hpayload : shape.payload=2^o*(3*(r*w)))
    (budget : CompactBasisBudget) :
    ∀ j, (∀ i<j, scaleR u ds i < w) → ∀ a,
    CompactLayerReady shape n o u ρ R₀ r w Ka D hR₀ hG hGK hrecord budget j a →
    ∀ (hfit : ∀ i<bits u j, (o+a)+ρ+shape.chunk*i<o+n),
    (o+a)+shape.chunk*bits u j ≤ o+n →
    CallSpecF (compactLayerTableR (Ka := Ka) (U := U) hQ ds) (.call .layer)
      (compactBasisRest shape o r) R₀ j u shape.chunk ρ (o+a) (shape.chunk*bits u j) (o+n) r w
      (layerRW w u ds R₀ j (actMap (o+a) ρ shape.chunk (bits u j) (o+n) hfit))
      (compactLayerCostR ds u shape.chunk ρ R₀ n o r w budget j a) := by
  intro j
  induction j with
  | zero =>
      intro _ a _ hfit _ Z v S _ hpar hrest hio
      have hlev : S.R (reg .lev)=[] := List.eq_nil_of_length_eq_zero (hpar .lev)
      have hp := Exec.act (body := compactLayerTableR (U := U) hQ ds) (peekR (reg .lev)) (mk v S)
      rw [peekR_run] at hp
      obtain ⟨v₁,c₁,hu₁,hc₁,he₁⟩ := leafP_exec (compactLayerTableR hQ ds) hA9 hr hw hfit Z
        {v with flag := (S.R (reg .lev)).head?.isSome} S hpar hrest hio
      have hc₁' : c₁ ≤ leafCost u shape.chunk ρ (o+a) R₀ (o+n) r w := hc₁
      refine ⟨v₁,1+(c₁+1)+2,hu₁,?_,?_⟩
      · simp only [compactLayerCostR]; omega
      · exact Exec.call (Exec.seq hp (Exec.cond_true (by simp [hlev]) he₁))
  | succ j ih =>
      intro hsw a hready hfit hfitL Z v S hL hpar hrest hio
      obtain ⟨left,right,layout,hpack,hbudget,hchildren⟩ := hready
      have hlev : (S.R (reg .lev)).length=j+1 := hpar .lev
      obtain ⟨x₀,rest,hl⟩ : ∃ x₀ rest, S.R (reg .lev)=x₀::rest := by
        cases h : S.R (reg .lev) with
        | nil => rw [h] at hlev; simp at hlev
        | cons x rest => exact ⟨x,rest,rfl⟩
      have hp := Exec.act (body := compactLayerTableR (U := U) hQ ds) (peekR (reg .lev)) (mk v S)
      rw [peekR_run] at hp
      set G := gateCount (program ds) with hGd
      set Lc := shape.chunk*bits u j with hLc
      set cf := facMax ds fun _ g => compactFactorCostR j u shape.chunk R₀ (o+n) r w g
        (compactLayerCostR ds u shape.chunk ρ R₀ n o r w budget j (a+pivotOf g.2*Lc) +
          truncCost G u j (rowsAt R₀ j) (o+n) r w)
        (budget j a g.2) with hcf
      set e := actMap (o+a) ρ shape.chunk (bits u (j+1)) (o+n) hfit with he_def
      set child : Fin m → ZArr (Fin (rowsAt R₀ j) × Fin r) (o+n) →
          ZArr (Fin (rowsAt R₀ j) × Fin r) (o+n) := fun s g => tdivArr (scaleR u ds j)
        (symArr w (layerRW w u ds R₀ j (fun c => e (bitIdx s c)) g)) with hchild
      have hfac : ∀ fw g, Instr.factor fw g ∈ program ds →
          FactorSpecL (compactLayerTableR (Ka := Ka) (U := U) hQ ds)
            (compactFactorProgR hQ (.seq (.call .layer) (truncP G)) fw g)
            (compactBasisRest shape o r)
            j u shape.chunk ρ (o+a) (shape.chunk*bits u (j+1)) (rowsAt R₀ (j+1)) (o+n) r w
            (k:=bits u j) e child 0 fw g cf := by
        intro fw g hg
        apply FactorSpecL.mono (compactFactorProgR_spec (compactLayerTableR hQ ds) hQ
          (.seq (.call .layer) (truncP G)) hA hr hw hu hR₀ layout hG hGK hrecord hpayload D hpack
          hfit hfitL child fw g
          (compactLayerCostR ds u shape.chunk ρ R₀ n o r w budget j (a+pivotOf g.2*Lc) +
            truncCost G u j (rowsAt R₀ j) (o+n) r w) ?_)
        · exact (compactFactorCostR_mono_basis _ _ _ _ _ _ _ _ _ (hbudget g.2)).trans
            (le_facMax ds (fun _ g => compactFactorCostR j u shape.chunk R₀ (o+n) r w g
              (compactLayerCostR ds u shape.chunk ρ R₀ n o r w budget j (a+pivotOf g.2*Lc) +
                truncCost G u j (rowsAt R₀ j) (o+n) r w)
              (budget j a g.2)) hg)
        · intro hs
          set s := Fin.find _ hs with hsdef
          have hpv : pivotOf g.2=(s : ℕ) := by simp [pivotOf,hs,hsdef]
          rw [hpv]
          have hsm : (s : ℕ)+1 ≤ m := s.2
          have hfitL' : (o+a)+(s : ℕ)*Lc+Lc ≤ o+n := by
            have h1 := Nat.mul_le_mul_right Lc hsm
            have h2 : shape.chunk*bits u (j+1)=m*Lc := by
              rw [hLc, show bits u (j+1)=m*bits u j from rfl]; ring
            have h3 : ((s : ℕ)+1)*Lc=(s : ℕ)*Lc+Lc := by ring
            omega
          have hfit' : ∀ i < bits u j, (o+a) + (s : ℕ) * Lc + ρ + shape.chunk * i < (o+n) := by
            intro i hi
            have hs' := s.2
            have h1 : i + bits u j * s < bits u (j + 1) := by
              show i + bits u j * s < m * bits u j
              nlinarith
            have := hfit _ h1
            have h2 : shape.chunk * (i + bits u j * s) = shape.chunk * i + s * Lc := by
              rw [hLc]; ring
            omega
          have heS : (fun c => e (bitIdx s c)) =
              actMap ((o+a) + (s : ℕ) * Lc) ρ shape.chunk (bits u j) (o+n) hfit' := by
            funext c
            apply Fin.ext
            simp only [he_def, actMap, bitIdx, finProdFinEquiv_apply_val, hLc]
            ring
          have ih' := ih (fun i hi => hsw i (by omega)) (a+(s : ℕ)*Lc) (hchildren s)
          rw [← Nat.add_assoc o a] at ih'
          have ht := (ih' hfit' hfitL').trunc _ (by omega) G
            (by rw [hGd, ← scaleR_eq_expSeq]; exact hsw j (by omega))
          have hcs : child s = fun Z => tdivArr (expSeq G 0 u j) (symArr w
              (layerRW w u ds R₀ j (actMap ((o+a) + (s : ℕ) * Lc) ρ shape.chunk (bits u j) (o+n)
                hfit') Z)) := by
            funext Z
            rw [hchild, hGd, ← scaleR_eq_expSeq]
            dsimp only
            rw [heS]
          rw [hcs]
          exact ht
      have hmono : ∀ i ∈ program ds, i.IsMono →
          MonoSpecL (compactLayerTableR (Ka := Ka) (U := U) hQ ds) (monoProgC hQ i)
            (compactBasisRest shape o r) j u shape.chunk ρ (o+a) (shape.chunk*bits u (j+1))
            (rowsAt R₀ (j+1)) (o+n) r w (k:=bits u j) e child 0 i
            (monoMax ds (monoCostB (budget j a) j u shape.chunk (o+a) R₀ (o+n) o r w ρ (rowsAt R₀ j))) :=
        fun i hi hm => MonoSpecL.mono _ (MonoSpecL.mono _ (monoProgC_spec (compactLayerTableR hQ ds)
          hQ hA hr hw hu hR₀ layout hG hGK hrecord hpayload D hpack hfit child i (program_fit ds i hi) hm)
          (monoCostC_le layout hG hGK (rowsAt_pos hR₀ j) hrecord D hpack (nT CompactBReg) o r w j u
            (o+a) R₀ (budget j a) hbudget i)) (le_monoMax ds _ hi)
      obtain ⟨v₁,c₁,hu₁,hc₁,he₁⟩ := nodeBodyR_execL (compactLayerTableR hQ ds) ds
        (compactFactorProgR hQ (.seq (.call .layer) (truncP G))) (monoProgC hQ) (by omega) hNW hgate
        hr hw (by omega) hfit child hfac hmono Z {v with flag := (S.R (reg .lev)).head?.isSome} S hL
        hpar hrest hio
      refine ⟨v₁,1+(c₁+1)+2,hu₁,?_,?_⟩
      · simp only [compactLayerCostR]; rw [← hLc, ← hGd, ← hcf]; omega
      · exact Exec.call (Exec.seq hp (Exec.cond_false (by simp [hl]) he₁))

end
end IntegerMultBounds.MathlibTM2.LayerMachine
