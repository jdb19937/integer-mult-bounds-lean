module

public import IntegerMultBounds.MathlibTM2.Node.CompactFactor
public import IntegerMultBounds.MathlibTM2.Node.LayerProc
public import IntegerMultBounds.MathlibTM2.Node.MonoC
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

/-! Recursive execution of the compact layer with one fixed global reservation. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds IntegerMultBounds.Networks IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Layer
open IntegerMultBounds.MathlibTM2.Node hiding LReg
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
open CompactGadgetReservationShape (Shape)
noncomputable section
variable {Q Ka : ℕ} {U : Type}

noncomputable def compactLayerBody (hQ : compactRuntimeStates ≤ Q)
    (ds : ComplexFramedExecution.Directions) : Pr LProc (nT CompactBReg) Q (prime+Ka) U :=
  .seq (.act (peekR (reg .lev)))
    (.cond (fun v => !v.flag) leafP
      (nodeBody ds (compactFactorProg hQ (.call .layer) ds) (monoProgC hQ)))

noncomputable def compactLayerTable (hQ : compactRuntimeStates ≤ Q)
    (ds : ComplexFramedExecution.Directions) : LProc → Pr LProc (nT CompactBReg) Q (prime+Ka) U :=
  fun _ => compactLayerBody hQ ds

/-- A numerical bound for each basis invocation at each local offset. -/
abbrev CompactBasisBudget := ℕ → ℕ → BinaryWalsh.Address m → Fin m → ℕ

/-- Explicit geometric and packing conditions at all reachable positive levels.
The zero-level case has no layout requirement. This predicate contains no execution assumptions. -/
def CompactLayerReady (shape : Shape) (n o u ρ R₀ r w Ka D : ℕ)
    (hR₀ : 1 ≤ R₀) (hG : 1 ≤ shape.guard) (hGK : shape.guard+1 ≤ shape.chunk)
    (hrecord : shape.bits+1 ≤ shape.payload) (budget : CompactBasisBudget) : ℕ → ℕ → Prop
  | 0, _ => True
  | j+1, a => ∃ left right,
      ∃ layout : CompactRecursiveLayout shape n a (bits u j) ρ left right,
      ∃ hp : CompactLayoutPacked layout (rowsAt R₀ j) D,
      (∀ vv x, compactFactorBasisCost layout hG hGK (rowsAt_pos hR₀ j) hrecord D hp
        (nT CompactBReg) Ka o r w vv x ≤ budget j a vv x) ∧
      ∀ p : Fin m, CompactLayerReady shape n o u ρ R₀ r w Ka D hR₀ hG hGK hrecord budget
        j (a+p.val*(shape.chunk*bits u j))

noncomputable def compactLayerCost (ds : ComplexFramedExecution.Directions)
    (u K ρ R₀ n o r w : ℕ) (budget : CompactBasisBudget) : ℕ → ℕ → ℕ
  | 0, a => leafCost u K ρ (o+a) R₀ (o+n) r w+4
  | j+1, a => nodeCost ds u j K ρ (o+a) (rowsAt R₀ j) (o+n) r w
      (facMax ds fun _ g => compactFactorCost (nT CompactBReg) ds j u K ρ (o+a) R₀ (o+n) r w g
        (compactLayerCost ds u K ρ R₀ n o r w budget j (a+pivotOf g.2*(K*bits u j)))
        (budget j a g.2))
      (monoMax ds (monoCostB (budget j a) j u K (o+a) R₀ (o+n) o r w ρ (rowsAt R₀ j))) + 4

lemma compactFactorCost_mono_basis (ds : ComplexFramedExecution.Directions)
    (T j u K ρ a R₀ n r w : ℕ) (g : ZMod 4 × BinaryWalsh.Address m) (cc : ℕ)
    {b b' : Fin m → ℕ} (hb : ∀ x, b x ≤ b' x) :
    compactFactorCost T ds j u K ρ a R₀ n r w g cc b ≤
      compactFactorCost T ds j u K ρ a R₀ n r w g cc b' := by
  unfold compactFactorCost
  split
  · rename_i h
    have := hb (Fin.find _ h)
    omega
  · exact le_rfl

/-- The actual recursive compact program. Child calls are discharged by induction. -/
theorem compactLayer_exec (hQ : compactRuntimeStates ≤ Q)
    (ds : ComplexFramedExecution.Directions) (hA : 14 ≤ prime+Ka)
    (hA9 : 9^4 ≤ prime+Ka+4) (hNW : NW ≤ prime+Ka+4)
    (hgate : ∀ g, Instr.gate g ∈ program ds →
      (2*gateBound g+1)^(2*(gateWires g).length) ≤ prime+Ka+4)
    {shape : Shape} {u ρ R₀ n o r w D : ℕ}
    (hr : 1 ≤ r) (hw : 1 ≤ w) (hu : 1 ≤ u) (hR₀ : 1 ≤ R₀)
    (hG : 1 ≤ shape.guard) (hGK : shape.guard+1 ≤ shape.chunk)
    (hrecord : shape.bits+1 ≤ shape.payload) (hpayload : shape.payload=2^o*(3*(r*w)))
    (budget : CompactBasisBudget) :
    ∀ j, (∀ i<j, expZ u ds i ≤ w) → ∀ a,
    CompactLayerReady shape n o u ρ R₀ r w Ka D hR₀ hG hGK hrecord budget j a →
    ∀ (hfit : ∀ i<bits u j, (o+a)+ρ+shape.chunk*i<o+n),
    (o+a)+shape.chunk*bits u j ≤ o+n →
    ∀ (Z : ZArr (Fin (rowsAt R₀ j) × Fin r) (o+n))
      (v : HS (nT CompactBReg) Q (prime+Ka) U) (S : Stacks (nT CompactBReg) (prime+Ka)),
    (∀ y, S.L y=[]) →
    ParState S.R j u shape.chunk ρ (o+a) (shape.chunk*bits u j) (rowsAt R₀ j) (o+n) w (r*w) →
    Rest (compactBasisRest shape o r) (o+n) r w S.R → S.R (reg .io)=encZ (prime+Ka) w Z →
    ∃ (v' : HS (nT CompactBReg) Q (prime+Ka) U) (c : ℕ), v'.user=v.user ∧
      c ≤ compactLayerCost ds u shape.chunk ρ R₀ n o r w budget j a ∧
      Exec (compactLayerTable hQ ds) (.call .layer) (mk v S) c (mk v' {S with
        R := Function.update S.R (reg .io)
          (encZ (prime+Ka) w (layerZ u ds R₀ j (actMap (o+a) ρ shape.chunk (bits u j) (o+n) hfit) Z))}) := by
  intro j
  induction j with
  | zero =>
      intro _ a _ hfit _ Z v S _ hpar hrest hio
      have hlev : S.R (reg .lev)=[] := List.eq_nil_of_length_eq_zero (hpar .lev)
      have hp := Exec.act (body := compactLayerTable (U := U) hQ ds) (peekR (reg .lev)) (mk v S)
      rw [peekR_run] at hp
      obtain ⟨v₁,c₁,hu₁,hc₁,he₁⟩ := leafP_exec (compactLayerTable hQ ds) hA9 hr hw hfit Z
        {v with flag := (S.R (reg .lev)).head?.isSome} S hpar hrest hio
      have hc₁' : c₁ ≤ leafCost u shape.chunk ρ (o+a) R₀ (o+n) r w := hc₁
      refine ⟨v₁,1+(c₁+1)+2,hu₁,?_,?_⟩
      · simp only [compactLayerCost]; omega
      · exact Exec.call (Exec.seq hp (Exec.cond_true (by simp [hlev]) he₁))
  | succ j ih =>
      intro hTw a hready hfit hfitL Z v S hL hpar hrest hio
      obtain ⟨left,right,layout,hpack,hbudget,hchildren⟩ := hready
      have hlev : (S.R (reg .lev)).length=j+1 := hpar .lev
      obtain ⟨x₀,rest,hl⟩ : ∃ x₀ rest, S.R (reg .lev)=x₀::rest := by
        cases h : S.R (reg .lev) with
        | nil => rw [h] at hlev; simp at hlev
        | cons x rest => exact ⟨x,rest,rfl⟩
      have hp := Exec.act (body := compactLayerTable (U := U) hQ ds) (peekR (reg .lev)) (mk v S)
      rw [peekR_run] at hp
      set cf := facMax ds fun _ g => compactFactorCost (nT CompactBReg) ds j u shape.chunk ρ (o+a)
        R₀ (o+n) r w g
        (compactLayerCost ds u shape.chunk ρ R₀ n o r w budget j (a+pivotOf g.2*(shape.chunk*bits u j)))
        (budget j a g.2) with hcf
      have hfac : ∀ fw g, Instr.factor fw g ∈ program ds →
          FactorSpecL (compactLayerTable (Ka := Ka) (U := U) hQ ds)
            (compactFactorProg hQ (.call .layer) ds fw g) (compactBasisRest shape o r)
            j u shape.chunk ρ (o+a) (shape.chunk*bits u (j+1)) (rowsAt R₀ (j+1)) (o+n) r w
            (k:=bits u j) (actMap (o+a) ρ shape.chunk (bits u (j+1)) (o+n) hfit)
            (fun s => layerZ u ds R₀ j fun c => actMap (o+a) ρ shape.chunk (bits u (j+1)) (o+n) hfit (bitIdx s c))
            (expZ u ds j) fw g cf := by
        intro fw g hg
        apply FactorSpecL.mono (compactFactorProg_spec (compactLayerTable hQ ds) hQ (.call .layer)
          ds hA hr hw hu hR₀ layout hG hGK hrecord hpayload D hpack hfit hfitL
          (hTw j (by omega)) fw g
          (compactLayerCost ds u shape.chunk ρ R₀ n o r w budget j (a+pivotOf g.2*(shape.chunk*bits u j))) ?_)
        · exact (compactFactorCost_mono_basis ds _ _ _ _ _ _ _ _ _ _ _ _ (hbudget g.2)).trans
            (le_facMax ds (fun _ g => compactFactorCost (nT CompactBReg) ds j u shape.chunk ρ (o+a)
              R₀ (o+n) r w g
              (compactLayerCost ds u shape.chunk ρ R₀ n o r w budget j (a+pivotOf g.2*(shape.chunk*bits u j)))
              (budget j a g.2)) hg)
        · intro hs hfit'
          have hpv : pivotOf g.2=(Fin.find _ hs : ℕ) := by simp [pivotOf,hs]
          rw [hpv]
          have hsm : (Fin.find _ hs : ℕ)+1 ≤ m := (Fin.find _ hs).2
          have hfitL' : (o+a)+(Fin.find _ hs : ℕ)*(shape.chunk*bits u j)+shape.chunk*bits u j ≤ o+n := by
            have h1 := Nat.mul_le_mul_right (shape.chunk*bits u j) hsm
            have h2 : shape.chunk*bits u (j+1)=m*(shape.chunk*bits u j) := by
              rw [show bits u (j+1)=m*bits u j from rfl]; ring
            have h3 : ((Fin.find _ hs : ℕ)+1)*(shape.chunk*bits u j)=
                (Fin.find _ hs : ℕ)*(shape.chunk*bits u j)+shape.chunk*bits u j := by ring
            omega
          have ih' := ih (fun i hi => hTw i (by omega))
            (a+(Fin.find _ hs : ℕ)*(shape.chunk*bits u j)) (hchildren (Fin.find _ hs))
          rw [← Nat.add_assoc o a] at ih'
          exact ih' hfit' hfitL'
      have hmono : ∀ i ∈ program ds, i.IsMono →
          MonoSpecL (compactLayerTable (Ka := Ka) (U := U) hQ ds) (monoProgC hQ i)
            (compactBasisRest shape o r) j u shape.chunk ρ (o+a) (shape.chunk*bits u (j+1))
            (rowsAt R₀ (j+1)) (o+n) r w (k:=bits u j)
            (actMap (o+a) ρ shape.chunk (bits u (j+1)) (o+n) hfit)
            (fun s => layerZ u ds R₀ j fun c => actMap (o+a) ρ shape.chunk (bits u (j+1)) (o+n) hfit (bitIdx s c))
            (expZ u ds j) i
            (monoMax ds (monoCostB (budget j a) j u shape.chunk (o+a) R₀ (o+n) o r w ρ (rowsAt R₀ j))) :=
        fun i hi hm => MonoSpecL.mono _ (MonoSpecL.mono _ (monoProgC_spec (compactLayerTable hQ ds) hQ hA
          hr hw hu hR₀ layout hG hGK hrecord hpayload D hpack hfit _ i (program_fit ds i hi) hm)
          (monoCostC_le layout hG hGK (rowsAt_pos hR₀ j) hrecord D hpack (nT CompactBReg) o r w j u
            (o+a) R₀ (budget j a) hbudget i)) (le_monoMax ds _ hi)
      obtain ⟨v₁,c₁,hu₁,hc₁,he₁⟩ := nodeBody_execL_layerZ (compactLayerTable hQ ds) ds
        (compactFactorProg hQ (.call .layer) ds) (monoProgC hQ) (by omega) hNW hgate hr hw (by omega)
        hfit hfac hmono Z {v with flag := (S.R (reg .lev)).head?.isSome} S hL hpar hrest hio
      refine ⟨v₁,1+(c₁+1)+2,hu₁,?_,?_⟩
      · simp only [compactLayerCost]; rw [← hcf]; omega
      · exact Exec.call (Exec.seq hp (Exec.cond_false (by simp [hl]) he₁))


/-- Closed recursive call contract for the concrete compact procedure table. -/
theorem compactLayer_callSpec (hQ : compactRuntimeStates ≤ Q)
    (ds : ComplexFramedExecution.Directions) (hA : 14 ≤ prime+Ka)
    (hA9 : 9^4 ≤ prime+Ka+4) (hNW : NW ≤ prime+Ka+4)
    (hgate : ∀ g, Instr.gate g ∈ program ds →
      (2*gateBound g+1)^(2*(gateWires g).length) ≤ prime+Ka+4)
    {shape : Shape} {u ρ R₀ n o r w D : ℕ}
    (hr : 1 ≤ r) (hw : 1 ≤ w) (hu : 1 ≤ u) (hR₀ : 1 ≤ R₀)
    (hG : 1 ≤ shape.guard) (hGK : shape.guard+1 ≤ shape.chunk)
    (hrecord : shape.bits+1 ≤ shape.payload) (hpayload : shape.payload=2^o*(3*(r*w)))
    (budget : CompactBasisBudget) (j : ℕ) (hTw : ∀ i<j, expZ u ds i ≤ w) (a : ℕ)
    (hready : CompactLayerReady shape n o u ρ R₀ r w Ka D hR₀ hG hGK hrecord budget j a)
    (hfit : ∀ i<bits u j, (o+a)+ρ+shape.chunk*i<o+n)
    (hfitL : (o+a)+shape.chunk*bits u j ≤ o+n) :
    CallSpec (compactLayerTable (Ka := Ka) (U := U) hQ ds) (.call .layer)
      (compactBasisRest shape o r) ds R₀ j u shape.chunk ρ (o+a) (shape.chunk*bits u j)
      (o+n) r w hfit (compactLayerCost ds u shape.chunk ρ R₀ n o r w budget j a) :=
  compactLayer_exec hQ ds hA hA9 hNW hgate hr hw hu hR₀ hG hGK hrecord hpayload budget
    j hTw a hready hfit hfitL

end
end IntegerMultBounds.MathlibTM2.LayerMachine
