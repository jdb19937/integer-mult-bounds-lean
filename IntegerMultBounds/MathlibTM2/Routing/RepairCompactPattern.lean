module

public import IntegerMultBounds.MathlibTM2.Routing.CompactPatternTable
public import IntegerMultBounds.MathlibTM2.Routing.RepairDescriptorBank

/-! The compact compiler's concrete patterns for all eleven repair descriptors.
Compact inputs still require executed generation from the sparse profiles. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget

noncomputable section

def repairCompactRows (p : Par) : RepairDescriptorKey → ℕ
  | none => p.wy
  | some (off, _) => selectiveTargetWidth p off

def repairCompactSourceWidth (p : Par) (X : ℕ) : RepairDescriptorKey → ℕ
  | none => p.wy + 2 * p.wc + X
  | some (off, _) => selectiveSourceWidth p X off

variable (p : Par) (X : ℕ) (hG : 0 < p.G) (hK : 0 < p.K)
  (active : Fin p.n → Bool) (s : Fin p.n → SlotSource p X) (key : RepairDescriptorKey)

def repairCompactPattern : (key : RepairDescriptorKey) →
    Fin (repairCompactRows p key) → Option (Fin (repairCompactSourceWidth p X key))
  | none => selectiveKeyPattern p X active s
  | some (off, k) => selectivePatterns p X hG hK active s off k

theorem repairCompactPattern_word {A : ℕ} :
    (patternTable (repairCompactPattern p X hG hK active s key)).flatten.map (bitSymbol (a := A)) =
      repairDescriptorWord p X hG hK active s key := by
  cases key with
  | none => rfl
  | some pair => cases pair; rfl

variable {T Q A : ℕ} {P U : Type}

theorem repairCompactPattern_exec (body : P → Pr P T Q A U)
    (zero : BinaryZeroReg → Fin T) (hzero : Function.Injective zero)
    (runs : SelectorRunReg → Fin T) (hruns : Function.Injective runs) (hblockReg : zero .dst = runs .block)
    (mask : BinaryMaskReg → Fin T) (hmask : Function.Injective mask)
    (saved out : Fin T) (hss : runs .dst ≠ saved) (hso : runs .dst ≠ out) (hao : saved ≠ out)
    (hsrcMask : ∀ r, runs .dst ≠ mask r) (hsavedMask : ∀ r, saved ≠ mask r) (houtMask : ∀ r, out ≠ mask r)
    (Lw Lg L : ℕ) (hL : L < 2 ^ Lw) (hW : repairCompactSourceWidth p X key + 1 < 2 ^ L)
    (hsize : repairCompactRows p key < 2 ^ Lg)
    (v : HS T Q A U) (S : Stacks T A)
    (hwidth : S.R (zero .width) = binSyms Lw L) (hunary : S.R (zero .unary) = [])
    (hscratch : ∀ i, S.R (zero (.scratch i)) = [])
    (hinput : S.R (runs .src) = selectorRunFrames Lg L (SparseSelectorRun.compress (List.ofFn (patternIndex (repairCompactPattern p X hG hK active s key))).reverse).reverse)
    (harchive : S.R (runs .archive) = []) (hblock : S.R (runs .block) = []) (hselectors : S.R (runs .dst) = [])
    (hblank : ∀ r, r ≠ .src → r ≠ .archive → r ≠ .block → r ≠ .dst → S.R (runs r) = [])
    (hready : DescriptorCompileReady mask S.R L (repairCompactSourceWidth p X key + 1)) (hsaved : S.R saved = []) :
    ∃ (v' : HS T Q A U) (steps : ℕ), v'.user = v.user ∧
      steps ≤ ((Lw * (4 * L + 11) + 8 * L + 13) + selectorRunLoopCost Lg L (SparseSelectorRun.compress (List.ofFn (patternIndex (repairCompactPattern p X hG hK active s key))).reverse).reverse +
        2 * (selectorRunFrames (A := A) Lg L (SparseSelectorRun.compress (List.ofFn (patternIndex (repairCompactPattern p X hG hK active s key))).reverse).reverse).length + 3 + (2 * (L + 1) + 2)) +
        (repairCompactRows p key * (descriptorCompileCallCost L (repairCompactSourceWidth p X key + 1) + 2) + 2 * (repairCompactRows p key * (L + 1)) + 4) +
        (2 * (repairCompactRows p key * (L + 1)) + 2) ∧
      Exec body (compactDescriptorProgram zero runs mask saved out) (mk v S) steps
        (mk v' { S with R := Function.update S.R out (repairDescriptorWord p X hG hK active s key ++ S.R out) }) := by
  obtain ⟨v', steps, hu, ht, he⟩ := compactPatternTable_exec body zero hzero runs hruns hblockReg mask hmask
    saved out hss hso hao hsrcMask hsavedMask houtMask Lw Lg L hL hW
    (repairCompactPattern p X hG hK active s key) hsize v S hwidth hunary hscratch
    hinput harchive hblock hselectors hblank hready hsaved
  rw [repairCompactPattern_word] at he
  exact ⟨v', steps, hu, ht, he⟩

end
end IntegerMultBounds.MathlibTM2.Routing
