module

public import IntegerMultBounds.MathlibTM2.Node.Mono
public import IntegerMultBounds.MathlibTM2.Node.CompactFactorBasis

/-! **The exact instructions on the compact register file.** A slot XOR is the compact basis change
`compactBasisW` along `e_i + e_j` at the pivot `i`, a translation is `transW`; both run framed at the
parameters of the child level. A slot phase is `phaseInstr`. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds IntegerMultBounds.Networks IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Layer
open IntegerMultBounds.MathlibTM2.Node hiding LReg
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
open CompactGadgetReservationShape (Shape)
noncomputable section

section MonoC

variable {Q Ka : ℕ} {U P : Type} (body : P → Pr P (nT CompactBReg) Q (prime + Ka) U)

/-- The program of an exact instruction on the compact register file. -/
def monoProgC (hQ : compactRuntimeStates ≤ Q) : Instr → Pr P (nT CompactBReg) Q (prime + Ka) U
  | .trans fw tv => if h : ∃ x, tv x = 0 then framed (transW hQ fw tv (Fin.find _ h)) else .act .done
  | .xor fw i j => framed (compactBasisW hQ fw (Pi.single i 1 + Pi.single j 1) i)
  | .phase fw i c => phaseInstr fw i c
  | _ => .act .done

/-- The step bound of the compact program of an exact instruction at level `j + 1`. -/
def monoCostC {s : Shape} {n a₀ k ρ left right : ℕ} (layout : CompactRecursiveLayout s n a₀ k ρ left right)
    (hG : 1 ≤ s.guard) (hGK : s.guard + 1 ≤ s.chunk) {R : ℕ} (hR : 0 < R)
    (hrecord : s.bits + 1 ≤ s.payload) (D : ℕ)
    (hp : CompactLayoutPacked layout R D)
    (T o r w j u a₀' R₀ n' : ℕ) : Instr → ℕ
  | .trans _ tv => if h : ∃ x, tv x = 0 then framedCost j u s.chunk R₀
      (2 * compactFactorBasisCost layout hG hGK hR hrecord D hp T Ka o r w
        (tv + Pi.single (Fin.find _ h) 1) (Fin.find _ h) + 2 * (6 * (R * 2 ^ (o + n) * r * w) + 6))
      else 1
  | .xor _ i j' => framedCost j u s.chunk R₀
      (compactFactorBasisCost layout hG hGK hR hrecord D hp T Ka o r w (Pi.single i 1 + Pi.single j' 1) i)
  | .phase _ _ _ => phaseInstrCost u j a₀' ρ s.chunk R n' r w
  | _ => 1

/-- The step bound of the compact program of an exact instruction with a numerical basis budget. -/
def monoCostB (budget : BinaryWalsh.Address m → Fin m → ℕ) (j u K a₀' R₀ n' _o r w ρ R : ℕ) :
    Instr → ℕ
  | .trans _ tv => if h : ∃ x, tv x = 0 then framedCost j u K R₀
      (2 * budget (tv + Pi.single (Fin.find _ h) 1) (Fin.find _ h) + 2 * (6 * (R * 2 ^ n' * r * w) + 6))
      else 1
  | .xor _ i j' => framedCost j u K R₀ (budget (Pi.single i 1 + Pi.single j' 1) i)
  | .phase _ _ _ => phaseInstrCost u j a₀' ρ K R n' r w
  | _ => 1

omit body in
lemma monoCostC_le {s : Shape} {n a₀ k ρ left right : ℕ} (layout : CompactRecursiveLayout s n a₀ k ρ left right)
    (hG : 1 ≤ s.guard) (hGK : s.guard + 1 ≤ s.chunk) {R : ℕ} (hR : 0 < R)
    (hrecord : s.bits + 1 ≤ s.payload) (D : ℕ)
    (hp : CompactLayoutPacked layout R D)
    (T o r w j u a₀' R₀ : ℕ) (budget : BinaryWalsh.Address m → Fin m → ℕ)
    (hb : ∀ vv x, compactFactorBasisCost layout hG hGK hR hrecord D hp T Ka o r w vv x ≤ budget vv x)
    (ins : Instr) :
    monoCostC (Ka := Ka) layout hG hGK hR hrecord D hp T o r w j u a₀' R₀ (o + n) ins ≤
      monoCostB budget j u s.chunk a₀' R₀ (o + n) o r w ρ R ins := by
  cases ins with
  | trans fw tv =>
    simp only [monoCostC, monoCostB]
    split_ifs with h
    · unfold framedCost; have := hb (tv + Pi.single (Fin.find _ h) 1) (Fin.find _ h); omega
    · exact le_rfl
  | xor fw i j' =>
    simp only [monoCostC, monoCostB]
    unfold framedCost; have := hb (Pi.single i 1 + Pi.single j' 1) i; omega
  | phase fw i c => exact le_rfl
  | factor fw g => exact le_rfl
  | gate g => exact le_rfl

/-- **The exact instructions on the compact register file.** -/
theorem monoProgC_spec (hQ : compactRuntimeStates ≤ Q) (hA : 14 ≤ prime + Ka) {shape : Shape}
    {R₀ j u ρ a₀ n o r w left right Tc : ℕ} (hr : 1 ≤ r) (hw : 1 ≤ w) (_hu : 1 ≤ u) (hR₀ : 1 ≤ R₀)
    (layout : CompactRecursiveLayout shape n a₀ (bits u j) ρ left right)
    (hGuard : 1 ≤ shape.guard) (hGuardChunk : shape.guard + 1 ≤ shape.chunk)
    (hRecord : shape.bits + 1 ≤ shape.payload) (hPayload : shape.payload = 2 ^ o * (3 * (r * w)))
    (D : ℕ)
    (hp : CompactLayoutPacked layout (rowsAt R₀ j) D)
    (hfit : ∀ i < bits u (j + 1), (o + a₀) + ρ + shape.chunk * i < o + n)
    (child : Fin m → ZArr (Fin (rowsAt R₀ j) × Fin r) (o + n) → ZArr (Fin (rowsAt R₀ j) × Fin r) (o + n))
    (ins : Instr) (hfit' : ins.Fit) (hmono : ins.IsMono) :
    MonoSpecL body (monoProgC hQ ins) (compactBasisRest shape o r) j u shape.chunk ρ (o + a₀)
      (shape.chunk * bits u (j + 1)) (rowsAt R₀ (j + 1)) (o + n) r w (k := bits u j)
      (actMap (o + a₀) ρ shape.chunk (bits u (j + 1)) (o + n) hfit) child Tc ins
      (monoCostC (Ka := Ka) layout hGuard hGuardChunk (rowsAt_pos hR₀ j) hRecord D hp (nT CompactBReg)
        o r w j u (o + a₀) R₀ (o + n) ins) := by
  have hK : 1 ≤ shape.chunk := by have := hGuardChunk; omega
  set e := actMap (o + a₀) ρ shape.chunk (bits u (j + 1)) (o + n) hfit with he
  have he' : e = compactOffsetEmbedding o (compactRecursiveBits layout) := by
    funext i
    apply Fin.ext
    simp only [he, actMap, compactOffsetEmbedding, compactRecursiveBits, Fin.natAdd]
    omega
  cases ins with
  | factor fw g => exact absurd hmono id
  | gate g => exact absurd hmono id
  | phase fw i c => exact phaseInstr_monoSpecL body (by omega) hr hw hK hfit child fw i c
  | xor fw i j' =>
    have hij : i ≠ j' := hfit'
    refine framed_spec body _ fw e child _ (pullM e (Networks.Certificates.T16.Impl.xorMap i j'))
      _ (fun B => rfl) fun v S Z hL hpar hrest hx => ?_
    obtain ⟨v', c, hu', hc, hex⟩ := compactBasisW_exec body hQ layout i hGuard hGuardChunk
      (rowsAt_pos hR₀ j) hRecord (by omega) hPayload D hp fw _ (xor_pivot hij) Z v S hL hpar
      (fun z => hrest (.bc z) (by simp)) (hrest .tmp (by simp)) hx
    rw [← he', basisMap_xor hij] at hex
    exact ⟨v', c, hu', hc, hex⟩
  | trans fw tv =>
    have h : ∃ x, tv x = 0 := hfit'
    simp only [monoProgC, monoCostC, h, ↓reduceDIte]
    refine framed_spec body _ fw e child _ (pullM e (fun t => t + tv)) _ (fun B => rfl)
      fun v S Z hL hpar hrest hZ => ?_
    obtain ⟨v', c, hu', hc, hex⟩ := transW_exec body hQ layout (Fin.find _ h) hGuard hGuardChunk
      (rowsAt_pos hR₀ j) hRecord (by omega) hPayload D hp fw tv (Fin.find_spec h) Z v S hL hpar
      (fun z => hrest (.bc z) (by simp)) (hrest .tmp (by simp)) (hrest (.wtmp fw) (by simp)) hZ
    rw [← he'] at hex
    exact ⟨v', c, hu', hc, hex⟩

end MonoC

end

end IntegerMultBounds.MathlibTM2.LayerMachine
