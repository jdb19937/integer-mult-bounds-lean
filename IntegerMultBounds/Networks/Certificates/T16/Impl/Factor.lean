module

public import IntegerMultBounds.Networks.Certificates.T16.Impl.Call
public import IntegerMultBounds.Networks.Certificates.T16.Streams.Charts

/-! Splitting a kernel product into its local and exterior parts. A vector with no local part
translates only the 64 exterior coordinates, so its kernel commutes with every lifted nine-bit
operator. Characters split as products of a local and an exterior character, so a lifted
Fourier-diagonal nine-bit operator multiplies a 73-bit character by its local phase. Hence a
kernel product over vectors that are either local or exterior is the lift of the nine-bit
kernel product of its local factors, composed with the product of its exterior factors. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.T16.Impl

open BinaryWalsh BinaryPhase Streams Multiplicative

theorem lowPart_add (x y : Addr) : lowPart (x + y) = lowPart x + lowPart y := rfl

theorem joinAddr_add_high (l : Address 9) (h : Address 64) (w : Addr) (hw : lowPart w = 0) :
    joinAddr l h + w = joinAddr l (h + highPart w) := by
  conv_lhs => rw [← join_parts w, hw]
  rw [← joinAddr_add_add, add_zero]

/-- An exterior kernel commutes with every lifted nine-bit operator. -/
theorem lift9_kernel_exterior (T : Arrays 9 →ₗ[ℂ] Arrays 9) (q : ZMod 4) {w : Addr}
    (hw : lowPart w = 0) (f : Arrays 73) :
    lift9 T (BinaryWalsh.kernel q w f) = BinaryWalsh.kernel q w (lift9 T f) := by
  funext x
  have e : (fun l => BinaryWalsh.kernel q w f (joinAddr l (highPart x))) =
      ((1 + phase q) / 2) • (fun l => f (joinAddr l (highPart x))) +
        ((1 - phase q) / 2) • (fun l => f (joinAddr l (highPart x + highPart w))) := by
    funext l
    simp only [kernel_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, joinAddr_add_high l _ w hw]
  rw [lift9_apply, e, map_add, map_smul, map_smul, kernel_apply, lift9_apply, lift9_apply]
  rw [show lowPart (x + w) = lowPart x by rw [lowPart_add, hw, add_zero],
    show highPart (x + w) = highPart x + highPart w from rfl]
  rfl

theorem binary_join (a c : Address 9) (b d : Address 64) :
    Labels.binary 73 (joinAddr a b) (joinAddr c d) = Labels.binary 9 a c + Labels.binary 64 b d := by
  simp only [Labels.binary, Labels.form_apply, zero_mul, sub_zero]
  have e := Fin.sum_univ_add (a := 9) (b := 64) (fun i => joinAddr a b i * joinAddr c d i)
  simp only [joinAddr, Fin.append_left, Fin.append_right] at e
  exact e

theorem charVec_join (u : Addr) (l : Address 9) (h : Address 64) :
    charVec u (joinAddr l h) = charVec (lowPart u) l * charVec (highPart u) h := by
  change chi u (joinAddr l h) = chi (lowPart u) l * chi (highPart u) h
  rw [chi, ← join_parts u, binary_join, sign_add, lowPart_join, highPart_join]
  rfl

/-- A Fourier-diagonal nine-bit operator, lifted, multiplies each 73-bit character by the phase
of its local part. -/
theorem lift9_charVec (T : Arrays 9 →ₗ[ℂ] Arrays 9) (a : Address 9 → ℂ)
    (hT : ∀ v, T (charVec v) = a v • charVec v) (u : Addr) :
    lift9 T (charVec u) = a (lowPart u) • charVec u := by
  funext x
  have e : (fun l => charVec u (joinAddr l (highPart x))) =
      charVec (highPart u) (highPart x) • charVec (lowPart u) := by
    funext l
    rw [charVec_join, Pi.smul_apply, smul_eq_mul, mul_comm]
  rw [lift9_apply, e, map_smul, hT, Pi.smul_apply, Pi.smul_apply, Pi.smul_apply, smul_eq_mul,
    smul_eq_mul, smul_eq_mul, ← join_parts x, charVec_join, lowPart_join, highPart_join]
  ring

/-! ### Nine-bit kernel lists -/

/-- The product of nine-bit kernels of a list, applied head first. -/
noncomputable def kernelList : List (ZMod 4 × Address 9) → Arrays 9 →ₗ[ℂ] Arrays 9
  | [] => LinearMap.id
  | g :: gs => (kernelList gs).comp (BinaryWalsh.kernel g.1 g.2)

/-- The phase of a nine-bit kernel list at a frequency. -/
def kernelListPhase (gs : List (ZMod 4 × Address 9)) (v : Address 9) : ZMod 4 :=
  (gs.map fun g => g.1 * bitLift (Labels.binary 9 v g.2)).sum

theorem kernelList_char (gs : List (ZMod 4 × Address 9)) (v : Address 9) :
    kernelList gs (charVec v) = phase (kernelListPhase gs v) • charVec v := by
  induction gs with
  | nil => simp [kernelList, kernelListPhase]
  | cons g gs ih =>
    rw [kernelList, LinearMap.comp_apply, kernel_char, map_smul, ih, smul_smul, ← phase_add]
    simp only [kernelListPhase, List.map_cons, List.sum_cons]

/-- The local part of a kernel list along local vectors. -/
theorem lift9_kernelList_char (gs : List (ZMod 4 × Address 9)) (u : Addr) :
    lift9 (kernelList gs) (charVec u) = phase (kernelListPhase gs (lowPart u)) • charVec u :=
  lift9_charVec _ _ (kernelList_char gs) u

/-- **Splitting.** If a kernel product's phase is a nine-bit kernel list's phase on the local
part plus another kernel product's phase, the first product is the lifted list composed with
the second. -/
theorem basisOp_split (B : Fin 73 → Addr) (c : Fin 73 → ZMod 4) (gs : List (ZMod 4 × Address 9))
    (B' : Fin 73 → Addr) (c' : Fin 73 → ZMod 4)
    (h : ∀ u, phaseExp B c u = kernelListPhase gs (lowPart u) + phaseExp B' c' u) (f : Arrays 73) :
    basisOp B (ofAdd c) f = lift9 (kernelList gs) (basisOp B' (ofAdd c') f) := by
  refine eq_of_chars_fun (A := fun f => basisOp B (ofAdd c) f)
    (B := fun f => lift9 (kernelList gs) (basisOp B' (ofAdd c') f))
    (by simp) (fun x y => by simp) (fun z x => by simp) (by simp) (fun x y => by simp)
    (fun z x => by simp) (fun u => ?_) f
  rw [basisOp_char, basisOp_char, map_smul, lift9_kernelList_char, smul_smul, ← phase_add, h u,
    add_comm]

/-- An exterior kernel product commutes with every lifted nine-bit operator. -/
theorem lift9_basisOp_exterior (T : Arrays 9 →ₗ[ℂ] Arrays 9) (B : Fin 73 → Addr)
    (c : Fin 73 → ZMod 4) (hB : ∀ k, c k ≠ 0 → lowPart (B k) = 0) (f : Arrays 73) :
    lift9 T (basisOp B (ofAdd c) f) = basisOp B (ofAdd c) (lift9 T f) := by
  have key : ∀ S : Finset (Fin 73), ∀ f,
      lift9 T (basisOp B (ofAdd (∑ k ∈ S, Pi.single k (c k))) f) =
        basisOp B (ofAdd (∑ k ∈ S, Pi.single k (c k))) (lift9 T f) := by
    intro S
    induction S using Finset.induction_on with
    | empty => intro f; simp
    | insert a S ha ih =>
      intro f
      rw [Finset.sum_insert ha, ofAdd_add, map_mul, Module.End.mul_apply, Module.End.mul_apply,
        basisOp_single]
      by_cases hc : c a = 0
      · rw [hc]
        have hk : ∀ g : Arrays 73, BinaryWalsh.kernel 0 (B a) g = g := fun g => by
          funext x; simp [kernel_apply]
        rw [hk, hk, ih]
      · rw [lift9_kernel_exterior T _ (hB a hc), ih]
  have hc : ∑ k ∈ Finset.univ, Pi.single k (c k) = c := Finset.univ_sum_single c
  simpa [hc] using key Finset.univ f

end IntegerMultBounds.Networks.Certificates.T16.Impl
