module

public import IntegerMultBounds.Networks.Certificates.T16.Streams.Charts

/-! Nine-bit chart operators on 73-bit arrays. An address of 73 bits splits into its first nine
local coordinates and the 64 remaining ones; `lift9 T` applies `T` to the local coordinates with
the others fixed. The lift is multiplicative and preserves equivalences, and it sends the
nine-bit translation kernel along `v` to the 73-bit kernel along `v` padded by zeros. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.T16.Streams

open BinaryWalsh BinaryPhase

/-- The local nine coordinates of an address. -/
def lowPart (x : Addr) : Address 9 := fun i => x (Fin.castAdd 64 i)

/-- The remaining 64 coordinates. -/
def highPart (x : Addr) : Address 64 := fun j => x (Fin.natAdd 9 j)

/-- Reassemble an address from its two parts. -/
def joinAddr (l : Address 9) (h : Address 64) : Addr := Fin.append l h

@[simp] theorem lowPart_join (l : Address 9) (h : Address 64) : lowPart (joinAddr l h) = l := by
  funext i; simp [lowPart, joinAddr]

@[simp] theorem highPart_join (l : Address 9) (h : Address 64) : highPart (joinAddr l h) = h := by
  funext j; simp [highPart, joinAddr]

@[simp] theorem join_parts (x : Addr) : joinAddr (lowPart x) (highPart x) = x := by
  funext i
  simp only [joinAddr]
  refine Fin.addCases (m := 9) (n := 64) (fun i => ?_) (fun j => ?_) i
  · simp [lowPart]
  · simp [highPart]

/-- Apply a nine-bit operator to the local coordinates. -/
noncomputable def lift9 (T : Arrays 9 →ₗ[ℂ] Arrays 9) : Arrays 73 →ₗ[ℂ] Arrays 73 where
  toFun f x := T (fun l => f (joinAddr l (highPart x))) (lowPart x)
  map_add' f g := by
    funext x
    simp only [Pi.add_apply]
    rw [show (fun l => f (joinAddr l (highPart x)) + g (joinAddr l (highPart x))) =
      (fun l => f (joinAddr l (highPart x))) + (fun l => g (joinAddr l (highPart x))) from rfl,
      map_add]
    rfl
  map_smul' c f := by
    funext x
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [show (fun l => c * f (joinAddr l (highPart x))) = c • (fun l => f (joinAddr l (highPart x)))
      from rfl, map_smul]
    rfl

theorem lift9_apply (T : Arrays 9 →ₗ[ℂ] Arrays 9) (f : Arrays 73) (x : Addr) :
    lift9 T f x = T (fun l => f (joinAddr l (highPart x))) (lowPart x) := rfl

theorem lift9_comp (T S : Arrays 9 →ₗ[ℂ] Arrays 9) (f : Arrays 73) :
    lift9 T (lift9 S f) = lift9 (T.comp S) f := by
  funext x
  simp only [lift9_apply, LinearMap.comp_apply, lowPart_join, highPart_join]

theorem lift9_id (f : Arrays 73) : lift9 LinearMap.id f = f := by
  funext x
  simp [lift9_apply]

/-- The lift of a nine-bit equivalence. -/
noncomputable def lift9Equiv (T : Arrays 9 ≃ₗ[ℂ] Arrays 9) : Arrays 73 ≃ₗ[ℂ] Arrays 73 :=
  { lift9 T.toLinearMap with
    invFun := lift9 T.symm.toLinearMap
    left_inv := fun f => by
      change lift9 T.symm.toLinearMap (lift9 T.toLinearMap f) = f
      rw [lift9_comp]
      have : T.symm.toLinearMap.comp T.toLinearMap = LinearMap.id := by
        ext g; simp
      rw [this, lift9_id]
    right_inv := fun f => by
      change lift9 T.toLinearMap (lift9 T.symm.toLinearMap f) = f
      rw [lift9_comp]
      have : T.toLinearMap.comp T.symm.toLinearMap = LinearMap.id := by
        ext g; simp
      rw [this, lift9_id] }

/-- Pad a local vector by zeros. -/
def padLow (v : Address 9) : Addr := joinAddr v 0

theorem joinAddr_add (l l' : Address 9) (h : Address 64) :
    joinAddr l h + padLow l' = joinAddr (l + l') h := by
  funext i
  simp only [joinAddr, padLow, Pi.add_apply]
  refine Fin.addCases (m := 9) (n := 64) (fun i => ?_) (fun j => ?_) i
  · simp
  · simp

/-- The local translation kernel lifts to the padded kernel. -/
theorem lift9_kernel (q : ZMod 4) (v : Address 9) (f : Arrays 73) :
    lift9 (kernel q v) f = kernel q (padLow v) f := by
  funext x
  rw [lift9_apply, kernel_apply, kernel_apply]
  congr 2
  · rw [join_parts]
  · rw [← join_parts x, joinAddr_add, lowPart_join, highPart_join]

end IntegerMultBounds.Networks.Certificates.T16.Streams
