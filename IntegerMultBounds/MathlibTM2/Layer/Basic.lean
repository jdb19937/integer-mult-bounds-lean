module

public import IntegerMultBounds.Networks.ComplexEndpoints

/-!
# The C layer on active bits

Arrays are complex functions of a spectator coordinate and `n` active bits. `kBit q i` is the
two-term translation kernel on active bit `i`, and `Cfull n` applies the forward kernel `C` on
every active bit. Kernels on distinct bits commute, so `Cfull` is the product over any
enumeration of the bits.
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Layer

open IntegerMultBounds.Networks BinaryWalsh BinaryPhase

/-- Arrays over spectators `X` with `n` active bits. -/
abbrev Arr (X : Type) (n : ℕ) := X × (Fin n → ZMod 2) → ℂ

variable {X : Type} {n : ℕ}

/-- Flip active bit `i`. -/
def flip (i : Fin n) (b : Fin n → ZMod 2) : Fin n → ZMod 2 := b + Pi.single i 1

@[simp] lemma flip_flip (i : Fin n) (b : Fin n → ZMod 2) : flip i (flip i b) = b := by
  funext j
  simp only [flip, Pi.add_apply]
  have h2 : (1 : ZMod 2) + 1 = 0 := by decide
  by_cases h : j = i
  · subst h; simp [add_assoc, h2]
  · simp [h]

lemma flip_comm (i j : Fin n) (b : Fin n → ZMod 2) : flip i (flip j b) = flip j (flip i b) := by
  simp only [flip]; abel

/-- The kernel with phase `q` on active bit `i`. -/
noncomputable def kBit (q : ZMod 4) (i : Fin n) : Arr X n →ₗ[ℂ] Arr X n where
  toFun f p := ((1 + phase q) / 2) * f p + ((1 - phase q) / 2) * f (p.1, flip i p.2)
  map_add' f g := by funext p; simp only [Pi.add_apply]; ring
  map_smul' c f := by funext p; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

@[simp] lemma kBit_apply (q : ZMod 4) (i : Fin n) (f : Arr X n) (p : X × (Fin n → ZMod 2)) :
    kBit q i f p = ((1 + phase q) / 2) * f p + ((1 - phase q) / 2) * f (p.1, flip i p.2) := rfl

lemma kBit_commute (q r : ZMod 4) (i j : Fin n) :
    Commute (kBit (X := X) q i) (kBit r j) := by
  change kBit q i * kBit r j = kBit r j * kBit q i
  apply LinearMap.ext
  intro f
  funext p
  change kBit q i (kBit r j f) p = kBit r j (kBit q i f) p
  simp only [kBit_apply, flip_comm i j]
  ring

/-- `C` on every active bit. -/
noncomputable def Cfull (X : Type) (n : ℕ) : Arr X n →ₗ[ℂ] Arr X n :=
  (List.ofFn (fun i : Fin n => kBit 1 i)).prod

/-- Kernels ignore the spectator: they commute with reindexing it. -/
lemma kBit_respec {Z : Type} (φ : Z → X) (q : ZMod 4) (i : Fin n) (f : Arr X n) :
    (fun p : Z × (Fin n → ZMod 2) => kBit q i f (φ p.1, p.2)) =
      kBit q i (fun p : Z × (Fin n → ZMod 2) => f (φ p.1, p.2)) := rfl

lemma prod_respec {Z : Type} (φ : Z → X) (q : ZMod 4) (l : List (Fin n)) (f : Arr X n) :
    (fun p : Z × (Fin n → ZMod 2) => (l.map (kBit q)).prod f (φ p.1, p.2)) =
      (l.map (kBit q)).prod (fun p : Z × (Fin n → ZMod 2) => f (φ p.1, p.2)) := by
  induction l generalizing f with
  | nil => rfl
  | cons i l ih =>
      simp only [List.map_cons, List.prod_cons, Module.End.mul_apply]
      rw [← ih]
      rfl

/-- `Cfull` commutes with reindexing the spectator. -/
lemma Cfull_respec {Z : Type} (φ : Z → X) (f : Arr X n) (z : Z) (b : Fin n → ZMod 2) :
    Cfull X n f (φ z, b) = Cfull Z n (fun p => f (φ p.1, p.2)) (z, b) := by
  have := congrFun (prod_respec φ 1 (List.finRange n) f) (z, b)
  simp only [Cfull, List.ofFn_eq_map] at this ⊢
  exact this

end IntegerMultBounds.MathlibTM2.Layer
