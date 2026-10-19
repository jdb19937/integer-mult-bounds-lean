module

public import IntegerMultBounds.Networks.CircuitTriples

/-! Compile the three-stage signed exchange by changing register names in the
middle inverse schedule. Renaming is a finite circuit construction, not a free
data movement operation on tapes. -/

@[expose] public section

namespace IntegerMultBounds.Networks.Circuit

variable {ι κ R : Type*} [DecidableEq ι] [DecidableEq κ] [CommRing R]

def Gate.rename (e : ι ≃ κ) (g : Gate ι R) : Gate κ R :=
  ⟨e g.target, g.terms.map (fun p => (e p.1, p.2))⟩

def rename (e : ι ≃ κ) (p : Program ι R) : Program κ R := p.map (Gate.rename e)

theorem Gate.run_rename (e : ι ≃ κ) (g : Gate ι R) (r : κ → R) :
    (g.rename e).run r ∘ e = g.run (r ∘ e) := by
  funext k
  simp only [Gate.run, Gate.rename, List.map_map, Function.comp_apply]
  by_cases hk : k = g.target
  · subst k; simp [Function.comp_def]
  · simp [Function.update_of_ne hk, Function.update_of_ne (e.injective.ne hk)]

theorem run_rename (e : ι ≃ κ) (p : Program ι R) (r : κ → R) :
    run (rename e p) r ∘ e = run p (r ∘ e) := by
  induction p generalizing r with
  | nil => rfl
  | cons g gs ih =>
    simp only [rename, List.map_cons, run_cons] at *
    rw [ih, Gate.run_rename]

omit [DecidableEq ι] [DecidableEq κ] [CommRing R] in
@[simp] theorem rename_length (e : ι ≃ κ) (p : Program ι R) :
    (rename e p).length = p.length := List.length_map _

def swapRole {n a c s : ℕ} : Role n a c s → Role n a c s
  | Sum.inl i => y i
  | Sum.inr (Sum.inl i) => x i
  | Sum.inr (Sum.inr i) => Sum.inr (Sum.inr i)

theorem swapRole_involutive {n a c s : ℕ} :
    Function.Involutive (@swapRole n a c s) := by
  intro k
  rcases k with i | i | i <;> rfl

def exchangeRoles (n a c s : ℕ) : Role n a c s ≃ Role n a c s where
  toFun := swapRole
  invFun := swapRole
  left_inv := swapRole_involutive
  right_inv := swapRole_involutive

omit [CommRing R] in
theorem banks_exchange {n a c s : ℕ} (X Y : Fin n → R) (A : Fin a → R)
    (C : Fin c → R) (S : Fin s → R) :
    banks X Y A C S ∘ exchangeRoles n a c s = banks Y X A C S := by
  funext k
  rcases k with i | i | i <;> rfl

/-- The reverse schedule with data-bank roles exchanged is a shear in the
opposite direction; arbitrary scratch and spectators are still restored. -/
theorem opposite_run {n a c s : ℕ} (V : Fin a → Fin n → R)
    (G : Fin c → Fin n → R) (J : Fin n → Fin a → R) (H : Fin n → Fin c → R)
    (reconstruct : ∀ X, mv J (mv V X) + mv H (mv G X) = X)
    (X Y : Fin n → R) (A : Fin a → R) (C : Fin c → R) (S : Fin s → R) :
    run (rename (exchangeRoles n a c s) (dirtyInverse V G J H)) (banks X Y A C S) =
      banks (X - Y) Y A C S := by
  have h := run_rename (exchangeRoles n a c s) (dirtyInverse V G J H) (banks X Y A C S)
  rw [banks_exchange, dirtyInverse_run, reconstruct] at h
  funext k
  have hk := congrFun h (exchangeRoles n a c s k)
  rcases k with i | i | i | i | i <;> exact hk

end IntegerMultBounds.Networks.Circuit
