module

public import IntegerMultBounds.Networks.GlobalGrouped
public import IntegerMultBounds.Networks.Mixer.Scalar

/-! The global three-stage mixer network on the physical three-coordinate layout.
Stages one and three run the forward mixer invocation and stage two the inverse
with exchanged data banks, each invocation on its own scratch bank. The whole
network sends `(X, Y)` to `(-Y, X)` and restores every scratch register. -/

@[expose] public section

namespace IntegerMultBounds.Networks.Mixer.Global

open GroupedCircuit Circuit GlobalCircuit GlobalGrouped Scalar

variable {B A C R : Type*} [DecidableEq B] [DecidableEq A] [DecidableEq C]
  [CommRing R] [DecidableEq R] {n a c M : ℕ}

section Local
variable (kind : Fin a → Kind n M) (G : Fin c → Fin n → R) (J : Fin n → Fin a → R)
  (H : Fin n → Fin c → R)

/-- The local grouped invocation of stage `j`. -/
def localGroups (j : Fin 3) : List (Group (Role n a c 0) R) :=
  if j = 1 then renameGroups (exchangeRoles n a c 0) (Scalar.inverse kind G J H)
  else Scalar.forward kind G J H

/-- The reconstruction identity of the mixer invocation. -/
def Reconstructs : Prop :=
  ∀ X : Fin n → R, mv J (mv (copyMatrix kind) X + mix kind (mv (copyMatrix kind) X)) +
    mv H (mv G X) = X

theorem forward_shear (hr : Reconstructs kind G J H) (X Y : Fin n → R) (A' : Fin a → R)
    (C' : Fin c → R) (S : Fin 0 → R) :
    runGroups (Scalar.forward kind G J H) (banks X Y A' C' S) = banks X (Y + X) A' C' S := by
  rw [forward_run, hr]

theorem opposite_shear (hr : Reconstructs kind G J H) (X Y : Fin n → R) (A' : Fin a → R)
    (C' : Fin c → R) (S : Fin 0 → R) :
    runGroups (renameGroups (exchangeRoles n a c 0) (Scalar.inverse kind G J H))
      (banks X Y A' C' S) = banks (X - Y) Y A' C' S := by
  have h := runGroups_rename (exchangeRoles n a c 0) (Scalar.inverse kind G J H)
    (banks X Y A' C' S)
  rw [banks_exchange, inverse_run, hr] at h
  funext k
  have hk := congrFun h (exchangeRoles n a c 0 k)
  rcases k with i | i | i | i | i <;> exact hk

end Local

section Invocations
variable (eB : Fin n ≃ B) (eA : Fin a ≃ A) (eC : Fin c ≃ C)
  (kind : Fin a → Kind n M) (G : Fin c → Fin n → R) (J : Fin n → Fin a → R)
  (H : Fin n → Fin c → R)

/-- One invocation placed on its coordinate line and its own scratch bank. -/
def invocationGroups (j : Fin 3) (q : B × B) : List (Group (World B A C) R) :=
  embedGroups (localEmbedding eB eA eC j q) (localGroups kind G J H j)

omit [CommRing R] [DecidableEq R] in
theorem contents_local (j : Fin 3) (q : B × B) (X Y : Address B → R)
    (S : Invocation B × (A ⊕ C) → R) :
    contents X Y S ∘ localEmbedding eB eA eC j q =
      banks (fun i => X (address j q (eB i))) (fun i => Y (address j q (eB i)))
        (fun i => S ((j, q), Sum.inl (eA i))) (fun i => S ((j, q), Sum.inr (eC i)))
        (Fin.elim0) := by
  funext k
  rcases k with i | i | i | i | i <;> try rfl
  exact Fin.elim0 i

/-- One invocation's effect on the whole register file. -/
theorem invocation_run (hr : Reconstructs kind G J H) (j : Fin 3) (q : B × B)
    (X Y : Address B → R) (S : Invocation B × (A ⊕ C) → R) :
    runGroups (invocationGroups eB eA eC kind G J H j q) (contents X Y S) =
      invocationEffect j q X Y S := by
  have hl : runGroups (localGroups kind G J H j)
      (contents X Y S ∘ localEmbedding eB eA eC j q) =
      invocationEffect j q X Y S ∘ localEmbedding eB eA eC j q := by
    by_cases hj : j = 1
    · simp only [localGroups, invocationEffect, hj, ↓reduceIte, contents_local,
        opposite_shear kind G J H hr]
      simp [onLine]
      rfl
    · simp only [localGroups, invocationEffect, hj, ↓reduceIte, contents_local,
        forward_shear kind G J H hr]
      simp [onLine]
      rfl
  funext k
  by_cases hk : ∃ i, localEmbedding eB eA eC j q i = k
  · obtain ⟨i, rfl⟩ := hk
    exact congrFun ((run_embedGroups (localEmbedding eB eA eC j q) _ _).trans hl) i
  · have hout : ∀ i, localEmbedding eB eA eC j q i ≠ k := by simpa using hk
    rw [invocationGroups, run_embedGroups_outside _ _ _ _ hout]
    rcases k with b | b | scratch
    · have hb : fixed j b ≠ q := by
        intro hb
        apply hout (x (eB.symm (varying j b)))
        simp [localEmbedding, localMap, x, ← hb]
      unfold invocationEffect
      split <;> simp [contents, onLine, hb]
    · have hb : fixed j b ≠ q := by
        intro hb
        apply hout (y (eB.symm (varying j b)))
        simp [localEmbedding, localMap, y, ← hb]
      unfold invocationEffect
      split <;> simp [contents, onLine, hb]
    · by_cases hj : j = 1 <;> simp [invocationEffect, hj, contents]

def partialStage (j : Fin 3) (qs : List (B × B)) : List (Group (World B A C) R) :=
  qs.flatMap (invocationGroups eB eA eC kind G J H j)

theorem onLines_step (j : Fin 3) (q : B × B) (qs : List (B × B))
    (hq : q ∉ qs) (base : Address B → R) (F : Address B → R → R) :
    onLines j qs (fun b => F b (onLine j q (fun b => F b (base b)) base b))
      (onLine j q (fun b => F b (base b)) base) =
      onLines j (q :: qs) (fun b => F b (base b)) base := by
  funext b
  by_cases he : fixed j b = q
  · simp [onLines, onLine, he, hq]
  · simp [onLines, onLine, he]

theorem partialStage_run (hr : Reconstructs kind G J H) (j : Fin 3) (qs : List (B × B))
    (hq : qs.Nodup) (X Y : Address B → R) (S : Invocation B × (A ⊕ C) → R) :
    runGroups (partialStage eB eA eC kind G J H j qs) (contents X Y S) =
      if j = 1 then contents (onLines j qs (X - Y) X) Y S
      else contents X (onLines j qs (Y + X) Y) S := by
  induction qs generalizing X Y with
  | nil =>
    simp only [partialStage, List.flatMap_nil]
    split <;> rfl
  | cons q qs ih =>
    obtain ⟨hmem, hnodup⟩ := List.nodup_cons.mp hq
    simp only [partialStage, List.flatMap_cons, runGroups_append]
    rw [invocation_run eB eA eC kind G J H hr]
    by_cases hj : j = 1
    · subst j
      simp only [invocationEffect, ↓reduceIte]
      rw [show runGroups (List.flatMap (invocationGroups eB eA eC kind G J H 1) qs)
          (contents (onLine 1 q (X - Y) X) Y S) = _ from ih hnodup _ Y]
      simp only [↓reduceIte]
      congr 1
      exact onLines_step 1 q qs hmem X (fun b x => x - Y b)
    · simp only [invocationEffect, hj, ↓reduceIte]
      rw [show runGroups (List.flatMap (invocationGroups eB eA eC kind G J H j) qs)
          (contents X (onLine j q (Y + X) Y) S) = _ from ih hnodup X _]
      simp only [hj, ↓reduceIte]
      congr 1
      exact onLines_step j q qs hmem Y (fun b y => y + X b)

def stage (j : Fin 3) : List (Group (World B A C) R) :=
  partialStage eB eA eC kind G J H j (keys eB)

theorem stage_run (hr : Reconstructs kind G J H) (j : Fin 3) (X Y : Address B → R)
    (S : Invocation B × (A ⊕ C) → R) :
    runGroups (stage eB eA eC kind G J H j) (contents X Y S) =
      if j = 1 then contents (X - Y) Y S else contents X (Y + X) S := by
  have full (f g : Address B → R) : onLines j (keys eB) f g = f := by
    funext b
    simp only [onLines, mem_keys, ↓reduceIte]
  rw [stage, partialStage_run eB eA eC kind G J H hr j _ (keys_nodup eB)]
  simp only [full]

/-- The three stages of the global mixer network. -/
def program : List (Group (World B A C) R) :=
  stage eB eA eC kind G J H 0 ++ stage eB eA eC kind G J H 1 ++ stage eB eA eC kind G J H 2

/-- The global mixer network performs the signed exchange and restores every
scratch bank, for arbitrary initial scratch. -/
theorem program_run (hr : Reconstructs kind G J H) (X Y : Address B → R)
    (S : Invocation B × (A ⊕ C) → R) :
    runGroups (program eB eA eC kind G J H) (contents X Y S) = contents (-Y) X S := by
  simp only [program, runGroups_append, stage_run eB eA eC kind G J H hr,
    show (0 : Fin 3) ≠ 1 by decide, show (2 : Fin 3) ≠ 1 by decide, ↓reduceIte]
  congr 1 <;> abel

end Invocations

end IntegerMultBounds.Networks.Mixer.Global
