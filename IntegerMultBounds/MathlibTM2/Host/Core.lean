module

public import IntegerMultBounds.MathlibTM2.Stack
public import IntegerMultBounds.MathlibTM2.Tape

/-!
# Host programs

Host programs run on Mathlib `TM2` stacks: the Mathlib input and output stacks and two stacks per
tape of a bank of `T` tapes over the alphabet `Fin (A + 4)`. The local state carries the
registers of a multitape simulation (`Host.Foreign`) and an arbitrary finite `user` component.
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Host

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2


/-- Stacks: the input, the output, and two stacks per tape. -/
inductive HK (T : ℕ) where
  | inp
  | out
  | lt (i : Fin T)
  | rt (i : Fin T)
  deriving DecidableEq, Fintype

/-- Stack alphabets. -/
abbrev HΓ {T : ℕ} (A : ℕ) : HK T → Type
  | .inp => Bool ⊕ Bool
  | .out => Bool
  | .lt _ => Fin (A + 4)
  | .rt _ => Fin (A + 4)

/-- Local state: simulation registers and a user component. -/
structure HS (T Q A : ℕ) (U : Type) where
  flag : Bool
  sym : Option (Fin (A + 4))
  st : Fin Q
  scan : Fin T → Fin (A + 4)
  nxt : Option (Fin Q × (Fin T → Fin (A + 4) × Move))
  user : U

/-- `HS` as a product, for its `Fintype` instance. -/
def HS.equiv (T Q A : ℕ) (U : Type) : HS T Q A U ≃ Bool × Option (Fin (A + 4)) × Fin Q ×
    (Fin T → Fin (A + 4)) × Option (Fin Q × (Fin T → Fin (A + 4) × Move)) × U where
  toFun v := (v.flag, v.sym, v.st, v.scan, v.nxt, v.user)
  invFun p := ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2.1, p.2.2.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance (T Q A : ℕ) (U : Type) [Fintype U] : Fintype (HS T Q A U) :=
  Fintype.ofEquiv _ (HS.equiv T Q A U).symm

variable {T Q A : ℕ} {U : Type}

/-- Straight-line code and programs of host machines with procedure names `P`. -/
abbrev Act (T Q A : ℕ) (U : Type) := Action (HΓ (T := T) A) (HS T Q A U)
abbrev Pr (P : Type) (T Q A : ℕ) (U : Type) := Prog P (HΓ (T := T) A) (HS T Q A U)

/-- The contents of all stacks. -/
@[ext]
structure Stacks (T A : ℕ) where
  inp : List (Bool ⊕ Bool)
  out : List Bool
  L : Fin T → List (Fin (A + 4))
  R : Fin T → List (Fin (A + 4))

/-- The stack function of a `Stacks` record. -/
def Stacks.get (S : Stacks T A) : ∀ k : HK T, List (HΓ A k)
  | .inp => S.inp
  | .out => S.out
  | .lt i => S.L i
  | .rt i => S.R i

/-- The store with local state `v` and stacks `S`. -/
def mk (v : HS T Q A U) (S : Stacks T A) : Store (HΓ (T := T) A) (HS T Q A U) := ⟨v, S.get⟩

@[simp] lemma mk_var (v : HS T Q A U) (S : Stacks T A) : (mk v S).var = v := rfl
@[simp] lemma mk_stk (v : HS T Q A U) (S : Stacks T A) : (mk v S).stk = S.get := rfl
@[simp] lemma store_mk (v : HS T Q A U) (S : Stacks T A) :
    (⟨v, S.get⟩ : Store (HΓ (T := T) A) (HS T Q A U)) = mk v S := rfl

@[simp] lemma get_inp (S : Stacks T A) : S.get .inp = S.inp := rfl
@[simp] lemma get_out (S : Stacks T A) : S.get .out = S.out := rfl
@[simp] lemma get_lt (S : Stacks T A) (i : Fin T) : S.get (.lt i) = S.L i := rfl
@[simp] lemma get_rt (S : Stacks T A) (i : Fin T) : S.get (.rt i) = S.R i := rfl

lemma update_inp (S : Stacks T A) (l : List (Bool ⊕ Bool)) :
    Function.update S.get .inp l = Stacks.get { S with inp := l } := by
  funext k; cases k <;> simp [Stacks.get, Function.update]

lemma update_out (S : Stacks T A) (l : List Bool) :
    Function.update S.get .out l = Stacks.get { S with out := l } := by
  funext k; cases k <;> simp [Stacks.get, Function.update]

lemma update_lt (S : Stacks T A) (i : Fin T) (l : List (Fin (A + 4))) :
    Function.update S.get (.lt i) l = Stacks.get { S with L := Function.update S.L i l } := by
  funext k
  cases k with
  | lt i' =>
    by_cases h : i' = i
    · subst h; simp [Stacks.get]
    · simp [Stacks.get, Function.update, h]
  | _ => simp [Stacks.get, Function.update]

lemma update_rt (S : Stacks T A) (i : Fin T) (l : List (Fin (A + 4))) :
    Function.update S.get (.rt i) l = Stacks.get { S with R := Function.update S.R i l } := by
  funext k
  cases k with
  | rt i' =>
    by_cases h : i' = i
    · subst h; simp [Stacks.get]
    · simp [Stacks.get, Function.update, h]
  | _ => simp [Stacks.get, Function.update]

@[simp] lemma run_done (v : HS T Q A U) (S : Stacks T A) :
    (Action.done : Act T Q A U).run (mk v S) = mk v S := rfl

end IntegerMultBounds.MathlibTM2.Host
