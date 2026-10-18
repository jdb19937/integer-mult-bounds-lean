module

public import IntegerMultBounds.MathlibTM2.DFT.Statement
public import IntegerMultBounds.MathlibTM2.Stack

/-!
# Stack programs with `Γ'` input and output

A stack machine over keys `K` reads and writes its own alphabets `Γ k`. The keys `DK K` add a
`Γ'` input stack `gin` and a `Γ'` output stack `gout` (`DΓ`), so a machine over `DK K` can read
and write Mathlib's alphabet `Γ'` and run programs over `K` unchanged on the other stacks.

* `hostProg ι` runs a program over `K` on the keys `.host k`, calling procedure `ι f` for `f`.
  `exec_hostProg`: if the table `body'` over `DK K` holds `hostProg ι (body f)` at `ι f`, an
  execution from `s` to `t` in `n` steps is an execution of `hostProg ι p` from
  `hostExt s gi go` to `hostExt t gi go` in `n` steps, for any contents `gi`, `go` of `gin` and
  `gout` (`hostAct_run` for single actions). `hostCode` and `exec_hostCode` are the case of a
  program without calls, which runs in every table. Every store over `DK K` is `hostExt` of its
  host part (`hostExt_res`).
* `computableInTime`: a procedure table over `DK K` whose main procedure runs from `ea a` alone
  on `gin` to `eb (f a)` alone on `gout` within `time` (`ComputesWithin`) compiles, through
  `Stack.machine`, to `TM2ComputableInTime ea eb f`. `dftInTime_of_computes` specializes this to
  the discrete Fourier transform.
-/

@[expose] public section

open Turing Computability Asymptotics Filter IntegerMultBounds.MathlibTM2.Stack

namespace IntegerMultBounds.MathlibTM2.DFT

/-- Stack keys: the `Γ'` input `gin`, the `Γ'` output `gout`, and the keys of a host. -/
inductive DK (K : Type) where
  | gin
  | gout
  | host (k : K)
  deriving DecidableEq

variable {K : Type}

/-- `DK K` as a sum, for its `Fintype` instance. -/
def DK.equiv : DK K ≃ Bool ⊕ K where
  toFun
    | .gin => .inl false
    | .gout => .inl true
    | .host k => .inr k
  invFun
    | .inl false => .gin
    | .inl true => .gout
    | .inr k => .host k
  left_inv x := by cases x <;> rfl
  right_inv x := by rcases x with (_ | _) | k <;> rfl

instance [Fintype K] : Fintype (DK K) := Fintype.ofEquiv _ DK.equiv.symm

/-- Stack alphabets: `Γ'` on `gin` and `gout`, the host alphabets on the host keys. -/
abbrev DΓ (Γ : K → Type) : DK K → Type
  | .gin => Γ'
  | .gout => Γ'
  | .host k => Γ k

variable {Γ : K → Type} {σ P P' : Type}

/-! ### Host programs on the host keys -/

/-- A host action on the host keys. -/
def hostAct : Action Γ σ → Action (DΓ Γ) σ
  | .done => .done
  | .push k f a => .push (.host k) f (hostAct a)
  | .peek k f a => .peek (.host k) f (hostAct a)
  | .pop k f a => .pop (.host k) f (hostAct a)
  | .load f a => .load f (hostAct a)
  | .branch f a b => .branch f (hostAct a) (hostAct b)

/-- A host program on the host keys, with procedure `f` renamed `ι f`. -/
def hostProg (ι : P → P') : Prog P Γ σ → Prog P' (DΓ Γ) σ
  | .act a => .act (hostAct a)
  | .seq p q => .seq (hostProg ι p) (hostProg ι q)
  | .cond f p q => .cond f (hostProg ι p) (hostProg ι q)
  | .loop f p => .loop f (hostProg ι p)
  | .call f => .call (ι f)

/-- A host program without calls, on the host keys. -/
abbrev hostCode (p : Prog Empty Γ σ) : Prog P' (DΓ Γ) σ := hostProg Empty.elim p

/-- The stacks of a host store with `gi` on `gin` and `go` on `gout`. -/
def hostStk (S : ∀ k, List (Γ k)) (gi go : List Γ') : ∀ k : DK K, List (DΓ Γ k)
  | .gin => gi
  | .gout => go
  | .host k => S k

/-- A host store with `gi` on `gin` and `go` on `gout`. -/
def hostExt (s : Store Γ σ) (gi go : List Γ') : Store (DΓ Γ) σ := ⟨s.var, hostStk s.stk gi go⟩

/-- The host part of a store. -/
def hostRes (s : Store (DΓ Γ) σ) : Store Γ σ := ⟨s.var, fun k => s.stk (.host k)⟩

@[simp] lemma hostExt_var (s : Store Γ σ) (gi go : List Γ') : (hostExt s gi go).var = s.var := rfl

@[simp] lemma hostExt_gin (s : Store Γ σ) (gi go : List Γ') : (hostExt s gi go).stk .gin = gi :=
  rfl

@[simp] lemma hostExt_gout (s : Store Γ σ) (gi go : List Γ') :
    (hostExt s gi go).stk .gout = go := rfl

@[simp] lemma hostExt_host (s : Store Γ σ) (gi go : List Γ') (k : K) :
    (hostExt s gi go).stk (.host k) = s.stk k := rfl

theorem hostExt_res (s : Store (DΓ Γ) σ) : hostExt (hostRes s) (s.stk .gin) (s.stk .gout) = s :=
  Store.ext rfl (funext fun k => by cases k <;> rfl)

theorem hostStk_update [DecidableEq K] (S : ∀ k, List (Γ k)) (gi go : List Γ') (k : K)
    (l : List (Γ k)) :
    Function.update (hostStk S gi go) (.host k) l = hostStk (Function.update S k l) gi go := by
  funext j
  cases j with
  | gin => exact Function.update_of_ne (show (DK.gin : DK K) ≠ .host k from nofun) _ _
  | gout => exact Function.update_of_ne (show (DK.gout : DK K) ≠ .host k from nofun) _ _
  | host j =>
    by_cases h : j = k
    · subst h
      rw [Function.update_self]
      exact (Function.update_self (f := S) _ _).symm
    · rw [Function.update_of_ne (show (DK.host j : DK K) ≠ .host k from fun e => h (DK.host.inj e))]
      exact (Function.update_of_ne h l S).symm

/-- A host action on `hostExt s gi go` acts on `s` and keeps `gin` and `gout`. -/
theorem hostAct_run [DecidableEq K] (a : Action Γ σ) (s : Store Γ σ) (gi go : List Γ') :
    (hostAct a).run (hostExt s gi go) = hostExt (a.run s) gi go := by
  induction a generalizing s with
  | done => rfl
  | push k f a ih =>
    show (hostAct a).run
      ⟨s.var, Function.update (hostStk s.stk gi go) (.host k) (f s.var :: s.stk k)⟩ = _
    rw [hostStk_update]
    exact ih ⟨s.var, Function.update s.stk k (f s.var :: s.stk k)⟩
  | peek k f a ih => exact ih ⟨f s.var (s.stk k).head?, s.stk⟩
  | pop k f a ih =>
    show (hostAct a).run
      ⟨f s.var (s.stk k).head?, Function.update (hostStk s.stk gi go) (.host k) (s.stk k).tail⟩ = _
    rw [hostStk_update]
    exact ih ⟨f s.var (s.stk k).head?, Function.update s.stk k (s.stk k).tail⟩
  | load f a ih => exact ih ⟨f s.var, s.stk⟩
  | branch f a b iha ihb =>
    show (if f s.var then (hostAct a).run (hostExt s gi go)
      else (hostAct b).run (hostExt s gi go)) = hostExt (if f s.var then a.run s else b.run s) gi go
    cases f s.var
    · exact ihb s
    · exact iha s

/-- An execution of a host program is an execution of `hostProg ι` with the same step count;
the `Γ'` stacks are unchanged. -/
theorem exec_hostProg [DecidableEq K] {body : P → Prog P Γ σ} {body' : P' → Prog P' (DΓ Γ) σ}
    {ι : P → P'} (hbody : ∀ f, body' (ι f) = hostProg ι (body f)) {p : Prog P Γ σ}
    {s t : Store Γ σ} {n : ℕ} (h : Exec body p s n t) (gi go : List Γ') :
    Exec body' (hostProg ι p) (hostExt s gi go) n (hostExt t gi go) := by
  induction h with
  | act a s =>
    rw [← hostAct_run]
    exact .act _ _
  | seq _ _ ih₁ ih₂ => exact .seq ih₁ ih₂
  | cond_true hf _ ih => exact .cond_true hf ih
  | cond_false hf _ ih => exact .cond_false hf ih
  | loop_false hf => exact .loop_false hf
  | loop_true hf _ _ ih₁ ih₂ => exact .loop_true hf ih₁ ih₂
  | call _ ih =>
    refine .call ?_
    rw [hbody]
    exact ih

/-- A host program without calls runs on the host keys of every table. -/
theorem exec_hostCode [DecidableEq K] {body' : P' → Prog P' (DΓ Γ) σ} {p : Prog Empty Γ σ}
    {s t : Store Γ σ} {n : ℕ} (h : Exec Empty.elim p s n t) (gi go : List Γ') :
    Exec body' (hostCode p) (hostExt s gi go) n (hostExt t gi go) :=
  exec_hostProg (fun f => f.elim) h gi go

/-! ### Packaging as `TM2ComputableInTime` -/

section Package

variable [DecidableEq K] [Fintype K] [Fintype P] [Fintype σ]

/-- The main procedure turns `ea a` alone on `gin` into `eb (f a)` alone on `gout`, for every
`a`, in `m` steps with `m + 2 ≤ time |ea a|`. -/
def ComputesWithin (body : P → Prog P (DΓ Γ) σ) (main : P) (σ₀ : σ) {α β : Type}
    (ea : α → List Γ') (eb : β → List Γ') (f : α → β) (time : ℕ → ℕ) : Prop :=
  ∀ a, ∃ m, m + 2 ≤ time (ea a).length ∧
    Exec body (body main) (Store.only σ₀ .gin (ea a)) m (Store.only σ₀ .gout (eb (f a)))

/-- The compiled machine computes `f` within `time`. -/
noncomputable def computableInTime (body : P → Prog P (DΓ Γ) σ) (main : P) (σ₀ : σ)
    {α β : Type} (ea : α → List Γ') (eb : β → List Γ') (f : α → β) (time : ℕ → ℕ)
    (h : ComputesWithin body main σ₀ ea eb f time) : TM2ComputableInTime ea eb f where
  tm := machine body main .gin .gout σ₀
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := time
  outputsFun a := by
    have e := Classical.choose_spec (h a)
    have o := Exec.toOutputs (body := body) main .gin .gout σ₀ e.2 e.1
    simp only [Equiv.refl]
    erw [List.map_id, List.map_id]
    exact o

/-- A procedure table computing the transform within `time = O(N (log N) ^ (1 - κ))` gives
`DFTInTime κ`. -/
theorem dftInTime_of_computes (body : P → Prog P (DΓ Γ) σ) (main : P) (σ₀ : σ)
    (time : ℕ → ℕ) {κ : ℝ}
    (h : ComputesWithin body main σ₀ DFTInstance.encode encodeNatList DFTInstance.transform time)
    (htime : (fun N => (time N : ℝ)) =O[atTop] fun N : ℕ => (N : ℝ) * Real.log N ^ (1 - κ)) :
    DFTInTime κ :=
  ⟨computableInTime body main σ₀ _ _ _ time h, htime⟩

end Package

end IntegerMultBounds.MathlibTM2.DFT
