module

public import IntegerMultBounds.MathlibTM2.Host.Core
public import IntegerMultBounds.MathlibTM2.Statement
public import IntegerMultBounds.MathlibTM2.Binary
public import Mathlib.Data.Set.Finite.List

/-!
# From host programs to the statement, and a dispatch for small inputs

`mulInTime_of_host` packages a host program (`IntegerMultBounds.MathlibTM2.Host.Pr`) that multiplies every input
pair within a time bound `O(n (log n) ^ (1 - κ))` as `IntegerMultBounds.MathlibTM2.MulInTime κ`. The machine is
`IntegerMultBounds.MathlibTM2.Stack.machine` of the program's procedure table, reading the Mathlib input stack
`.inp` and writing the Mathlib output stack `.out`; `HostMulWithin` is the per-input contract.

`dispatch n₀ body pm` turns a host program correct on inputs of length at least `n₀` into one
correct on every input. It pops up to `n₀` input symbols into a buffer `Buf n₀` held in the
finite local state. If the input runs out first, the buffer holds the whole input, and the
dispatch pushes the bits of the product from the state onto `.out`. Otherwise it pushes the
buffered symbols back onto `.inp`, which restores the input, and calls `body`.

The buffer is an extra user component: the dispatch's user state is `U × Buf n₀`. The
procedures of `body` run through `liftProg`, which reads and writes only the `U` part, and
`exec_lift` shows that a lifted program takes exactly the steps of the original and leaves the
extra component untouched. So `body` is stated over its own user state `U`.

The dispatch meets the time bound `dispatchTime n₀ time n = time n + (4 n₀ + 5)` at input length
`n`: the fast branch adds `4 n₀ + 5` steps to `body`, and the small branch finishes within
`4 n₀ + 5` steps.
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Fast

open IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host Computability Turing Asymptotics Filter

/-! ### Host programs give `MulInTime` -/

section Glue

variable {P : Type} {T Q A : ℕ} {U : Type}

/-- The host program `body`, started at procedure `pm` in local state `v₀`, turns the input store
of `(x, y)` into the output store of `x * y` in `m` steps with `m + 2 ≤ time n`, where `n` is the
input length. -/
def HostMulWithin (body : P → Pr P T Q A U) (pm : P) (v₀ : HS T Q A U) (time : ℕ → ℕ)
    (x y : ℕ) : Prop :=
  ∃ m, m + 2 ≤ time (pairEnc (x, y)).length ∧
    Exec body (body pm) (Store.only v₀ .inp (pairEnc (x, y))) m
      (Store.only v₀ .out (encodingNatBool.encode (x * y)))

/-- A host program multiplying every input pair within `time`, with
`time n = O(n (log n) ^ (1 - κ))`, gives `MulInTime κ`. -/
theorem mulInTime_of_host [Fintype P] [Fintype U] (body : P → Pr P T Q A U) (pm : P)
    (v₀ : HS T Q A U) (time : ℕ → ℕ) {κ : ℝ}
    (hrun : ∀ x y, HostMulWithin body pm v₀ time x y)
    (htime : (fun n => (time n : ℝ)) =O[atTop] fun n : ℕ => (n : ℝ) * Real.log n ^ (1 - κ)) :
    MulInTime κ := by
  refine ⟨{ tm := machine body pm .inp .out v₀
            inputAlphabet := Equiv.refl _
            outputAlphabet := Equiv.refl _
            time := time
            outputsFun := fun p => ?_ }, htime⟩
  have e := Classical.choose_spec (hrun p.1 p.2)
  have o := Exec.toOutputs (body := body) pm .inp .out v₀ e.2 e.1
  simp only [Equiv.refl]
  erw [List.map_id, List.map_id]
  exact o

/-- With `0 < κ`, a host program as in `mulInTime_of_host` gives the statement. -/
theorem statement_of_host [Fintype P] [Fintype U] (body : P → Pr P T Q A U) (pm : P)
    (v₀ : HS T Q A U) (time : ℕ → ℕ) {κ : ℝ} (hκ : 0 < κ)
    (hrun : ∀ x y, HostMulWithin body pm v₀ time x y)
    (htime : (fun n => (time n : ℝ)) =O[atTop] fun n : ℕ => (n : ℝ) * Real.log n ^ (1 - κ)) :
    Statement :=
  ⟨κ, hκ, mulInTime_of_host body pm v₀ time hrun htime⟩

end Glue

/-! ### Stores with one nonempty stack -/

section Only

variable {K : Type} [DecidableEq K] {Γ : K → Type} {σ : Type}

@[simp] lemma only_var (v : σ) (k : K) (l : List (Γ k)) : (Store.only v k l).var = v := rfl

@[simp] lemma only_stk_self (v : σ) (k : K) (l : List (Γ k)) : (Store.only v k l).stk k = l := by
  simp [Store.only]

lemma only_stk_of_ne (v : σ) {j k : K} (h : j ≠ k) (l : List (Γ k)) :
    (Store.only v k l).stk j = [] := by
  simp [Store.only, h]

lemma only_update (v : σ) (k : K) (l l' : List (Γ k)) :
    Function.update (Store.only v k l).stk k l' = (Store.only v k l').stk := by
  funext j
  by_cases h : j = k
  · subst h; simp
  · rw [Function.update_of_ne h, only_stk_of_ne v h, only_stk_of_ne v h]

lemma only_nil (v : σ) (k k' : K) : (Store.only v k [] : Store Γ σ) = Store.only v k' [] := by
  refine Store.ext rfl (funext fun j => ?_)
  by_cases h : j = k
  · subst h
    by_cases h' : j = k'
    · subst h'; rfl
    · rw [only_stk_self, only_stk_of_ne v h']
  · by_cases h' : j = k'
    · subst h'; rw [only_stk_self, only_stk_of_ne v h]
    · rw [only_stk_of_ne v h, only_stk_of_ne v h']

lemma run_pop_only (k : K) (f : σ → Option (Γ k) → σ) (v : σ) (l : List (Γ k)) :
    (Action.pop k f .done).run (Store.only v k l) = Store.only (f v l.head?) k l.tail := by
  simp only [Action.run, only_var, only_stk_self, only_update]; rfl

lemma run_push_load_only (k : K) (g : σ → Γ k) (h : σ → σ) (v : σ) (l : List (Γ k)) :
    (Action.push k g (.load h .done)).run (Store.only v k l) = Store.only (h v) k (g v :: l) := by
  simp only [Action.run, only_var, only_stk_self, only_update]; rfl

lemma run_load_only (h : σ → σ) (v : σ) (k : K) (l : List (Γ k)) :
    (Action.load h .done : Action Γ σ).run (Store.only v k l) = Store.only (h v) k l := rfl

/-- A loop moving a list `o` held in the local state onto stack `k`, one symbol per iteration,
which leaves `o.reverse` on top of the stack. The local state `st o` holds the list `o` still to
be moved. -/
theorem drain_exec {P : Type} {body : P → Prog P Γ σ} (k : K) (get : σ → List (Γ k))
    (pop1 : σ → σ) (d : Γ k) (N : ℕ) (st : List (Γ k) → σ)
    (hget : ∀ o, o.length ≤ N → get (st o) = o)
    (hpop : ∀ c o, (c :: o).length ≤ N → pop1 (st (c :: o)) = st o) :
    ∀ o acc : List (Γ k), o.length ≤ N →
      Exec body (.loop (fun v => !(get v).isEmpty)
          (.act (.push k (fun v => (get v).headD d) (.load pop1 .done))))
        (Store.only (st o) k acc) (2 * o.length + 1) (Store.only (st []) k (o.reverse ++ acc)) := by
  intro o
  induction o with
  | nil =>
      intro acc _
      have h₀ : get (st []) = [] := hget [] (Nat.zero_le _)
      have := Exec.loop_false (body := body) (f := fun v => !(get v).isEmpty)
        (p := .act (.push k (fun v => (get v).headD d) (.load pop1 .done)))
        (s := Store.only (st []) k acc) (by simp [h₀])
      simpa using this
  | cons c o ih =>
      intro acc hl
      have hg := hget (c :: o) hl
      have e₁ := Exec.act (body := body) (.push k (fun v => (get v).headD d) (.load pop1 .done))
        (Store.only (st (c :: o)) k acc)
      rw [run_push_load_only, hg, hpop c o hl, List.headD_cons] at e₁
      have e₂ := ih (c :: acc) (by simp at hl ⊢; omega)
      have := Exec.loop_true (body := body) (f := fun v => !(get v).isEmpty)
        (s := Store.only (st (c :: o)) k acc) (by simp [hg]) e₁ e₂
      exact this.cast (by simp; ring) (by simp)

end Only

/-! ### Running a program with an extra component in its local state -/

section Lift

variable {K : Type} [DecidableEq K] {Γ : K → Type} {σ σ' B P P' : Type}

/-- An action on local states `σ`, run on local states `σ' ≃ σ × B`; the `B` part stays. -/
def liftAct (e : σ' ≃ σ × B) : Action Γ σ → Action Γ σ'
  | .done => .done
  | .push k f a => .push k (fun w => f (e w).1) (liftAct e a)
  | .peek k f a => .peek k (fun w o => e.symm (f (e w).1 o, (e w).2)) (liftAct e a)
  | .pop k f a => .pop k (fun w o => e.symm (f (e w).1 o, (e w).2)) (liftAct e a)
  | .load f a => .load (fun w => e.symm (f (e w).1, (e w).2)) (liftAct e a)
  | .branch f a a' => .branch (fun w => f (e w).1) (liftAct e a) (liftAct e a')

/-- A program on local states `σ`, run on local states `σ' ≃ σ × B` with procedure names sent
along `ι`. -/
def liftProg (e : σ' ≃ σ × B) (ι : P → P') : Prog P Γ σ → Prog P' Γ σ'
  | .act a => .act (liftAct e a)
  | .seq p q => .seq (liftProg e ι p) (liftProg e ι q)
  | .cond f p q => .cond (fun w => f (e w).1) (liftProg e ι p) (liftProg e ι q)
  | .loop f p => .loop (fun w => f (e w).1) (liftProg e ι p)
  | .call f => .call (ι f)

lemma liftAct_run (e : σ' ≃ σ × B) (a : Action Γ σ) (s : Store Γ σ) (b : B) :
    (liftAct e a).run ⟨e.symm (s.var, b), s.stk⟩ = ⟨e.symm ((a.run s).var, b), (a.run s).stk⟩ := by
  induction a generalizing s with
  | done => rfl
  | push k f a ih =>
      simp only [liftAct, Action.run, Equiv.apply_symm_apply]
      exact ih ⟨s.var, Function.update s.stk k (f s.var :: s.stk k)⟩
  | peek k f a ih => simp only [liftAct, Action.run, Equiv.apply_symm_apply]; exact ih ⟨_, _⟩
  | pop k f a ih => simp only [liftAct, Action.run, Equiv.apply_symm_apply]; exact ih ⟨_, _⟩
  | load f a ih => simp only [liftAct, Action.run, Equiv.apply_symm_apply]; exact ih ⟨_, _⟩
  | branch f a a' iha iha' =>
      simp only [liftAct, Action.run, Equiv.apply_symm_apply]
      cases f s.var
      · exact iha' s
      · exact iha s

/-- A lifted program runs in exactly the steps of the original and keeps the extra component. -/
theorem exec_lift (e : σ' ≃ σ × B) (ι : P → P') {body : P → Prog P Γ σ}
    {body' : P' → Prog P' Γ σ'} (hbody : ∀ f, body' (ι f) = liftProg e ι (body f))
    {p : Prog P Γ σ} {s t : Store Γ σ} {n : ℕ} (h : Exec body p s n t) (b : B) :
    Exec body' (liftProg e ι p) ⟨e.symm (s.var, b), s.stk⟩ n ⟨e.symm (t.var, b), t.stk⟩ := by
  induction h with
  | act a s =>
      have := Exec.act (body := body') (liftAct e a) ⟨e.symm (s.var, b), s.stk⟩
      rwa [liftAct_run] at this
  | seq _ _ ih₁ ih₂ => exact .seq ih₁ ih₂
  | cond_true hf _ ih => exact .cond_true (by simpa using hf) ih
  | cond_false hf _ ih => exact .cond_false (by simpa using hf) ih
  | loop_false hf => exact .loop_false (by simpa using hf)
  | loop_true hf _ _ ih₁ ih₂ => exact .loop_true (by simpa using hf) ih₁ ih₂
  | call _ ih => exact .call (by rw [hbody]; exact ih)

end Lift

/-! ### Host states with an extra user component -/

section Split

variable {T Q A : ℕ} {U B : Type}

/-- A host state with the extra user component `b`. -/
def withBuf (v : HS T Q A U) (b : B) : HS T Q A (U × B) :=
  ⟨v.flag, v.sym, v.st, v.scan, v.nxt, (v.user, b)⟩

/-- Host states over `U × B` split into host states over `U` and the `B` component. -/
def splitUser (B : Type) : HS T Q A (U × B) ≃ HS T Q A U × B where
  toFun v := (⟨v.flag, v.sym, v.st, v.scan, v.nxt, v.user.1⟩, v.user.2)
  invFun p := withBuf p.1 p.2
  left_inv _ := rfl
  right_inv _ := rfl

/-- Change the extra user component. -/
def onBuf (g : B → B) (v : HS T Q A (U × B)) : HS T Q A (U × B) :=
  { v with user := (v.user.1, g v.user.2) }

@[simp] lemma onBuf_withBuf (g : B → B) (v : HS T Q A U) (b : B) :
    onBuf g (withBuf v b) = withBuf v (g b) := rfl

@[simp] lemma withBuf_user (v : HS T Q A U) (b : B) : (withBuf v b).user = (v.user, b) := rfl

lemma splitUser_symm (v : HS T Q A U) (b : B) : (splitUser B).symm (v, b) = withBuf v b := rfl

end Split

/-! ### The buffer -/

/-- Lists of length at most `n`. -/
abbrev BList (α : Type) (n : ℕ) := {l : List α // l.length ≤ n}

noncomputable instance BList.instFintype (α : Type) [Finite α] (n : ℕ) : Fintype (BList α n) :=
  @Fintype.ofFinite _ (List.finite_length_le α n).to_subtype

namespace BList

variable {α : Type} {n : ℕ}

/-- A list as a bounded list: itself if short enough, else empty. -/
def ofList (l : List α) : BList α n := if h : l.length ≤ n then ⟨l, h⟩ else ⟨[], Nat.zero_le n⟩

lemma ofList_val {l : List α} (h : l.length ≤ n) : (ofList l : BList α n).1 = l := by
  simp [ofList, h]

/-- Prepend a symbol if there is room. -/
def cons (c : α) (l : BList α n) : BList α n := if h : l.1.length < n then ⟨c :: l.1, h⟩ else l

lemma cons_val (c : α) {l : BList α n} (h : l.1.length < n) : (l.cons c).1 = c :: l.1 := by
  simp [cons, h]

/-- Drop the first symbol. -/
def tail (l : BList α n) : BList α n :=
  ⟨l.1.tail, by have := l.2; simp only [List.length_tail]; omega⟩

lemma tail_val (l : BList α n) : l.tail.1 = l.1.tail := rfl

end BList

/-- The product of the pair encoded by a word, or `0` if the word encodes no pair. -/
def prodOf (l : List (Bool ⊕ Bool)) : ℕ :=
  ((encodingProd encodingNatBool encodingNatBool).decode l).elim 0 fun p => p.1 * p.2

lemma prodOf_pairEnc (x y : ℕ) : prodOf (pairEnc (x, y)) = x * y := by
  simp [prodOf, pairEnc]

/-- The dispatch buffer: the input symbols read so far (most recent first), whether the input
ran out, and the output bits still to push (most significant first). -/
@[ext]
structure Buf (n₀ : ℕ) where
  inb : BList (Bool ⊕ Bool) n₀
  ended : Bool
  outb : BList Bool n₀
  deriving DecidableEq

/-- `Buf` as a product, for its `Fintype` instance. -/
def Buf.equiv (n₀ : ℕ) : Buf n₀ ≃ BList (Bool ⊕ Bool) n₀ × Bool × BList Bool n₀ where
  toFun b := (b.inb, b.ended, b.outb)
  invFun p := ⟨p.1, p.2.1, p.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable instance (n₀ : ℕ) : Fintype (Buf n₀) := Fintype.ofEquiv _ (Buf.equiv n₀).symm

namespace Buf

variable {n₀ : ℕ}

/-- The buffer with contents `r`, end flag `e` and pending output `o`. -/
def of (r : List (Bool ⊕ Bool)) (e : Bool) (o : List Bool) : Buf n₀ :=
  ⟨BList.ofList r, e, BList.ofList o⟩

/-- The empty buffer. -/
def empty : Buf n₀ := of [] false []

/-- Record a popped input symbol, or the end of the input. -/
def take (c : Option (Bool ⊕ Bool)) (b : Buf n₀) : Buf n₀ :=
  match c with
  | some c => { b with inb := b.inb.cons c }
  | none => { b with ended := true }

/-- Forget the most recent buffered input symbol. -/
def dropIn (b : Buf n₀) : Buf n₀ := { b with inb := b.inb.tail }

/-- Forget the next pending output bit. -/
def dropOut (b : Buf n₀) : Buf n₀ := { b with outb := b.outb.tail }

/-- Set the pending output to the product of the buffered input, most significant bit first. -/
def setOut (b : Buf n₀) : Buf n₀ :=
  { b with outb := BList.ofList (encodeNat (prodOf b.inb.1.reverse)).reverse }

@[simp] lemma of_ended (r : List (Bool ⊕ Bool)) (e : Bool) (o : List Bool) :
    (of r e o : Buf n₀).ended = e := rfl

lemma of_inb {r : List (Bool ⊕ Bool)} (h : r.length ≤ n₀) (e : Bool) (o : List Bool) :
    (of r e o : Buf n₀).inb.1 = r := BList.ofList_val h

lemma of_outb (r : List (Bool ⊕ Bool)) (e : Bool) {o : List Bool} (h : o.length ≤ n₀) :
    (of r e o : Buf n₀).outb.1 = o := BList.ofList_val h

lemma take_some {r : List (Bool ⊕ Bool)} (h : r.length < n₀) (c : Bool ⊕ Bool) (o : List Bool) :
    (of r false o : Buf n₀).take (some c) = of (c :: r) false o := by
  refine Buf.ext (Subtype.ext ?_) rfl rfl
  change ((of r false o : Buf n₀).inb.cons c).1 = (BList.ofList (c :: r) : BList _ n₀).1
  rw [BList.cons_val c (by rw [of_inb h.le]; exact h), of_inb h.le,
    BList.ofList_val (by simp; omega)]

lemma take_none (r : List (Bool ⊕ Bool)) (o : List Bool) :
    (of r false o : Buf n₀).take none = of r true o := rfl

lemma dropIn_of {c : Bool ⊕ Bool} {r : List (Bool ⊕ Bool)} (h : (c :: r).length ≤ n₀) (e : Bool)
    (o : List Bool) : (of (c :: r) e o : Buf n₀).dropIn = of r e o := by
  refine Buf.ext (Subtype.ext ?_) rfl rfl
  change (BList.ofList (c :: r) : BList _ n₀).1.tail = (BList.ofList r : BList _ n₀).1
  rw [BList.ofList_val h, BList.ofList_val (by simp at h ⊢; omega), List.tail_cons]

lemma dropOut_of (r : List (Bool ⊕ Bool)) (e : Bool) {c : Bool} {o : List Bool}
    (h : (c :: o).length ≤ n₀) : (of r e (c :: o) : Buf n₀).dropOut = of r e o := by
  refine Buf.ext rfl rfl (Subtype.ext ?_)
  change (BList.ofList (c :: o) : BList _ n₀).1.tail = (BList.ofList o : BList _ n₀).1
  rw [BList.ofList_val h, BList.ofList_val (by simp at h ⊢; omega), List.tail_cons]

lemma setOut_of {r : List (Bool ⊕ Bool)} (h : r.length ≤ n₀) (e : Bool) (o : List Bool) :
    (of r e o : Buf n₀).setOut = of r e (encodeNat (prodOf r.reverse)).reverse := by
  refine Buf.ext rfl rfl ?_
  change BList.ofList (encodeNat (prodOf (of r e o : Buf n₀).inb.1.reverse)).reverse = _
  rw [of_inb h]
  rfl

end Buf

/-! ### Binary lengths -/

lemma length_encodeNat (n : ℕ) : (encodeNat n).length = Nat.size n := by
  induction n using Nat.binaryRec with
  | zero => rfl
  | bit b m ih =>
      rw [IntegerMultBounds.MathlibTM2.encodeNat_bit]
      cases b
      · by_cases hm : m = 0
        · subst hm; simp
        · have hb : Nat.bit false m ≠ 0 := by simp [hm]
          rw [Nat.size_bit hb]
          simp [hm, ih]
      · have hb : Nat.bit true m ≠ 0 := by simp
        rw [Nat.size_bit hb]
        simp [ih]

lemma length_pairEnc (x y : ℕ) : (pairEnc (x, y)).length = Nat.size x + Nat.size y := by
  simp [pairEnc, encodingProd, encodingNatBool, length_encodeNat]

lemma size_mul_le (x y : ℕ) : Nat.size (x * y) ≤ Nat.size x + Nat.size y := by
  rw [Nat.size_le, pow_add]
  exact Nat.mul_lt_mul'' (Nat.lt_size_self x) (Nat.lt_size_self y)

lemma exists_pairEnc_length (n : ℕ) : ∃ x y : ℕ, (pairEnc (x, y)).length = n := by
  cases n with
  | zero => exact ⟨0, 0, by simp [length_pairEnc]⟩
  | succ n => exact ⟨2 ^ n, 0, by simp [length_pairEnc, Nat.size_pow]⟩

/-! ### The dispatch program -/

section Dispatch

variable {P : Type} {T Q A : ℕ} {U : Type} (n₀ : ℕ)

/-- Keep reading while the input has not run out and the buffer has room. -/
def readTest (v : HS T Q A (U × Buf n₀)) : Bool :=
  !v.user.2.ended && decide (v.user.2.inb.1.length < n₀)

/-- Pop one input symbol into the buffer, or record the end of the input. -/
def readAct : Act T Q A (U × Buf n₀) := .pop .inp (fun v c => onBuf (Buf.take c) v) .done

/-- Read up to `n₀` input symbols into the buffer. -/
def readLoop {P' : Type} : Pr P' T Q A (U × Buf n₀) := .loop (readTest n₀) (.act (readAct n₀))

/-- Push the pending output bits onto the output stack. -/
def outLoop {P' : Type} : Pr P' T Q A (U × Buf n₀) :=
  .loop (fun v => !v.user.2.outb.1.isEmpty)
    (.act (.push .out (fun v => v.user.2.outb.1.headD false) (.load (onBuf Buf.dropOut) .done)))

/-- Push the buffered input symbols back onto the input stack. -/
def backLoop {P' : Type} : Pr P' T Q A (U × Buf n₀) :=
  .loop (fun v => !v.user.2.inb.1.isEmpty)
    (.act (.push .inp (fun v => v.user.2.inb.1.headD (Sum.inl false))
      (.load (onBuf Buf.dropIn) .done)))

/-- The dispatch's main procedure: read the input up to `n₀` symbols; on a short input write the
product from the buffer, otherwise restore the input and call the main procedure `pm` of the
lifted program. -/
def dispatchMain (pm : P) : Pr (Option P) T Q A (U × Buf n₀) :=
  .seq (readLoop n₀)
    (.cond (fun v => v.user.2.ended)
      (.seq (.act (.load (onBuf Buf.setOut) .done))
        (.seq (outLoop n₀) (.act (.load (onBuf fun _ => Buf.empty) .done))))
      (.seq (backLoop n₀) (.call (some pm))))

/-- The dispatch procedure table: `none` is the main procedure, `some p` runs procedure `p` of
`body` on the `U` part of the user state. -/
def dispatch (body : P → Pr P T Q A U) (pm : P) : Option P → Pr (Option P) T Q A (U × Buf n₀)
  | none => dispatchMain n₀ pm
  | some p => liftProg (splitUser (Buf n₀)) some (body p)

/-- The time bound of the dispatch. -/
def dispatchTime (time : ℕ → ℕ) (n : ℕ) : ℕ := time n + (4 * n₀ + 5)

variable {P' : Type} {body' : P' → Pr P' T Q A (U × Buf n₀)} (v₀ : HS T Q A U)

lemma readAct_run (b : Buf n₀) (l : List (Bool ⊕ Bool)) :
    (readAct n₀ : Act T Q A (U × Buf n₀)).run (Store.only (withBuf v₀ b) .inp l) =
      Store.only (withBuf v₀ (b.take l.head?)) .inp l.tail := by
  rw [readAct, run_pop_only]; rfl

/-- The read loop on an input shorter than the room left in the buffer. -/
theorem readLoop_short : ∀ l r : List (Bool ⊕ Bool), r.length + l.length < n₀ →
    Exec body' (readLoop n₀) (Store.only (withBuf v₀ (Buf.of r false [])) .inp l)
      (2 * l.length + 3) (Store.only (withBuf v₀ (Buf.of (l.reverse ++ r) true [])) .inp []) := by
  intro l
  induction l with
  | nil =>
      intro r hr
      have hr' : r.length < n₀ := by simpa using hr
      have h₁ : readTest n₀ (withBuf v₀ (Buf.of r false [] : Buf n₀)) = true := by
        simp [readTest, Buf.of_inb hr'.le, hr']
      have h₂ : readTest n₀ (withBuf v₀ (Buf.of r true [] : Buf n₀)) = false := by
        simp [readTest]
      have e₁ := Exec.act (body := body') (readAct n₀)
        (Store.only (withBuf v₀ (Buf.of r false [])) .inp [])
      rw [readAct_run, List.head?_nil, List.tail_nil, Buf.take_none] at e₁
      have e₂ : Exec body' (readLoop n₀) (Store.only (withBuf v₀ (Buf.of r true [])) .inp []) 1
          (Store.only (withBuf v₀ (Buf.of r true [])) .inp []) := Exec.loop_false h₂
      have : Exec body' (readLoop n₀) (Store.only (withBuf v₀ (Buf.of r false [])) .inp []) (1 + 1 + 1)
          (Store.only (withBuf v₀ (Buf.of r true [])) .inp []) := Exec.loop_true h₁ e₁ e₂
      exact this.cast (by simp) (by simp)
  | cons c l ih =>
      intro r hr
      have hr' : r.length < n₀ := by simp at hr; omega
      have h₁ : readTest n₀ (withBuf v₀ (Buf.of r false [] : Buf n₀)) = true := by
        simp [readTest, Buf.of_inb hr'.le, hr']
      have e₁ := Exec.act (body := body') (readAct n₀)
        (Store.only (withBuf v₀ (Buf.of r false [])) .inp (c :: l))
      rw [readAct_run, List.head?_cons, List.tail_cons, Buf.take_some hr'] at e₁
      have e₂ := ih (c :: r) (by simp at hr ⊢; omega)
      have : Exec body' (readLoop n₀) (Store.only (withBuf v₀ (Buf.of r false [])) .inp (c :: l))
          (1 + (2 * l.length + 3) + 1)
          (Store.only (withBuf v₀ (Buf.of (l.reverse ++ c :: r) true [])) .inp []) :=
        Exec.loop_true h₁ e₁ e₂
      exact this.cast (by simp; ring) (by simp)

/-- The read loop on an input at least as long as the room left in the buffer. -/
theorem readLoop_long : ∀ l r : List (Bool ⊕ Bool), r.length ≤ n₀ → n₀ ≤ r.length + l.length →
    Exec body' (readLoop n₀) (Store.only (withBuf v₀ (Buf.of r false [])) .inp l)
      (2 * (n₀ - r.length) + 1)
      (Store.only (withBuf v₀ (Buf.of ((l.take (n₀ - r.length)).reverse ++ r) false [])) .inp
        (l.drop (n₀ - r.length))) := by
  intro l
  induction l with
  | nil =>
      intro r hr hrl
      have hk : n₀ - r.length = 0 := by simp at hrl; omega
      have h₂ : readTest n₀ (withBuf v₀ (Buf.of r false [] : Buf n₀)) = false := by
        simp [readTest, Buf.of_inb hr]; omega
      have : Exec body' (readLoop n₀) (Store.only (withBuf v₀ (Buf.of r false [])) .inp []) 1
          (Store.only (withBuf v₀ (Buf.of r false [])) .inp []) := Exec.loop_false h₂
      rw [hk]
      simpa using this
  | cons c l ih =>
      intro r hr hrl
      by_cases hlt : r.length < n₀
      · obtain ⟨k, hk⟩ : ∃ k, n₀ - r.length = k + 1 := ⟨n₀ - r.length - 1, by omega⟩
        have hk' : n₀ - (c :: r).length = k := by simp; omega
        have h₁ : readTest n₀ (withBuf v₀ (Buf.of r false [] : Buf n₀)) = true := by
          simp [readTest, Buf.of_inb hr, hlt]
        have e₁ := Exec.act (body := body') (readAct n₀)
          (Store.only (withBuf v₀ (Buf.of r false [])) .inp (c :: l))
        rw [readAct_run, List.head?_cons, List.tail_cons, Buf.take_some hlt] at e₁
        have e₂ := ih (c :: r) (by simp; omega) (by simp at hrl ⊢; omega)
        rw [hk'] at e₂
        have : Exec body' (readLoop n₀) (Store.only (withBuf v₀ (Buf.of r false [])) .inp (c :: l))
            (1 + (2 * k + 1) + 1)
            (Store.only (withBuf v₀ (Buf.of ((l.take k).reverse ++ c :: r) false [])) .inp
              (l.drop k)) :=
          Exec.loop_true h₁ e₁ e₂
        rw [hk]
        exact this.cast (by ring) (by simp)
      · have hk : n₀ - r.length = 0 := by omega
        have h₂ : readTest n₀ (withBuf v₀ (Buf.of r false [] : Buf n₀)) = false := by
          simp [readTest, Buf.of_inb hr, hlt]
        have : Exec body' (readLoop n₀) (Store.only (withBuf v₀ (Buf.of r false [])) .inp (c :: l))
            1 (Store.only (withBuf v₀ (Buf.of r false [])) .inp (c :: l)) := Exec.loop_false h₂
        rw [hk]
        simpa using this

/-- The output loop pushes the pending output bits. -/
theorem outLoop_exec (r : List (Bool ⊕ Bool)) (o acc : List Bool) (ho : o.length ≤ n₀) :
    Exec body' (outLoop n₀) (Store.only (withBuf v₀ (Buf.of r true o)) .out acc)
      (2 * o.length + 1) (Store.only (withBuf v₀ (Buf.of r true [])) .out (o.reverse ++ acc)) :=
  drain_exec (body := body') HK.out (fun v => v.user.2.outb.1) (onBuf Buf.dropOut) false n₀
    (fun o => withBuf v₀ (Buf.of r true o)) (fun o h => Buf.of_outb r true h)
    (fun c o h => by rw [onBuf_withBuf, Buf.dropOut_of r true h]) o acc ho

/-- The back loop pushes the buffered input symbols back onto the input stack. -/
theorem backLoop_exec (r acc : List (Bool ⊕ Bool)) (hr : r.length ≤ n₀) :
    Exec body' (backLoop n₀) (Store.only (withBuf v₀ (Buf.of r false [])) .inp acc)
      (2 * r.length + 1) (Store.only (withBuf v₀ Buf.empty) .inp (r.reverse ++ acc)) :=
  drain_exec (body := body') HK.inp (fun v => v.user.2.inb.1) (onBuf Buf.dropIn) (Sum.inl false)
    n₀ (fun r => withBuf v₀ (Buf.of r false [])) (fun o h => Buf.of_inb h false [])
    (fun c o h => by rw [onBuf_withBuf, Buf.dropIn_of h]) r acc hr


end Dispatch

/-! ### Correctness and time of the dispatch -/

section Correct

variable {P : Type} {T Q A : ℕ} {U : Type}

/-- The dispatch multiplies every input pair within `dispatchTime n₀ time`, given that `body`
does so within `time` on inputs of length at least `n₀`. -/
theorem dispatch_exec (body : P → Pr P T Q A U) (pm : P) (v₀ : HS T Q A U) (time : ℕ → ℕ)
    (n₀ : ℕ) (hfast : ∀ x y, n₀ ≤ (pairEnc (x, y)).length → HostMulWithin body pm v₀ time x y)
    (x y : ℕ) :
    HostMulWithin (dispatch n₀ body pm) none (withBuf v₀ Buf.empty) (dispatchTime n₀ time) x y := by
  by_cases hn : n₀ ≤ (pairEnc (x, y)).length
  · obtain ⟨m, hm, e⟩ := hfast x y hn
    unfold HostMulWithin
    generalize hl : pairEnc (x, y) = l at hn hm e ⊢
    have e₁ := readLoop_long n₀ (body' := dispatch n₀ body pm) v₀ l [] (by simp) (by simpa using hn)
    simp only [List.length_nil, Nat.sub_zero, List.append_nil] at e₁
    have e₂ := backLoop_exec n₀ (body' := dispatch n₀ body pm) v₀ (l.take n₀).reverse (l.drop n₀)
      (by simp)
    simp only [List.reverse_reverse, List.take_append_drop] at e₂
    have e₃ : Exec (dispatch n₀ body pm) (.call (some pm))
        (Store.only (withBuf v₀ Buf.empty) .inp l) (m + 2)
        (Store.only (withBuf v₀ Buf.empty) .out (encodingNatBool.encode (x * y))) :=
      .call (exec_lift (splitUser (Buf n₀)) some (fun _ => rfl) e Buf.empty)
    have hlen : (l.take n₀).reverse.length = n₀ := by simp; omega
    rw [hlen] at e₂
    refine ⟨_, ?_, Exec.seq e₁ (Exec.cond_false (f := fun v => v.user.2.ended) rfl
      (Exec.seq e₂ e₃))⟩
    simp only [dispatchTime]
    omega
  · replace hn : (pairEnc (x, y)).length < n₀ := by omega
    have hxy : Nat.size (x * y) ≤ (pairEnc (x, y)).length :=
      (size_mul_le x y).trans (length_pairEnc x y).ge
    have hprod : prodOf (pairEnc (x, y)) = x * y := prodOf_pairEnc x y
    unfold HostMulWithin
    generalize hl : pairEnc (x, y) = l at hn hxy hprod ⊢
    have e₁ := readLoop_short n₀ (body' := dispatch n₀ body pm) v₀ l [] (by simpa using hn)
    simp only [List.append_nil] at e₁
    have e₂ := Exec.act (body := dispatch n₀ body pm) (.load (onBuf Buf.setOut) .done)
      (Store.only (withBuf v₀ (Buf.of l.reverse true [])) .inp [])
    rw [run_load_only, onBuf_withBuf, Buf.setOut_of (by simp; omega), List.reverse_reverse,
      hprod] at e₂
    replace e₂ := e₂.cast rfl (only_nil _ HK.inp HK.out)
    have ho : (encodeNat (x * y)).reverse.length ≤ n₀ := by
      rw [List.length_reverse, length_encodeNat]; omega
    have e₃ := outLoop_exec n₀ (body' := dispatch n₀ body pm) v₀ l.reverse
      (encodeNat (x * y)).reverse [] ho
    simp only [List.reverse_reverse, List.append_nil] at e₃
    have e₄ := Exec.act (body := dispatch n₀ body pm) (.load (onBuf fun _ => Buf.empty) .done)
      (Store.only (withBuf v₀ (Buf.of l.reverse true [])) .out (encodeNat (x * y)))
    rw [run_load_only, onBuf_withBuf] at e₄
    refine ⟨_, ?_, Exec.seq e₁ (Exec.cond_true (f := fun v => v.user.2.ended) rfl
      (Exec.seq e₂ (Exec.seq e₃ e₄)))⟩
    rw [List.length_reverse, length_encodeNat] at *
    simp only [dispatchTime]
    omega

/-- `dispatchTime n₀ time` is `O(time)` once `time` is eventually positive. -/
theorem isBigO_dispatchTime (n₀ : ℕ) (time : ℕ → ℕ) (h : ∀ᶠ n in atTop, 1 ≤ time n) :
    (fun n => (dispatchTime n₀ time n : ℝ)) =O[atTop] fun n => (time n : ℝ) := by
  refine IsBigO.of_bound ((4 * n₀ + 6 : ℕ) : ℝ) ?_
  filter_upwards [h] with n hn
  rw [Real.norm_of_nonneg (Nat.cast_nonneg _), Real.norm_of_nonneg (Nat.cast_nonneg _)]
  have : dispatchTime n₀ time n ≤ (4 * n₀ + 6) * time n := by
    unfold dispatchTime; nlinarith
  exact_mod_cast this

/-- A time bound met on every input of every length `n ≥ n₀` is at least `2` there. -/
lemma two_le_time {body : P → Pr P T Q A U} {pm : P} {v₀ : HS T Q A U} {time : ℕ → ℕ} {n₀ : ℕ}
    (hfast : ∀ x y, n₀ ≤ (pairEnc (x, y)).length → HostMulWithin body pm v₀ time x y)
    {n : ℕ} (hn : n₀ ≤ n) : 2 ≤ time n := by
  obtain ⟨x, y, hxy⟩ := exists_pairEnc_length n
  obtain ⟨m, hm, -⟩ := hfast x y (hxy ▸ hn)
  rw [hxy] at hm
  omega

/-- A host program multiplying the inputs of length at least `n₀` within
`time n = O(n (log n) ^ (1 - κ))` gives `MulInTime κ`. -/
theorem mulInTime_of_dispatch [Fintype P] [Fintype U] (body : P → Pr P T Q A U) (pm : P)
    (v₀ : HS T Q A U) (time : ℕ → ℕ) (n₀ : ℕ) {κ : ℝ}
    (hfast : ∀ x y, n₀ ≤ (pairEnc (x, y)).length → HostMulWithin body pm v₀ time x y)
    (htime : (fun n => (time n : ℝ)) =O[atTop] fun n : ℕ => (n : ℝ) * Real.log n ^ (1 - κ)) :
    MulInTime κ := by
  have hpos : ∀ᶠ n in atTop, 1 ≤ time n :=
    eventually_atTop.2 ⟨n₀, fun n hn => by have := two_le_time hfast hn; omega⟩
  exact mulInTime_of_host (dispatch n₀ body pm) none (withBuf v₀ Buf.empty) (dispatchTime n₀ time)
    (dispatch_exec body pm v₀ time n₀ hfast) ((isBigO_dispatchTime n₀ time hpos).trans htime)

/-- A host program multiplying the inputs of length at least `n₀` within
`time n = O(n (log n) ^ (1 - κ))` for some `κ > 0` gives the statement. -/
theorem statement_of_dispatch [Fintype P] [Fintype U] (body : P → Pr P T Q A U) (pm : P)
    (v₀ : HS T Q A U) (time : ℕ → ℕ) (n₀ : ℕ) {κ : ℝ} (hκ : 0 < κ)
    (hfast : ∀ x y, n₀ ≤ (pairEnc (x, y)).length → HostMulWithin body pm v₀ time x y)
    (htime : (fun n => (time n : ℝ)) =O[atTop] fun n : ℕ => (n : ℝ) * Real.log n ^ (1 - κ)) :
    Statement :=
  ⟨κ, hκ, mulInTime_of_dispatch body pm v₀ time n₀ hfast htime⟩

end Correct

end IntegerMultBounds.MathlibTM2.Fast
