module

public import IntegerMultBounds.MathlibTM2.Stack
public import IntegerMultBounds.MathlibTM2.Tape
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Fintype.Option
public import Mathlib.Tactic.DeriveFintype

/-!
# The bridge machine

A structured stack program that multiplies naturals given in Mathlib's encoding by running an
`IntegerMultBounds.Machine.Program` on pairs of stacks:

1. split the input into the bits of the two factors and pad both to a common length `n ≥ 1`,
   most significant bit first;
2. write `x # y` on the right stack of tape 0;
3. simulate the multitape program, one transition per loop iteration;
4. drain tape 0 left to right, keeping its bit symbols and dropping leading zeroes, onto the
   output stack, which then holds the least-significant-first encoding of the product;
5. empty every other stack and restore the initial local state.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack

/-- Stacks: the input, the output, four bit stacks, and two stacks per simulated tape. -/
inductive BK (t : ℕ) where
  | inp
  | out
  | bit (j : Fin 4)
  | lt (i : Fin t)
  | rt (i : Fin t)
  deriving DecidableEq, Fintype

/-- Stack alphabets. -/
abbrev BΓ {t : ℕ} (a : ℕ) : BK t → Type
  | .inp => Bool ⊕ Bool
  | .out => Bool
  | .bit _ => Bool
  | .lt _ => Fin (a + 4)
  | .rt _ => Fin (a + 4)

/-- Local state. -/
structure BS (t q a : ℕ) where
  flag : Bool
  ib : Option (Bool ⊕ Bool)
  x : Option Bool
  y : Option Bool
  sym : Option (Fin (a + 4))
  lead : Bool
  st : Fin q
  scan : Fin t → Fin (a + 4)
  nxt : Option (Fin q × (Fin t → Fin (a + 4) × Move))

/-- `BS` as a product, for its `Fintype` instance. -/
def BS.equiv (t q a : ℕ) : BS t q a ≃ Bool × Option (Bool ⊕ Bool) × Option Bool × Option Bool ×
    Option (Fin (a + 4)) × Bool × Fin q × (Fin t → Fin (a + 4)) ×
    Option (Fin q × (Fin t → Fin (a + 4) × Move)) where
  toFun v := (v.flag, v.ib, v.x, v.y, v.sym, v.lead, v.st, v.scan, v.nxt)
  invFun p := ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2.1, p.2.2.2.2.2.1, p.2.2.2.2.2.2.1,
    p.2.2.2.2.2.2.2.1, p.2.2.2.2.2.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance (t q a : ℕ) : Fintype (BS t q a) := Fintype.ofEquiv _ (BS.equiv t q a).symm

variable {t q a : ℕ}

set_option linter.unusedSimpArgs false

/-- Straight-line code and programs of the bridge machine. -/
abbrev Act (t q a : ℕ) := Action (BΓ (t := t) a) (BS t q a)
abbrev Pr (t q a : ℕ) := Prog Unit (BΓ (t := t) a) (BS t q a)

/-! ### Stores, grouped by kind of stack -/

/-- The contents of all stacks. -/
@[ext]
structure Stacks (t a : ℕ) where
  inp : List (Bool ⊕ Bool)
  out : List Bool
  b0 : List Bool
  b1 : List Bool
  b2 : List Bool
  b3 : List Bool
  L : Fin t → List (Fin (a + 4))
  R : Fin t → List (Fin (a + 4))

/-- The stack function of a `Stacks` record. -/
def Stacks.get (S : Stacks t a) : ∀ k : BK t, List (BΓ a k)
  | .inp => S.inp
  | .out => S.out
  | .bit j => ![S.b0, S.b1, S.b2, S.b3] j
  | .lt i => S.L i
  | .rt i => S.R i

/-- The store with local state `v` and stacks `S`. -/
def mk (v : BS t q a) (S : Stacks t a) : Store (BΓ (t := t) a) (BS t q a) := ⟨v, S.get⟩

@[simp] lemma mk_var (v : BS t q a) (S : Stacks t a) : (mk v S).var = v := rfl
@[simp] lemma mk_stk (v : BS t q a) (S : Stacks t a) : (mk v S).stk = S.get := rfl

@[simp] lemma get_inp (S : Stacks t a) : S.get .inp = S.inp := rfl
@[simp] lemma get_out (S : Stacks t a) : S.get .out = S.out := rfl
@[simp] lemma get_b0 (S : Stacks t a) : S.get (.bit 0) = S.b0 := rfl
@[simp] lemma get_b1 (S : Stacks t a) : S.get (.bit 1) = S.b1 := rfl
@[simp] lemma get_b2 (S : Stacks t a) : S.get (.bit 2) = S.b2 := rfl
@[simp] lemma get_b3 (S : Stacks t a) : S.get (.bit 3) = S.b3 := rfl
@[simp] lemma get_lt (S : Stacks t a) (i : Fin t) : S.get (.lt i) = S.L i := rfl
@[simp] lemma get_rt (S : Stacks t a) (i : Fin t) : S.get (.rt i) = S.R i := rfl

lemma update_inp (S : Stacks t a) (l : List (Bool ⊕ Bool)) :
    Function.update S.get .inp l = Stacks.get { S with inp := l } := by
  funext k; cases k <;> simp [Stacks.get, Function.update]

lemma update_out (S : Stacks t a) (l : List Bool) :
    Function.update S.get .out l = Stacks.get { S with out := l } := by
  funext k; cases k <;> simp [Stacks.get, Function.update]

lemma update_b0 (S : Stacks t a) (l : List Bool) :
    Function.update S.get (.bit 0) l = Stacks.get { S with b0 := l } := by
  funext k
  rcases k with _ | _ | j | _ | _ <;> try simp [Stacks.get, Function.update]
  fin_cases j <;> simp [Stacks.get, Function.update]

lemma update_b1 (S : Stacks t a) (l : List Bool) :
    Function.update S.get (.bit 1) l = Stacks.get { S with b1 := l } := by
  funext k
  rcases k with _ | _ | j | _ | _ <;> try simp [Stacks.get, Function.update]
  fin_cases j <;> simp [Stacks.get, Function.update]

lemma update_b2 (S : Stacks t a) (l : List Bool) :
    Function.update S.get (.bit 2) l = Stacks.get { S with b2 := l } := by
  funext k
  rcases k with _ | _ | j | _ | _ <;> try simp [Stacks.get, Function.update]
  fin_cases j <;> simp [Stacks.get, Function.update]

lemma update_b3 (S : Stacks t a) (l : List Bool) :
    Function.update S.get (.bit 3) l = Stacks.get { S with b3 := l } := by
  funext k
  rcases k with _ | _ | j | _ | _ <;> try simp [Stacks.get, Function.update]
  fin_cases j <;> simp [Stacks.get, Function.update]

lemma update_lt (S : Stacks t a) (i : Fin t) (l : List (Fin (a + 4))) :
    Function.update S.get (.lt i) l = Stacks.get { S with L := Function.update S.L i l } := by
  funext k
  cases k with
  | lt i' =>
    by_cases h : i' = i
    · subst h; simp [Stacks.get]
    · simp [Stacks.get, Function.update, h]
  | _ => simp [Stacks.get, Function.update]

lemma update_rt (S : Stacks t a) (i : Fin t) (l : List (Fin (a + 4))) :
    Function.update S.get (.rt i) l = Stacks.get { S with R := Function.update S.R i l } := by
  funext k
  cases k with
  | rt i' =>
    by_cases h : i' = i
    · subst h; simp [Stacks.get]
    · simp [Stacks.get, Function.update, h]
  | _ => simp [Stacks.get, Function.update]

/-- `Action.run` on grouped stores. -/
@[simp] lemma run_done (v : BS t q a) (S : Stacks t a) : (Action.done : Act t q a).run (mk v S) = mk v S :=
  rfl

/-! ### The phases -/

/-- Record in `flag` whether stack `k` is nonempty. -/
def peekFlag (k : BK t) : Act t q a := .peek k (fun v o => { v with flag := o.isSome }) .done

/-- Pop an input symbol; push its bit onto `bit 0` (first factor) or `bit 1` (second factor). -/
def splitStep : Act t q a :=
  .pop .inp (fun v o => { v with ib := o })
    (.branch (fun v => (v.ib.bind Sum.getLeft?).isSome)
      (.push (.bit 0) (fun v => (v.ib.bind Sum.getLeft?).getD false) (peekFlag .inp))
      (.branch (fun v => (v.ib.bind Sum.getRight?).isSome)
        (.push (.bit 1) (fun v => (v.ib.bind Sum.getRight?).getD false) (peekFlag .inp))
        (peekFlag .inp)))

/-- Move one bit from `bit j` to `bit j'`. -/
def moveBit (j j' : Fin 4) : Act t q a :=
  .pop (.bit j) (fun v o => { v with x := o })
    (.push (.bit j') (fun v => v.x.getD false) (peekFlag (.bit j)))

/-- Peek both `bit 2` and `bit 3`; `flag` records whether either is nonempty. -/
def lockPeek : Act t q a :=
  .peek (.bit 2) (fun v o => { v with x := o })
    (.peek (.bit 3) (fun v o => { v with y := o })
      (.load (fun v => { v with flag := v.x.isSome || v.y.isSome }) .done))

/-- Pop `bit 2` and `bit 3` together, reading a missing bit as `false`, and push the pair onto
`bit 0` and `bit 1`. -/
def lockStep : Act t q a :=
  .pop (.bit 2) (fun v o => { v with x := o })
    (.pop (.bit 3) (fun v o => { v with y := o })
      (.push (.bit 0) (fun v => v.x.getD false)
        (.push (.bit 1) (fun v => v.y.getD false) lockPeek)))

/-- Push one zero onto both `bit 0` and `bit 1` when `bit 0` is empty. -/
def padEmpty : Act t q a :=
  .peek (.bit 0) (fun v o => { v with x := o })
    (.branch (fun v => v.x.isNone)
      (.push (.bit 0) (fun _ => false) (.push (.bit 1) (fun _ => false) .done)) .done)

/-- Move one bit from `bit j` onto the right stack of tape `i` as a bit symbol. -/
def toTape (j : Fin 4) (i : Fin t) : Act t q a :=
  .pop (.bit j) (fun v o => { v with x := o })
    (.push (.rt i) (fun v => bitSymbol (v.x.getD false)) (peekFlag (.bit j)))

/-- Push the separator onto the right stack of tape `i`. -/
def pushSep (i : Fin t) : Act t q a := .push (.rt i) (fun _ => separator) .done

/-- Read every scanned symbol and look up the transition. -/
def peekScan (M : Program t q a) : Act t q a :=
  (List.finRange t).foldr
    (fun i acc => .peek (.rt i) (fun v o => { v with scan := Function.update v.scan i (o.getD blank) }) acc)
    (.load (fun v => { v with nxt := M.transition v.st v.scan }) .done)

/-- The symbol written on tape `i` by the pending transition. -/
def writeOf (i : Fin t) (v : BS t q a) : Fin (a + 4) := (v.nxt.map fun p => (p.2 i).1).getD blank

/-- The head move of tape `i` in the pending transition. -/
def moveOf (i : Fin t) (v : BS t q a) : Move := (v.nxt.map fun p => (p.2 i).2).getD .stay

/-- Apply the pending transition to tape `i`: write under the head and move. -/
def tapeAct (i : Fin t) : Act t q a :=
  .pop (.rt i) (fun v _ => v)
    (.branch (fun v => decide (moveOf i v = .right))
      (.push (.lt i) (writeOf i) .done)
      (.branch (fun v => decide (moveOf i v = .stay))
        (.push (.rt i) (writeOf i) .done)
        (.push (.rt i) (writeOf i)
          (.pop (.lt i) (fun v o => { v with sym := o })
            (.push (.rt i) (fun v => v.sym.getD blank) .done)))))

/-- Enter the pending transition's new state. -/
def setState : Act t q a := .load (fun v => { v with st := (v.nxt.map Prod.fst).getD v.st }) .done

/-- Stop the simulation loop. -/
def stopFlag : Act t q a := .load (fun v => { v with flag := false }) .done

/-- One simulated transition, or detection of halting. -/
def simIter (M : Program t q a) : Pr t q a :=
  .seq (.act (peekScan M))
    (.cond (fun v => v.nxt.isSome)
      (Prog.seqList ((List.finRange t).map (fun i => .act (tapeAct i)) ++ [.act setState]))
      (.act stopFlag))

/-- Simulate until the multitape program halts. -/
def simLoop (M : Program t q a) : Pr t q a :=
  .seq (.act (.load (fun v => { v with flag := true }) .done)) (.loop (·.flag) (simIter M))

/-- Move one cell from the left stack of tape `i` to its right stack. -/
def leftToRight (i : Fin t) : Act t q a :=
  .pop (.lt i) (fun v o => { v with sym := o })
    (.push (.rt i) (fun v => v.sym.getD blank) (peekFlag (.lt i)))

/-- Whether the popped symbol is a bit to be written to the output. -/
def emits (v : BS t q a) : Bool :=
  match v.sym.bind decodeBit with
  | some b => b || !v.lead
  | none => false

/-- Pop a cell of tape `i`; push its bit to the output unless it is blank or a leading zero. -/
def extractStep (i : Fin t) : Act t q a :=
  .pop (.rt i) (fun v o => { v with sym := o })
    (.branch emits
      (.push .out (fun v => (v.sym.bind decodeBit).getD false)
        (.load (fun v => { v with lead := false }) (peekFlag (.rt i))))
      (peekFlag (.rt i)))

/-- Pop and discard one symbol of stack `k`. -/
def dropStep (k : BK t) : Act t q a := .pop k (fun v _ => v) (peekFlag k)

/-- Repeat `b` while stack `k` is nonempty. -/
def drain (k : BK t) (b : Act t q a) : Pr t q a := .seq (.act (peekFlag k)) (.loop (·.flag) (.act b))

/-- Empty the stacks of every tape. -/
def cleanup : Pr t q a :=
  Prog.seqList ((List.finRange t).flatMap fun i =>
    [drain (.lt i) (dropStep (.lt i)), drain (.rt i) (dropStep (.rt i))])

/-- The initial local state. -/
def init (M : Program t q a) : BS t q a :=
  ⟨false, none, none, none, none, true, M.start, fun _ => blank, none⟩

/-- Tape 0. -/
def tape0 (M : Program t q a) : Fin t := ⟨0, M.tapes_pos⟩

/-- Prepare `x # y` on tape 0 from the Mathlib-encoded input. -/
def prepare (M : Program t q a) : Pr t q a :=
  Prog.seqList [
    drain .inp splitStep,
    drain (.bit 0) (moveBit 0 2),
    drain (.bit 1) (moveBit 1 3),
    .seq (.act lockPeek) (.loop (·.flag) (.act lockStep)),
    .act padEmpty,
    drain (.bit 1) (moveBit 1 3),
    drain (.bit 3) (toTape 3 (tape0 M)),
    .act (pushSep (tape0 M)),
    drain (.bit 0) (moveBit 0 2),
    drain (.bit 2) (toTape 2 (tape0 M))]

/-- Read the product off tape 0, clear every stack and restore the initial state. -/
def finish (M : Program t q a) : Pr t q a :=
  Prog.seqList [
    drain (.lt (tape0 M)) (leftToRight (tape0 M)),
    drain (.rt (tape0 M)) (extractStep (tape0 M)),
    cleanup,
    .act (.load (fun _ => init M) .done)]

/-- The bridge program. -/
def main (M : Program t q a) : Pr t q a := .seq (prepare M) (.seq (simLoop M) (finish M))

end IntegerMultBounds.MathlibTM2
