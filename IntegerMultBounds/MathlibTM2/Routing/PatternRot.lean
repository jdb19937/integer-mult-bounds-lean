module

public import IntegerMultBounds.MathlibTM2.Routing.PatternCode
public import IntegerMultBounds.MathlibTM2.Host.ClassMove

/-!
# Executed gate-controlled rotations

Both optional source-pattern interpreters, the gate/carry or gate/borrow code
pass and all cleanup are concrete host programs. Their costs are included in the
record-stream class move. AND and XOR are fixed choices of the Boolean gate;
the operand selectors, repetitions and inactive zeros are descriptor data.
-/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Node (moveRecs)
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget

variable {T Q A nf W L : ℕ} {U P : Type}
  {len : Fin nf → ℕ} {ι : PatternReg nf → Fin T}

def patternOffset (len : Fin nf → ℕ) (fs : Fin nf) (gate : Bool → Bool → Bool)
    (s : Fin 2 → Fin L → Option (Fin W)) (i : ℕ) : ℕ :=
  patternGateValue gate s (digit len fs i)

theorem patternOffset_high (fs ft : Fin nf) (horder : ft < fs) (gate : Bool → Bool → Bool)
    (s : Fin 2 → Fin L → Option (Fin W)) : OffHigh len ft (patternOffset len fs gate s) := by
  refine offHigh_of_digits {fs} (by simpa using horder) ?_
  intro i j h
  have hs := h fs (by simp)
  simp only [patternOffset, hs]

variable (body : P → Pr P T Q A U)

/-- Real pattern interpreters followed by gate/wrap automata compute the wrap classes. -/
theorem patternCode_rot (hι : Function.Injective ι) (fs ft : Fin nf)
    (hs : len fs = W) (ht : len ft = L) (gate : Bool → Bool → Bool)
    (s : Fin 2 → Fin L → Option (Fin W)) (neg output : Bool) :
    CodeSpec body
      (patternCode ι fs ft (if output then outC A neg (rGate gate) else inC A neg (rGate gate)))
      (fun f => ι (.fld f)) len (ι .st) (fun k => ∃ r, ι r = k) (PatternInv len ι s)
      (codeSel (if output then outC A neg (rGate gate) else inC A neg (rGate gate)))
      (fun i => rotCls ((if output then wrapOut else wrapIn) (len ft) neg
        (patternOffset len fs gate s i) (digit len ft i))) (patternCodeCost L W) := by
  have hspec := patternCode_spec body hι fs ft hs ht s
    (if output then outC A neg (rGate gate) else inC A neg (rGate gate))
  have heq : (fun i =>
      (if output then outC A neg (rGate gate) else inC A neg (rGate gate)).eval L
        ![digit len ft i, patternValue (s 0) (digit len fs i), patternValue (s 1) (digit len fs i)]) =
      (fun i => rotCls ((if output then wrapOut else wrapIn) (len ft) neg
        (patternOffset len fs gate s i) (digit len ft i))) := by
    funext i
    have h0 : digit len ft i < 2 ^ L := by
      rw [← ht]
      exact Nat.mod_lt _ (by positivity)
    cases output
    · simp only [Bool.false_eq_true, ite_false]
      rw [inC_eval neg (rGate gate) L _ h0, offv_gate, ht]
      rfl
    · simp only [ite_true]
      rw [outC_eval neg (rGate gate) L _ h0, offv_gate, ht]
      rfl
  rw [heq] at hspec
  exact hspec

/-- The uniform gate-controlled record-stream rotation. -/
def patternRotate (ι : PatternReg nf → Fin T) (fs ft : Fin nf)
    (gate : Bool → Bool → Bool) (neg : Bool)
    (src : Fin T) (dst aux : Fin 2 → Fin T) (out ctr tmp cnt ctmp : Fin T) : Pr P T Q A U :=
  classMove (patternCode ι fs ft (inC A neg (rGate gate)))
    (patternCode ι fs ft (outC A neg (rGate gate)))
    (codeSel (inC A neg (rGate gate))) (codeSel (outC A neg (rGate gate)))
    src dst aux out ctr tmp cnt ctmp (fun f => ι (.fld f)) (ι .st)

/-- A complete mixed-control rotation pass, restoring descriptors, source fields,
index counters and all scratch. Only the record stream changes. -/
theorem patternRotate_exec (hι : Function.Injective ι) (fs ft : Fin nf)
    (hs : len fs = W) (ht : len ft = L) (horder : ft < fs)
    (gate : Bool → Bool → Bool) (s : Fin 2 → Fin L → Option (Fin W)) (neg : Bool)
    {src out ctr tmp cnt ctmp : Fin T} {dst aux : Fin 2 → Fin T}
    (hr : MoveRegs (fun k => ∃ r, ι r = k) src dst aux out ctr tmp cnt ctmp)
    {R B q : ℕ} (hq : fieldOff len ft + len ft ≤ q) (hB : 1 ≤ B)
    {l : List (List (Fin (A + 4)))} (hl : l.length = R * 2 ^ q)
    (hlB : ∀ r ∈ l, r.length = B)
    {cc kk : List (Fin (A + 4))} (hcB : cc.length = B) (hkk : kk.length = R * 2 ^ q)
    (v : HS T Q A U) (S : Stacks T A)
    (hsrc : S.R src = l.flatten) (hctr : S.R ctr = cc) (hcnt : S.R cnt = kk)
    (htmp : S.R tmp = []) (hctmp : S.R ctmp = []) (hout : S.R out = [])
    (hdst : ∀ d, S.R (dst d) = []) (haux : ∀ d, S.R (aux d) = [])
    (hI : PatternInv len ι s S.R 0) :
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧
      m ≤ classMoveCost (nd := 2) (patternCodeCost L W) (patternCodeCost L W)
        (R * 2 ^ q) B len ∧
      Exec body (patternRotate ι fs ft gate neg src dst aux out ctr tmp cnt ctmp) (mk v S) m
        (mk v' { S with
          R := Function.update S.R src (moveRecs
            (rotPerm (R := R) neg (patternOffset_high (len := len) fs ft horder gate s) hq) l).flatten }) := by
  have hin := patternCode_rot body hι fs ft hs ht gate s neg false
  have houtCode := patternCode_rot body hι fs ft hs ht gate s neg true
  have hoff : OffHigh len ft (patternOffset len fs gate s) := patternOffset_high fs ft horder gate s
  have hlt : ∀ i, patternOffset len fs gate s i < 2 ^ len ft := by
    intro i
    rw [ht]
    exact patternGateValue_lt gate s (digit len fs i)
  refine classMove_exec body hin houtCode hr hB (rotPerm (R := R) neg hoff hq) ?_ ?_
    hl hlB hcB hkk v S hsrc hctr hcnt htmp hctmp hout hdst haux hI
  · intro i hi
    simp only [Nat.zero_add, permFun_of_lt _ hi]
    change rotCls (wrapOut (len ft) neg (patternOffset len fs gate s
      (rotIdx len ft neg (patternOffset len fs gate s) i))
      (digit len ft (rotIdx len ft neg (patternOffset len fs gate s) i))) = _
    rw [wrapOut_rotIdx neg hoff hlt]
    rfl
  · intro i hi i' hi' hc hii'
    simp only [Nat.zero_add, rotCls_inj] at hc
    rw [permFun_of_lt _ hi, permFun_of_lt _ hi']
    exact rotIdx_lt neg hoff hlt hii' hc

end IntegerMultBounds.MathlibTM2.Routing
