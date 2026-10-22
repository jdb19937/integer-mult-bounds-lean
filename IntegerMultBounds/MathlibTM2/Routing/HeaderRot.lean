module

public import IntegerMultBounds.MathlibTM2.Routing.HeaderCode
public import IntegerMultBounds.MathlibTM2.Host.ClassMove

/-!
# Executed live-header rotations

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
  {len : Fin nf → ℕ} {cf : Fin nf → Fin T} {ι : PatternReg 2 → Fin T}

/-- Gate offset read from the actual higher index window. -/
def headerOffset (o : ℕ) (gate : Bool → Bool → Bool)
    (s : Fin 2 → Fin L → Option (Fin W)) (i : ℕ) : ℕ :=
  patternGateValue gate s ((i / 2 ^ o) % 2 ^ W)

theorem headerOffset_high (ft : Fin nf) (o : ℕ)
    (ho : fieldOff len ft + len ft ≤ o) (gate : Bool → Bool → Bool)
    (s : Fin 2 → Fin L → Option (Fin W)) : OffHigh len ft (headerOffset o gate s) := by
  intro i j hij
  obtain ⟨e, he⟩ := Nat.exists_eq_add_of_le ho
  unfold headerOffset
  rw [he, Nat.pow_add, ← Nat.div_div_eq_div_mul i, ← Nat.div_div_eq_div_mul j, hij]

variable (body : P → Pr P T Q A U)

/-- Real pattern interpreters followed by gate/wrap automata compute the wrap classes. -/
theorem headerCode_rot (bank : HeaderBank cf ι ft) (fields : List (Fin nf)) (o : ℕ)
    (hchain : HeaderChain len o fields) (hwidth : (fields.map len).sum = W)
    (ht : len ft = L) (gate : Bool → Bool → Bool)
    (s : Fin 2 → Fin L → Option (Fin W)) (neg output : Bool) :
    CodeSpec body
      (headerPatternCode (fields.map cf) ι
        (if output then outC A neg (rGate gate) else inC A neg (rGate gate)))
      cf len (ι .st) (fun k => (∃ f, cf f = k) ∨ (∃ r, ι r = k))
      (HeaderInv len cf ι s)
      (codeSel (if output then outC A neg (rGate gate) else inC A neg (rGate gate)))
      (fun i => rotCls ((if output then wrapOut else wrapIn) (len ft) neg
        (headerOffset o gate s i) (digit len ft i)))
      (headerCodeCost L W fields.length) := by
  have hspec := headerCode_spec body bank fields o hchain hwidth ht s
    (if output then outC A neg (rGate gate) else inC A neg (rGate gate))
  have heq : (fun i =>
      (if output then outC A neg (rGate gate) else inC A neg (rGate gate)).eval L
        ![digit len ft i, patternValue (s 0) ((i / 2 ^ o) % 2 ^ W),
          patternValue (s 1) ((i / 2 ^ o) % 2 ^ W)]) =
      (fun i => rotCls ((if output then wrapOut else wrapIn) (len ft) neg
        (headerOffset o gate s i) (digit len ft i))) := by
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
def headerRotate (cf : Fin nf → Fin T) (ι : PatternReg 2 → Fin T)
    (fields : List (Fin nf))
    (gate : Bool → Bool → Bool) (neg : Bool)
    (src : Fin T) (dst aux : Fin 2 → Fin T) (out ctr tmp cnt ctmp : Fin T) : Pr P T Q A U :=
  classMove (headerPatternCode (fields.map cf) ι (inC A neg (rGate gate)))
    (headerPatternCode (fields.map cf) ι (outC A neg (rGate gate)))
    (codeSel (inC A neg (rGate gate))) (codeSel (outC A neg (rGate gate)))
    src dst aux out ctr tmp cnt ctmp cf (ι .st)

/-- A complete mixed-control rotation pass, restoring descriptors, source fields,
index counters and all scratch. Only the record stream changes. -/
theorem headerRotate_exec (bank : HeaderBank cf ι ft) (fields : List (Fin nf)) (o : ℕ)
    (hchain : HeaderChain len o fields) (hwidth : (fields.map len).sum = W)
    (ht : len ft = L) (ho : fieldOff len ft + len ft ≤ o)
    (gate : Bool → Bool → Bool) (s : Fin 2 → Fin L → Option (Fin W)) (neg : Bool)
    {src out ctr tmp cnt ctmp : Fin T} {dst aux : Fin 2 → Fin T}
    (hr : MoveRegs (fun k => (∃ f, cf f = k) ∨ (∃ r, ι r = k)) src dst aux out ctr tmp cnt ctmp)
    {R B q : ℕ} (hq : fieldOff len ft + len ft ≤ q) (hB : 1 ≤ B)
    {l : List (List (Fin (A + 4)))} (hl : l.length = R * 2 ^ q)
    (hlB : ∀ r ∈ l, r.length = B)
    {cc kk : List (Fin (A + 4))} (hcB : cc.length = B) (hkk : kk.length = R * 2 ^ q)
    (v : HS T Q A U) (S : Stacks T A)
    (hsrc : S.R src = l.flatten) (hctr : S.R ctr = cc) (hcnt : S.R cnt = kk)
    (htmp : S.R tmp = []) (hctmp : S.R ctmp = []) (hout : S.R out = [])
    (hdst : ∀ d, S.R (dst d) = []) (haux : ∀ d, S.R (aux d) = [])
    (hI : HeaderInv len cf ι s S.R 0) :
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧
      m ≤ classMoveCost (nd := 2) (headerCodeCost L W fields.length) (headerCodeCost L W fields.length)
        (R * 2 ^ q) B len ∧
      Exec body (headerRotate cf ι fields gate neg src dst aux out ctr tmp cnt ctmp) (mk v S) m
        (mk v' { S with
          R := Function.update S.R src (moveRecs
            (rotPerm (R := R) neg (headerOffset_high (len := len) ft o ho gate s) hq) l).flatten }) := by
  have hin := headerCode_rot body bank fields o hchain hwidth ht gate s neg false
  have houtCode := headerCode_rot body bank fields o hchain hwidth ht gate s neg true
  have hoff : OffHigh len ft (headerOffset o gate s) := headerOffset_high ft o ho gate s
  have hlt : ∀ i, headerOffset o gate s i < 2 ^ len ft := by
    intro i
    rw [ht]
    exact patternGateValue_lt gate s ((i / 2 ^ o) % 2 ^ W)
  refine classMove_exec body hin houtCode hr hB (rotPerm (R := R) neg hoff hq) ?_ ?_
    hl hlB hcB hkk v S hsrc hctr hcnt htmp hctmp hout hdst haux hI
  · intro i hi
    simp only [Nat.zero_add, permFun_of_lt _ hi]
    change rotCls (wrapOut (len ft) neg (headerOffset o gate s
      (rotIdx len ft neg (headerOffset o gate s) i))
      (digit len ft (rotIdx len ft neg (headerOffset o gate s) i))) = _
    rw [wrapOut_rotIdx neg hoff hlt]
    rfl
  · intro i hi i' hi' hc hii'
    simp only [Nat.zero_add, rotCls_inj] at hc
    rw [permFun_of_lt _ hi, permFun_of_lt _ hi']
    exact rotIdx_lt neg hoff hlt hii' hc

end IntegerMultBounds.MathlibTM2.Routing
