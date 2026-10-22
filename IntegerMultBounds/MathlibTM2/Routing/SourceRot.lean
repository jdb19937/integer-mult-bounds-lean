module

public import IntegerMultBounds.MathlibTM2.Routing.SourceCode
public import IntegerMultBounds.MathlibTM2.Host.ClassMove
public import IntegerMultBounds.MathlibTM2.Layer.CompactOffsets

/-!
# Actual source-controlled modular rotations of record streams

The source callbacks are concrete programs, not hypothesized offset oracles.
Their source field may be read at arbitrary descriptor positions and in arbitrary
order. The source must be above the rotated field, making the index map a global
bijection even on bad addresses. The host pass restores all registers except the
record stream and charges both source computations in its class-move cost.
-/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Node (moveRecs)
open IntegerMultBounds.MathlibTM2.Layer.CompactMasks
open IntegerMultBounds.MathlibTM2.Layer.CompactDigits
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget

variable {T Q A nf W n G : ℕ} {U P : Type}
  {len : Fin nf → ℕ} {ι : SourceReg nf → Fin T}

/-- The source offset is bounded by the compact target width. -/
theorem sourceValue_lt (fs : Fin nf) (hG : 0 < G) (s : Fin n → Fin W) (i : ℕ) :
    sourceValue len fs G s i < 2 ^ (n * G) := by
  exact placeVal_lt (fun _ _ h => Nat.mul_lt_mul_of_pos_right h hG) _ n

/-- Reading a higher source field meets the rotation's exact high-only condition. -/
theorem sourceValue_high (fs ft : Fin nf) (horder : ft < fs) (s : Fin n → Fin W) :
    OffHigh len ft (sourceValue len fs G s) := by
  refine offHigh_of_digits {fs} (by simpa using horder) ?_
  intro i j h
  have hs := h fs (by simp)
  simp only [sourceValue, hs]

variable (body : P → Pr P T Q A U)

/-- Concrete source-reading programs compute the input and output wrap classes. -/
theorem sourceCode_rot (hι : Function.Injective ι) (fs ft : Fin nf)
    (hs : len fs = W) (ht : len ft = n * G) (hW : 0 < W) (hG : 0 < G)
    (s : Fin n → Fin W) (neg output : Bool) :
    CodeSpec body
      (sourceCode ι fs ft (if output then outC A neg rPlain else inC A neg rPlain))
      (fun f => ι (.fld f)) len (ι .st) (fun k => ∃ r, ι r = k) (SourceInv len ι G s)
      (codeSel (if output then outC A neg rPlain else inC A neg rPlain))
      (fun i => rotCls ((if output then wrapOut else wrapIn) (len ft) neg
        (sourceValue len fs G s i) (digit len ft i))) (sourceCodeCost n W G) := by
  have hspec := sourceCode_spec body hι fs ft hs ht hW hG s
    (if output then outC A neg rPlain else inC A neg rPlain)
  have heq : (fun i => (if output then outC A neg rPlain else inC A neg rPlain).eval
      (n * G) ![digit len ft i, sourceValue len fs G s i]) =
      (fun i => rotCls ((if output then wrapOut else wrapIn) (len ft) neg
        (sourceValue len fs G s i) (digit len ft i))) := by
    funext i
    have h0 : digit len ft i < 2 ^ (n * G) := by
      rw [← ht]
      exact Nat.mod_lt _ (by positivity)
    have hoff := sourceValue_lt (len := len) fs hG s i
    cases output
    · simp only [Bool.false_eq_true, ite_false]
      rw [inC_eval neg rPlain (n * G) _ h0, offv_rPlain, Nat.mod_eq_of_lt hoff, ht]
      rfl
    · simp only [ite_true]
      rw [outC_eval neg rPlain (n * G) _ h0, offv_rPlain, Nat.mod_eq_of_lt hoff, ht]
      rfl
  rw [heq] at hspec
  exact hspec

/-- The actual source-controlled rotation pass. -/
def sourceRotate (ι : SourceReg nf → Fin T) (fs ft : Fin nf) (neg : Bool)
    (src : Fin T) (dst aux : Fin 2 → Fin T) (out ctr tmp cnt ctmp : Fin T) : Pr P T Q A U :=
  classMove (sourceCode ι fs ft (inC A neg rPlain)) (sourceCode ι fs ft (outC A neg rPlain))
    (codeSel (inC A neg rPlain)) (codeSel (outC A neg rPlain)) src dst aux out ctr tmp cnt ctmp
      (fun f => ι (.fld f)) (ι .st)

/-- A complete record-stream rotation with actual arbitrary-source callbacks.
All source descriptors, masks, field counters and scratch are restored. -/
theorem sourceRotate_exec (hι : Function.Injective ι) (fs ft : Fin nf)
    (hs : len fs = W) (ht : len ft = n * G) (hW : 0 < W) (hG : 0 < G)
    (horder : ft < fs) (s : Fin n → Fin W) (neg : Bool)
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
    (hI : SourceInv len ι G s S.R 0) :
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧
      m ≤ classMoveCost (nd := 2) (sourceCodeCost n W G) (sourceCodeCost n W G)
        (R * 2 ^ q) B len ∧
      Exec body (sourceRotate ι fs ft neg src dst aux out ctr tmp cnt ctmp) (mk v S) m
        (mk v' { S with
          R := Function.update S.R src
            (moveRecs (rotPerm (R := R) neg (sourceValue_high (len := len) (G := G) fs ft horder s) hq) l).flatten }) := by
  have hin := sourceCode_rot body hι fs ft hs ht hW hG s neg false
  have houtCode := sourceCode_rot body hι fs ft hs ht hW hG s neg true
  refine classMove_exec body hin houtCode hr hB
    (rotPerm (R := R) neg (sourceValue_high (len := len) (G := G) fs ft horder s) hq) ?_ ?_ hl hlB hcB hkk v S
      hsrc hctr hcnt htmp hctmp hout hdst haux hI
  · intro i hi
    simp only [Nat.zero_add, permFun_of_lt _ hi]
    change rotCls (wrapOut (len ft) neg
      (sourceValue len fs G s (rotIdx len ft neg (sourceValue len fs G s) i))
      (digit len ft (rotIdx len ft neg (sourceValue len fs G s) i))) = _
    rw [wrapOut_rotIdx neg (sourceValue_high (len := len) (G := G) fs ft horder s)
      (fun i => by rw [ht]; exact sourceValue_lt fs hG s i)]
    rfl
  · intro i hi i' hi' hc hii'
    simp only [Nat.zero_add, rotCls_inj] at hc
    rw [permFun_of_lt _ hi, permFun_of_lt _ hi']
    exact rotIdx_lt neg (sourceValue_high (len := len) (G := G) fs ft horder s)
      (fun i => by rw [ht]; exact sourceValue_lt fs hG s i) hii' hc

end IntegerMultBounds.MathlibTM2.Routing
