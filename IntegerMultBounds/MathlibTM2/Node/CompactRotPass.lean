module

public import IntegerMultBounds.MathlibTM2.Node.CompactRotCodes
public import IntegerMultBounds.MathlibTM2.Host.ClassMove
public import IntegerMultBounds.MathlibTM2.Layer.CompactRot

/-!
# The rotation passes of the compact gadget

A rotation instruction of `IntegerMultBounds.MathlibTM2.Layer.CompactGadget.prog` rotates one
digit of the record index (`y` or `b`) by an offset that reads only higher digits. On the record
stream it is a class move (`IntegerMultBounds.MathlibTM2.Host.classMove`) whose input and output
codes are the wrap classes of the rotation, computed by the code programs of
`IntegerMultBounds.MathlibTM2.Node.CompactRotCodes`.

`cxRot_exec`: the generic pass for a target digit `f`, an offset `off` above it and code
programs computing the wrap classes. `rotOp_eq` identifies the index map of a rotation
instruction with `rotIdx`.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Node

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Layer.CompactDigits
open IntegerMultBounds.MathlibTM2.Layer.CompactMasks IntegerMultBounds.MathlibTM2.Layer.CompactGadget

variable {p : Par} {T Q A : ℕ} {U : Type} {P : Type} {body : P → Pr P T Q A U}
variable {ι : CxReg → Fin T} {len : Fin 10 → ℕ}

/-- The class-move registers of the compact gadget. -/
lemma cx_moveRegs (hι : Function.Injective ι) :
    MoveRegs (CxIdx ι) (ι .src) (fun d => ι (.dst d)) (fun d => ι (.aux d)) (ι .out) (ι .ctr)
      (ι .tmp) (ι .cnt) (ι .ctmp) where
  regs := by simp [hι.eq_iff]
  dst_regs := fun d => by simp [hι.eq_iff]
  aux_regs := fun d => by simp [hι.eq_iff]
  dst_aux := fun d d' e => by simpa using hι e
  dst_inj := fun d d' e => by simpa using hι e
  aux_inj := fun d d' e => by simpa using hι e
  idx := by
    rintro k ⟨x, hx, rfl⟩
    cases x <;> simp_all [CxReg.isIdx, hι.eq_iff]
  idx_dst := by
    rintro d ⟨x, hx, e⟩
    have := hι e
    subst this
    exact hx
  idx_aux := by
    rintro d ⟨x, hx, e⟩
    have := hι e
    subst this
    exact hx

/-- **A rotation pass.** Records of `B ≥ 1` symbols, `M = R 2^q` of them with digit `f` below
bit `q`, rotated in digit `f` by `± off`, with code programs computing the input and output wrap classes. -/
theorem cxRot_exec (hι : Function.Injective ι) {f : Fin 10} (neg : Bool) {off : ℕ → ℕ}
    (hoff : OffHigh len f off) (hlt : ∀ i, off i < 2 ^ len f)
    {cpIn cpOut : Pr P T Q A U} {selIn selOut : ℕ → Fin 2} {cIn cOut : ℕ}
    (hin : CodeSpec body cpIn (fun g => ι (.fld g)) len (ι .st) (CxIdx ι) (CxInv p ι len) selIn
      (fun i => rotCls (wrapIn (len f) neg (off i) (digit len f i))) cIn)
    (hout : CodeSpec body cpOut (fun g => ι (.fld g)) len (ι .st) (CxIdx ι) (CxInv p ι len)
      selOut (fun i => rotCls (wrapOut (len f) neg (off i) (digit len f i))) cOut)
    {R B q : ℕ} (hq : fieldOff len f + len f ≤ q) (hB : 1 ≤ B)
    {l : List (List (Fin (A + 4)))} (hl : l.length = R * 2 ^ q) (hlB : ∀ r ∈ l, r.length = B)
    {cc kk : List (Fin (A + 4))} (hcB : cc.length = B) (hkk : kk.length = R * 2 ^ q)
    (v : HS T Q A U) (S : Stacks T A)
    (hsrc : S.R (ι .src) = l.flatten) (hctr : S.R (ι .ctr) = cc) (hcnt : S.R (ι .cnt) = kk)
    (htmp : S.R (ι .tmp) = []) (hctmp : S.R (ι .ctmp) = []) (houtR : S.R (ι .out) = [])
    (hdst : ∀ d, S.R (ι (.dst d)) = []) (haux : ∀ d, S.R (ι (.aux d)) = [])
    (hI : CxInv p ι len S.R 0) :
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧
      m ≤ classMoveCost (nd := 2) cIn cOut (R * 2 ^ q) B len ∧
      Exec body (classMove cpIn cpOut selIn selOut (ι .src) (fun d => ι (.dst d))
          (fun d => ι (.aux d)) (ι .out) (ι .ctr) (ι .tmp) (ι .cnt) (ι .ctmp)
          (fun g => ι (.fld g)) (ι .st)) (mk v S) m
        (mk v' { S with
          R := Function.update S.R (ι .src)
            (moveRecs (rotPerm (R := R) neg hoff hq) l).flatten })
      := by
  refine classMove_exec body hin hout (cx_moveRegs hι) hB _ ?_ ?_ hl hlB hcB hkk v S hsrc hctr hcnt
    htmp hctmp houtR hdst haux hI
  · intro i hi
    simp only [Nat.zero_add, permFun_of_lt _ hi]
    show rotCls (wrapOut (len f) neg (off (rotIdx len f neg off i))
      (digit len f (rotIdx len f neg off i))) = _
    rw [wrapOut_rotIdx neg hoff hlt]
  · intro i hi i' hi' hc hii'
    simp only [Nat.zero_add, rotCls_inj] at hc
    rw [permFun_of_lt _ hi, permFun_of_lt _ hi']
    exact rotIdx_lt neg hoff hlt hii' hc

/-! ### The code programs of each rotation -/

/-- A code program specified by one code function also computes any equal function. -/
lemma _root_.IntegerMultBounds.MathlibTM2.Host.CodeSpec.congr {nd : ℕ} {cp : Pr P T Q A U} {cf : Fin 10 → Fin T} {st : Fin T}
    {Y : Fin T → Prop} {Inv : (Fin T → List (Fin (A + 4))) → ℕ → Prop} {sel : ℕ → Fin nd}
    {code code' : ℕ → Fin nd} {c : ℕ} (h : CodeSpec body cp cf len st Y Inv sel code c)
    (he : ∀ i, code i = code' i) : CodeSpec body cp cf len st Y Inv sel code' c := by
  have : code = code' := funext he
  subst this
  exact h

/-- The gadget fields in increasing order of significance where the rotations need it. -/
structure _root_.IntegerMultBounds.MathlibTM2.Layer.CompactGadget.Fields.Order
    (F : Fields 10) : Prop where
  b_y : F.b < F.y
  b_x : F.b < F.x
  b_u : F.b < F.u
  y_t : F.y < F.t
  y_u : F.y < F.u

variable {F : Fields 10}

lemma digit_lt_len (g : Fin 10) (i : ℕ) : digit len g i < 2 ^ len g :=
  Nat.mod_lt _ (by positivity)

/-- The offset of a rotation as a function of the record index. -/
def offIdx (p : Par) (len : Fin 10 → ℕ) (F : Fields 10) (o : Off) (i : ℕ) : ℕ :=
  o.eval p (view len F i)

lemma offIdx_A_high (hO : F.Order) : OffHigh len F.y (offIdx p len F .A) := by
  refine offHigh_of_digits {F.t, F.u} (by simp [hO.y_t, hO.y_u]) fun i j h => ?_
  have ht := h F.t (by simp)
  have hu := h F.u (by simp)
  simp only [offIdx, Off.eval, view, zc, ht, hu]

lemma offIdx_Z_high (hO : F.Order) : OffHigh len F.y (offIdx p len F .Z) := by
  refine offHigh_of_digits {F.u} (by simp [hO.y_u]) fun i j h => ?_
  have hu := h F.u (by simp)
  simp only [offIdx, Off.eval, view, zc, hu]

lemma offIdx_Y_high (hO : F.Order) : OffHigh len F.b (offIdx p len F .Y) := by
  refine offHigh_of_digits {F.y} (by simp [hO.b_y]) fun i j h => ?_
  have hy := h F.y (by simp)
  simp only [offIdx, Off.eval, view, hy]

lemma offIdx_X_high (hO : F.Order) : OffHigh len F.b (offIdx p len F .X) := by
  refine offHigh_of_digits {F.x} (by simp [hO.b_x]) fun i j h => ?_
  have hx := h F.x (by simp)
  simp only [offIdx, Off.eval, view, hx]

lemma offIdx_YZ_high (hO : F.Order) : OffHigh len F.b (offIdx p len F .YZ) := by
  refine offHigh_of_digits {F.y, F.u} (by simp [hO.b_y, hO.b_u]) fun i j h => ?_
  have hy := h F.y (by simp)
  have hu := h F.u (by simp)
  simp only [offIdx, Off.eval, view, zc, hy, hu]

/-- The code of the rotation of `y` by `± Off.A`. -/
theorem codeA_rot (hι : Function.Injective ι) (hF : F.Valid p len) (hK : 0 < p.K)
    (hG : 0 < p.G) (hGK : p.G < p.K) (neg out : Bool) :
    CodeSpec body (codeA (ι := ι) F (if out then outC A neg rLatch else inC A neg rLatch))
      (fun g => ι (.fld g)) len (ι .st) (CxIdx ι) (CxInv p ι len)
      (codeSel (if out then outC A neg rLatch else inC A neg rLatch))
      (fun i => rotCls ((if out then wrapOut else wrapIn) (len F.y) neg (offIdx p len F .A i)
        (digit len F.y i))) (20 * p.wc + 34 * p.wy + 40) := by
  refine (codeA_spec hι hF hK hG hGK _).congr fun i => ?_
  have hW : ∀ j < p.n * p.G, posA p j < p.wy := fun j hj => posA_lt hG hGK hj
  have hoff := offv_rLatch hK hG hGK hW (view len F i)
  have h0 : digit len F.y i < 2 ^ p.wy := by rw [← hF.ly]; exact digit_lt_len _ _
  simp only [view] at hoff
  cases out
  · simp only [Bool.false_eq_true, ite_false]
    rw [inC_eval neg rLatch p.wy _ h0, selV, hoff, hF.ly]
    rfl
  · simp only [ite_true]
    rw [outC_eval neg rLatch p.wy _ h0, selV, hoff, hF.ly]
    rfl

lemma placeVal_posS_lt (hK : 0 < p.K) (b : ℕ → Bool) : placeVal p.n (posS p) b < 2 ^ p.wy :=
  lt_of_lt_of_le (placeVal_lt (posS_mono hK) b p.n)
    (Nat.pow_le_pow_right (by norm_num) (by unfold posS Par.wy; omega))

lemma placeVal_posC_lt (hG : 0 < p.G) (b : ℕ → Bool) : placeVal p.n (posC p) b < 2 ^ p.wc :=
  lt_of_lt_of_le (placeVal_lt (posC_mono hG) b p.n) (by unfold posC Par.wc; rfl)

/-- The code of the rotation of `y` by `± Off.Z`. -/
theorem codeZ_rot (hι : Function.Injective ι) (hF : F.Valid p len) (hK : 0 < p.K)
    (hG : 0 < p.G) (neg out : Bool) :
    CodeSpec body (codeZ (ι := ι) F (if out then outC A neg rPlain else inC A neg rPlain))
      (fun g => ι (.fld g)) len (ι .st) (CxIdx ι) (CxInv p ι len)
      (codeSel (if out then outC A neg rPlain else inC A neg rPlain))
      (fun i => rotCls ((if out then wrapOut else wrapIn) (len F.y) neg (offIdx p len F .Z i)
        (digit len F.y i))) (10 * p.wc + 16 * p.wy + 24) := by
  refine (codeZ_spec hι hF hK hG _).congr fun i => ?_
  have h0 : digit len F.y i < 2 ^ p.wy := by rw [← hF.ly]; exact digit_lt_len _ _
  have hlt : Off.eval p .Z (view len F i) < 2 ^ p.wy := by
    rw [offZ_eq hG]; exact placeVal_posS_lt hK _
  cases out
  · simp only [Bool.false_eq_true, ite_false]
    rw [inC_eval neg rPlain p.wy _ h0, offv_rPlain, Nat.mod_eq_of_lt hlt, hF.ly]
    rfl
  · simp only [ite_true]
    rw [outC_eval neg rPlain p.wy _ h0, offv_rPlain, Nat.mod_eq_of_lt hlt, hF.ly]
    rfl

/-- The code of the rotation of `b` by `± Off.Y`. -/
theorem codeY_rot (hι : Function.Injective ι) (hF : F.Valid p len) (hK : 0 < p.K)
    (hG : 0 < p.G) (neg out : Bool) :
    CodeSpec body (codeY (ι := ι) F (if out then outC A neg rPlain else inC A neg rPlain))
      (fun g => ι (.fld g)) len (ι .st) (CxIdx ι) (CxInv p ι len)
      (codeSel (if out then outC A neg rPlain else inC A neg rPlain))
      (fun i => rotCls ((if out then wrapOut else wrapIn) (len F.b) neg (offIdx p len F .Y i)
        (digit len F.b i))) (16 * p.wc + 10 * p.wy + 24) := by
  refine (codeY_spec hι hF hK hG _).congr fun i => ?_
  have h0 : digit len F.b i < 2 ^ p.wc := by rw [← hF.lb]; exact digit_lt_len _ _
  have hlt : Off.eval p .Y (view len F i) < 2 ^ p.wc := by
    rw [offY_eq hK]; exact placeVal_posC_lt hG _
  cases out
  · simp only [Bool.false_eq_true, ite_false]
    rw [inC_eval neg rPlain p.wc _ h0, offv_rPlain, Nat.mod_eq_of_lt hlt, hF.lb]
    rfl
  · simp only [ite_true]
    rw [outC_eval neg rPlain p.wc _ h0, offv_rPlain, Nat.mod_eq_of_lt hlt, hF.lb]
    rfl

/-- The code of the rotation of `b` by `± Off.X`. -/
theorem codeX_rot (hι : Function.Injective ι) (hF : F.Valid p len) (hK : 0 < p.K)
    (hG : 0 < p.G) (neg out : Bool) :
    CodeSpec body (codeX (ι := ι) F (if out then outC A neg rPlain else inC A neg rPlain))
      (fun g => ι (.fld g)) len (ι .st) (CxIdx ι) (CxInv p ι len)
      (codeSel (if out then outC A neg rPlain else inC A neg rPlain))
      (fun i => rotCls ((if out then wrapOut else wrapIn) (len F.b) neg (offIdx p len F .X i)
        (digit len F.b i))) (16 * p.wc + 10 * p.wy + 24) := by
  refine (codeX_spec hι hF hK hG _).congr fun i => ?_
  have h0 : digit len F.b i < 2 ^ p.wc := by rw [← hF.lb]; exact digit_lt_len _ _
  have hlt : Off.eval p .X (view len F i) < 2 ^ p.wc := by
    rw [offX_eq hK]; exact placeVal_posC_lt hG _
  cases out
  · simp only [Bool.false_eq_true, ite_false]
    rw [inC_eval neg rPlain p.wc _ h0, offv_rPlain, Nat.mod_eq_of_lt hlt, hF.lb]
    rfl
  · simp only [ite_true]
    rw [outC_eval neg rPlain p.wc _ h0, offv_rPlain, Nat.mod_eq_of_lt hlt, hF.lb]
    rfl

/-- The code of the rotation of `b` by `± Off.YZ`. -/
theorem codeYZ_rot (hι : Function.Injective ι) (hF : F.Valid p len) (hK : 0 < p.K)
    (hG : 0 < p.G) (neg out : Bool) :
    CodeSpec body (codeYZ (ι := ι) F (if out then outC A neg rXor else inC A neg rXor))
      (fun g => ι (.fld g)) len (ι .st) (CxIdx ι) (CxInv p ι len)
      (codeSel (if out then outC A neg rXor else inC A neg rXor))
      (fun i => rotCls ((if out then wrapOut else wrapIn) (len F.b) neg (offIdx p len F .YZ i)
        (digit len F.b i))) (16 * p.wc + 10 * p.wy + 24) := by
  refine (codeYZ_spec hι hF hK hG _).congr fun i => ?_
  have h0 : digit len F.b i < 2 ^ p.wc := by rw [← hF.lb]; exact digit_lt_len _ _
  have hu : (view len F i).u < 2 ^ p.wc := by
    show digit len F.u i < _; rw [← hF.lu]; exact digit_lt_len _ _
  have hoff := offv_rXor_YZ hK hG (view len F i) hu
  simp only [view] at hoff
  cases out
  · simp only [Bool.false_eq_true, ite_false]
    rw [inC_eval neg rXor p.wc _ h0, hoff, hF.lb]
    rfl
  · simp only [ite_true]
    rw [outC_eval neg rXor p.wc _ h0, hoff, hF.lb]
    rfl

/-! ### Offset bounds -/

lemma offIdx_A_lt (hF : F.Valid p len) (hK : 0 < p.K) (hG : 0 < p.G) (hGK : p.G < p.K) (i : ℕ) :
    offIdx p len F .A i < 2 ^ len F.y := by
  have hoff := offv_rLatch hK hG hGK (fun j hj => posA_lt hG hGK hj) (view len F i)
  rw [offIdx, ← hoff, hF.ly]
  exact offv_lt _ _ _ _

lemma offIdx_Z_lt (hF : F.Valid p len) (hK : 0 < p.K) (hG : 0 < p.G) (i : ℕ) :
    offIdx p len F .Z i < 2 ^ len F.y := by
  rw [offIdx, offZ_eq hG, hF.ly]; exact placeVal_posS_lt hK _

lemma offIdx_Y_lt (hF : F.Valid p len) (hK : 0 < p.K) (hG : 0 < p.G) (i : ℕ) :
    offIdx p len F .Y i < 2 ^ len F.b := by
  rw [offIdx, offY_eq hK, hF.lb]; exact placeVal_posC_lt hG _

lemma offIdx_X_lt (hF : F.Valid p len) (hK : 0 < p.K) (hG : 0 < p.G) (i : ℕ) :
    offIdx p len F .X i < 2 ^ len F.b := by
  rw [offIdx, offX_eq hK, hF.lb]; exact placeVal_posC_lt hG _

lemma offIdx_YZ_lt (hF : F.Valid p len) (hK : 0 < p.K) (hG : 0 < p.G) (i : ℕ) :
    offIdx p len F .YZ i < 2 ^ len F.b := by
  have hu : (view len F i).u < 2 ^ p.wc := by
    show digit len F.u i < _; rw [← hF.lu]; exact digit_lt_len _ _
  rw [offIdx, ← offv_rXor_YZ hK hG (view len F i) hu, hF.lb]
  exact offv_lt _ _ _ _

/-- The index map of a rotation of `y` is `rotIdx`. -/
lemma rotY_idx (hF : F.Valid p len) (neg : Bool) (o : Off) (i : ℕ) :
    (Op.rotY neg o).idx p len F i = rotIdx len F.y neg (offIdx p len F o) i := by
  simp only [Op.idx, rotIdx, offIdx, hF.ly]

/-- The index map of a rotation of `b` is `rotIdx`. -/
lemma rotB_idx (hF : F.Valid p len) (neg : Bool) (o : Off) (i : ℕ) :
    (Op.rotB neg o).idx p len F i = rotIdx len F.b neg (offIdx p len F o) i := by
  simp only [Op.idx, rotIdx, offIdx, hF.lb]

end IntegerMultBounds.MathlibTM2.Node
