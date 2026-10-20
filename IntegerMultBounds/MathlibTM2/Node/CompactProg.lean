module

public import IntegerMultBounds.MathlibTM2.Node.CompactRotPass
public import IntegerMultBounds.MathlibTM2.Node.CompactSwapPass

/-!
# Running the gadget program pass by pass

`listPerm π xs` composes the permutations `π x` of a list, first to last; for the instructions of
the gadget it is the permutation of the index map `runIdx` (`runPerm_val`). `seqList_moveRecs`:
running a list of passes, each of which moves the records of `src` by its permutation and leaves
every other register as it was, moves the records by the composite.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Node

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Layer.CompactDigits
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget

/-- The composite of the permutations `π x` of a list, first to last. -/
def listPerm {X : Type*} {M : ℕ} (π : X → Equiv.Perm (Fin M)) : List X → Equiv.Perm (Fin M)
  | [] => Equiv.refl _
  | x :: xs => (π x).trans (listPerm π xs)

lemma moveRecs_refl {α : Type*} {M : ℕ} (l : List (List α)) (hl : l.length = M) :
    moveRecs (Equiv.refl (Fin M)) l = l := by
  subst hl
  apply List.ext_getElem (by simp [length_moveRecs])
  intro j h1 h2
  simp [moveRecs]

/-! ### The index map of a list of instructions -/

section RunPerm

variable {p : Par} {nf : ℕ} {len : Fin nf → ℕ} {F : Fields nf} (hF : F.Valid p len) {q R : ℕ}
  (hq : ∀ g, touched F g → fieldOff len g + len g ≤ q)

/-- The permutation of a well-formed instruction. -/
def wfPerm (o : {o : Op // o.WF}) : Equiv.Perm (Fin (R * 2 ^ q)) := opPerm hF hq o.2

lemma wfPerm_val (o : {o : Op // o.WF}) (i : Fin (R * 2 ^ q)) :
    (wfPerm hF hq o i : ℕ) = o.1.idx p len F i := rfl

/-- The composite permutation is the index map of the instruction list. -/
theorem runPerm_val (os : List {o : Op // o.WF}) (i : Fin (R * 2 ^ q)) :
    (listPerm (wfPerm hF hq) os i : ℕ) = runIdx p len F (os.map Subtype.val) i := by
  induction os generalizing i with
  | nil => rfl
  | cons o os ih =>
    show (listPerm (wfPerm hF hq) os (wfPerm hF hq o i) : ℕ) = _
    rw [ih, wfPerm_val]
    rfl

end RunPerm

/-! ### Running a list of passes -/

section Passes

variable {T Q A : ℕ} {U : Type} {P : Type} (body : P → Pr P T Q A U)

/-- **A list of passes.** If every pass `prog x` moves the records of `src` by `π x`, in at most
`cost x` steps, from any stream of `M` records satisfying `Rec` beside the fixed registers of
`S₀`, then the passes in order move them by the composite. -/
theorem seqList_moveRecs {X : Type*} (prog : X → Pr P T Q A U) {M : ℕ}
    (π : X → Equiv.Perm (Fin M)) (cost : X → ℝ) (src : Fin T) (S₀ : Stacks T A)
    (Rec : List (Fin (A + 4)) → Prop) :
    ∀ (xs : List X), (∀ x ∈ xs, ∀ l : List (List (Fin (A + 4))), l.length = M →
      (∀ r ∈ l, Rec r) → ∀ v : HS T Q A U, ∃ (v' : HS T Q A U) (m : ℕ),
        v'.user = v.user ∧ (m : ℝ) ≤ cost x ∧
        Exec body (prog x) (mk v { S₀ with R := Function.update S₀.R src l.flatten }) m
          (mk v' { S₀ with R := Function.update S₀.R src (moveRecs (π x) l).flatten })) →
      ∀ (l : List (List (Fin (A + 4)))), l.length = M → (∀ r ∈ l, Rec r) →
      ∀ v : HS T Q A U, ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧
        (m : ℝ) ≤ (xs.map cost).sum + 1 ∧
        Exec body (Prog.seqList (xs.map prog))
          (mk v { S₀ with R := Function.update S₀.R src l.flatten }) m
          (mk v' { S₀ with R := Function.update S₀.R src (moveRecs (listPerm π xs) l).flatten })
  | [], _, l, hl, _, v => by
    refine ⟨v, 1, rfl, by simp, ?_⟩
    rw [listPerm, moveRecs_refl l hl]
    simpa [Prog.seqList] using Exec.act (body := body) .done
      (mk v { S₀ with R := Function.update S₀.R src l.flatten })
  | x :: xs, h, l, hl, hlB, v => by
    obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := h x List.mem_cons_self l hl hlB v
    have hl₁ : (moveRecs (π x) l).length = M := length_moveRecs _ _
    have hlB₁ : ∀ r ∈ moveRecs (π x) l, Rec r := fun r hr => by
      simp only [moveRecs, List.mem_ofFn] at hr
      obtain ⟨j, rfl⟩ := hr
      rw [List.getD_eq_getElem _ _ (by rw [hl]; exact (π x).symm j |>.isLt)]
      exact hlB _ (List.getElem_mem _)
    obtain ⟨v₂, m₂, hu₂, hm₂, he₂⟩ := seqList_moveRecs prog π cost src S₀ Rec xs
      (fun y hy => h y (List.mem_cons_of_mem _ hy)) _ hl₁ hlB₁ v₁
    refine ⟨v₂, m₁ + m₂, by rw [hu₂, hu₁], ?_, ?_⟩
    · simp only [List.map_cons, List.sum_cons]; push_cast; linarith
    · rw [listPerm, moveRecs_trans _ _ l hl]
      exact Exec.seq he₁ he₂

end Passes

/-! ### The rotation passes -/

section Rot

variable {p : Par} {T Q A : ℕ} {U : Type} {P : Type} {body : P → Pr P T Q A U}
  {ι : CxReg → Fin T} {len : Fin 10 → ℕ} (F : Fields 10)

/-- The digit a rotation by offset `o` changes: `y` for `A` and `Z`, `b` otherwise. -/
def rotTgt : Off → Fin 10
  | .A | .Z => F.y
  | _ => F.b

/-- The code program of a rotation by `± o`: the input (`out = false`) or output wrap class. -/
def rotCode (o : Off) (neg out : Bool) : Pr P T Q A U :=
  match o with
  | .A => codeA (ι := ι) F (if out then outC A neg rLatch else inC A neg rLatch)
  | .Z => codeZ (ι := ι) F (if out then outC A neg rPlain else inC A neg rPlain)
  | .Y => codeY (ι := ι) F (if out then outC A neg rPlain else inC A neg rPlain)
  | .X => codeX (ι := ι) F (if out then outC A neg rPlain else inC A neg rPlain)
  | .YZ => codeYZ (ι := ι) F (if out then outC A neg rXor else inC A neg rXor)

variable (A) in
/-- The selector of `rotCode`. -/
def rotSel (o : Off) (neg out : Bool) : ℕ → Fin 2 :=
  match o with
  | .A => codeSel (if out then outC A neg rLatch else inC A neg rLatch)
  | .YZ => codeSel (if out then outC A neg rXor else inC A neg rXor)
  | _ => codeSel (if out then outC A neg rPlain else inC A neg rPlain)

variable (p) in
/-- The step bound of every rotation code program. -/
def cRot : ℕ := 20 * p.wc + 34 * p.wy + 40

variable {F}

theorem rotCode_spec (hι : Function.Injective ι) (hF : F.Valid p len) (hK : 0 < p.K)
    (hG : 0 < p.G) (hGK : p.G < p.K) (o : Off) (neg out : Bool) :
    CodeSpec body (rotCode (ι := ι) F o neg out) (fun g => ι (.fld g)) len (ι .st) (CxIdx ι)
      (CxInv p ι len) (rotSel A o neg out)
      (fun i => rotCls ((if out then wrapOut else wrapIn) (len (rotTgt F o)) neg
        (offIdx p len F o i) (digit len (rotTgt F o) i))) (cRot p) := by
  cases o
  · exact (codeA_rot hι hF hK hG hGK neg out).mono le_rfl
  · exact (codeZ_rot hι hF hK hG neg out).mono (by unfold cRot; omega)
  · exact (codeY_rot hι hF hK hG neg out).mono (by unfold cRot; omega)
  · exact (codeYZ_rot hι hF hK hG neg out).mono (by unfold cRot; omega)
  · exact (codeX_rot hι hF hK hG neg out).mono (by unfold cRot; omega)

lemma rotTgt_high (hO : F.Order) (o : Off) : OffHigh len (rotTgt F o) (offIdx p len F o) := by
  cases o
  · exact offIdx_A_high hO
  · exact offIdx_Z_high hO
  · exact offIdx_Y_high hO
  · exact offIdx_YZ_high hO
  · exact offIdx_X_high hO

lemma rotTgt_lt (hF : F.Valid p len) (hK : 0 < p.K) (hG : 0 < p.G) (hGK : p.G < p.K) (o : Off)
    (i : ℕ) : offIdx p len F o i < 2 ^ len (rotTgt F o) := by
  cases o
  · exact offIdx_A_lt hF hK hG hGK i
  · exact offIdx_Z_lt hF hK hG i
  · exact offIdx_Y_lt hF hK hG i
  · exact offIdx_YZ_lt hF hK hG i
  · exact offIdx_X_lt hF hK hG i

variable (F) in
/-- The pass of a rotation by `± o`. -/
def cxRotPass (o : Off) (neg : Bool) : Pr P T Q A U :=
  classMove (rotCode (ι := ι) F o neg false) (rotCode (ι := ι) F o neg true) (rotSel A o neg false)
    (rotSel A o neg true) (ι .src) (fun d => ι (.dst d)) (fun d => ι (.aux d)) (ι .out) (ι .ctr)
    (ι .tmp) (ι .cnt) (ι .ctmp) (fun g => ι (.fld g)) (ι .st)

variable (body) in
/-- **A rotation pass** moves the records by the rotation of the target digit by `± o`. -/
theorem cxRotPass_exec (hι : Function.Injective ι) (hF : F.Valid p len) (hO : F.Order)
    (hK : 0 < p.K) (hG : 0 < p.G) (hGK : p.G < p.K) (o : Off) (neg : Bool) {R B q : ℕ}
    (hq : fieldOff len (rotTgt F o) + len (rotTgt F o) ≤ q) (hB : 1 ≤ B)
    {l : List (List (Fin (A + 4)))} (hl : l.length = R * 2 ^ q) (hlB : ∀ r ∈ l, r.length = B)
    {cc kk : List (Fin (A + 4))} (hcB : cc.length = B) (hkk : kk.length = R * 2 ^ q)
    (v : HS T Q A U) (S : Stacks T A)
    (hsrc : S.R (ι .src) = l.flatten) (hctr : S.R (ι .ctr) = cc) (hcnt : S.R (ι .cnt) = kk)
    (htmp : S.R (ι .tmp) = []) (hctmp : S.R (ι .ctmp) = []) (houtR : S.R (ι .out) = [])
    (hdst : ∀ d, S.R (ι (.dst d)) = []) (haux : ∀ d, S.R (ι (.aux d)) = [])
    (hI : CxInv p ι len S.R 0) :
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧
      m ≤ classMoveCost (nd := 2) (cRot p) (cRot p) (R * 2 ^ q) B len ∧
      Exec body (cxRotPass (ι := ι) F o neg) (mk v S) m
        (mk v' { S with
          R := Function.update S.R (ι .src)
            (moveRecs (rotPerm (R := R) neg (rotTgt_high (p := p) hO o) hq) l).flatten }) :=
  cxRot_exec hι neg (rotTgt_high (p := p) hO o) (rotTgt_lt hF hK hG hGK o)
    (rotCode_spec hι hF hK hG hGK o neg false) (rotCode_spec hι hF hK hG hGK o neg true) hq hB
    hl hlB hcB hkk v S hsrc hctr hcnt htmp hctmp houtR hdst haux hI

end Rot

/-! ### The swap passes and the instruction passes -/

section Ops

open IntegerMultBounds.Networks.Shared50ModularControl (prime)

variable {p : Par} {T Q K : ℕ} {U : Type} {P : Type} {body : P → Pr P T Q (prime + K) U}
  {ι : CxReg → Fin T} {len : Fin 10 → ℕ} (F : Fields 10)

/-- The header registers of an interchange bank. -/
def cxHd : Fin 5 → Fin 6 := Fin.castSucc

/-- The payload register of an interchange bank. -/
def cxPay : Fin 6 := Fin.last 5

lemma cxHd_inj : Function.Injective cxHd := Fin.castSucc_injective 5

/-- The digit exchanged with `b` by bank `c`: `t` for `swapT`, `u` for `swapU`. -/
def swapFld (c : Fin 2) : Fin 10 := if c = 0 then F.t else F.u

/-- The interchange banks: injective, outside the compact registers. -/
structure Banks (ι : CxReg → Fin T) (bank : Fin 2 → Fin (swapT 6) → Fin T) : Prop where
  inj : ∀ c, Function.Injective (bank c)
  ne : ∀ c j x, bank c j ≠ ι x

variable {bank : Fin 2 → Fin (swapT 6) → Fin T}

variable (ι) in
/-- The pass of one instruction. -/
noncomputable def opPass (hb : Banks ι bank) (hQ : swapStates cxHd cxPay cxHd_inj ≤ Q) (hT : swapT 6 ≤ T) :
    Op → Pr P T Q (prime + K) U
  | .rotY neg o => cxRotPass (ι := ι) F o neg
  | .rotB neg o => cxRotPass (ι := ι) F o neg
  | .swapT => swapPass cxHd cxPay cxHd_inj hQ (bank 0) (hb.inj 0) hT (ι .src) (ι .tmp)
  | .swapU => swapPass cxHd cxPay cxHd_inj hQ (bank 1) (hb.inj 1) hT (ι .src) (ι .tmp)

/-- The fixed registers of the instruction passes: empty stream scratch, the record counters,
the index state at `0`, and the interchange banks holding their headers `hs c`. -/
structure PassState (ι : CxReg → Fin T) (bank : Fin 2 → Fin (swapT 6) → Fin T) (p : Par)
    (len : Fin 10 → ℕ) (B M : ℕ) (hs : Fin 2 → Fin 5 → List Bool) (S : Stacks T (prime + K)) :
    Prop where
  L : ∀ y, S.L y = []
  ctr : (S.R (ι .ctr)).length = B
  cnt : (S.R (ι .cnt)).length = M
  tmp : S.R (ι .tmp) = []
  ctmp : S.R (ι .ctmp) = []
  out : S.R (ι .out) = []
  dst : ∀ d, S.R (ι (.dst d)) = []
  aux : ∀ d, S.R (ι (.aux d)) = []
  inv : CxInv p ι len S.R 0
  pay : ∀ c, S.R (bank c (reg cxPay)) = []
  priv : ∀ c (j : Fin (swapT 6)), 6 ≤ j.val → S.R (bank c j) = []
  hdr : ∀ c k, S.R (bank c (reg (cxHd k))) = separator :: (hs c k).map bitSymbol

/-- The pass state does not read the stream register. -/
lemma PassState.update (hι : Function.Injective ι) (hb : Banks ι bank) {B M : ℕ}
    {hs : Fin 2 → Fin 5 → List Bool} {S : Stacks T (prime + K)}
    (h : PassState ι bank p len B M hs S) (w : List (Fin (prime + K + 4))) :
    PassState ι bank p len B M hs { S with R := Function.update S.R (ι .src) w } := by
  have e : ∀ x : CxReg, x ≠ .src → Function.update S.R (ι .src) w (ι x) = S.R (ι x) :=
    fun x hx => Function.update_of_ne (hι.ne hx) _ _
  have eb : ∀ c j, Function.update S.R (ι .src) w (bank c j) = S.R (bank c j) :=
    fun c j => Function.update_of_ne (hb.ne c j .src) _ _
  refine ⟨h.L, ?_, ?_, ?_, ?_, ?_, fun d => ?_, fun d => ?_, ?_, fun c => ?_, fun c j hj => ?_,
    fun c k => ?_⟩
  all_goals first
    | (show Function.update S.R (ι .src) w (ι _) = _ ; rw [e _ (by simp)])
    | (show (Function.update S.R (ι .src) w (ι _)).length = _ ; rw [e _ (by simp)])
    | (show Function.update S.R (ι .src) w (bank _ _) = _ ; rw [eb])
    | skip
  · exact h.ctr
  · exact h.cnt
  · exact h.tmp
  · exact h.ctmp
  · exact h.out
  · exact h.dst d
  · exact h.aux d
  · exact cxInv_frame h.inv fun k ⟨x, hx, hk⟩ => by
      subst hk; exact e x (by cases x <;> simp_all [CxReg.isIdx])
  · exact h.pay c
  · exact h.priv c j hj
  · exact h.hdr c k

variable (p len) in
/-- The step bound of the pass of an instruction. -/
noncomputable def opCost (T : ℕ) (Rr q B : ℕ) (bankLen : Fin 2 → ℕ) : Op → ℝ
  | .rotY _ _ | .rotB _ _ => classMoveCost (nd := 2) (cRot p) (cRot p) (Rr * 2 ^ q) B len
  | .swapT => 3 * swapConst * (T + 12 * swapT 6 + 5 : ℕ) * (Rr * 2 ^ q * B : ℕ) *
      ((max 1 p.wc : ℕ) : ℝ) ^ Parameters.tau +
      (6 * bankLen 0 + 34 * (Rr * 2 ^ q * B) + 2 * T + 6 * swapT 6 + 23 : ℕ)
  | .swapU => 3 * swapConst * (T + 12 * swapT 6 + 5 : ℕ) * (Rr * 2 ^ q * B : ℕ) *
      ((max 1 p.wc : ℕ) : ℝ) ^ Parameters.tau +
      (6 * bankLen 1 + 34 * (Rr * 2 ^ q * B) + 2 * T + 6 * swapT 6 + 23 : ℕ)

variable (body) in
/-- **The pass of a well-formed instruction** moves the records by its index map. -/
theorem opPass_exec (hι : Function.Injective ι) (hF : F.Valid p len) (hO : F.Order)
    (hK : 0 < p.K) (hG : 0 < p.G) (hGK : p.G < p.K) (hb : Banks ι bank)
    (hQ : swapStates cxHd cxPay cxHd_inj ≤ Q) (hT : swapT 6 ≤ T) {Rr q B : ℕ} (hRr : 0 < Rr)
    (hq : ∀ g, touched F g → fieldOff len g + len g ≤ q) (hB : 1 ≤ B)
    (hs : Fin 2 → Fin 5 → List Bool)
    (hv : ∀ c k, Counter.value (hs c k) = swapValues
      (swapDimsIdx (len := len) F.b (swapFld F c) p.wc Rr q B).1
      (swapDimsIdx (len := len) F.b (swapFld F c) p.wc Rr q B).2.1
      (swapDimsIdx (len := len) F.b (swapFld F c) p.wc Rr q B).2.2 p.wc p.wc k)
    (hc : ∀ c k, GrowingCounterData.Canonical (hs c k))
    (S₀ : Stacks T (prime + K)) (hS : PassState ι bank p len B (Rr * 2 ^ q) hs S₀)
    (o : {o : Op // o.WF}) (l : List (List (Fin (prime + K + 4))))
    (hl : l.length = Rr * 2 ^ q) (hlB : ∀ r ∈ l, r.length = B ∧ ∀ s ∈ r, s.val < 8)
    (v : HS T Q (prime + K) U) :
    ∃ (v' : HS T Q (prime + K) U) (m : ℕ), v'.user = v.user ∧
      (m : ℝ) ≤ opCost p len T Rr q B (fun c => ∑ j, (S₀.R (bank c j)).length) o.1 ∧
      Exec body (opPass (ι := ι) F hb hQ hT o.1)
        (mk v { S₀ with R := Function.update S₀.R (ι .src) l.flatten }) m
        (mk v' { S₀ with
          R := Function.update S₀.R (ι .src) (moveRecs (wfPerm (R := Rr) hF hq o) l).flatten }) := by
  have hS' := hS.update hι hb l.flatten
  have hsrc : Function.update S₀.R (ι .src) l.flatten (ι .src) = l.flatten := by simp
  have hlen : ∀ r ∈ l, r.length = B := fun r hr => (hlB r hr).1
  obtain ⟨o, ho⟩ := o
  have hd := hF.distinct
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hd
  cases o with
  | rotY neg off =>
    have hy : rotTgt F off = F.y := by rcases ho with rfl | rfl <;> rfl
    have hq' : fieldOff len (rotTgt F off) + len (rotTgt F off) ≤ q := by
      rw [hy]; exact hq _ (Or.inr (Or.inr (Or.inr rfl)))
    obtain ⟨v', m, hu, hm, he⟩ := cxRotPass_exec body hι hF hO hK hG hGK off neg hq' hB hl hlen
      hS'.ctr hS'.cnt v _ hsrc rfl rfl hS'.tmp hS'.ctmp hS'.out hS'.dst hS'.aux hS'.inv
    refine ⟨v', m, hu, by simp only [opCost]; exact_mod_cast hm, ?_⟩
    have hπ : rotPerm (R := Rr) neg (rotTgt_high (p := p) hO off) hq' = wfPerm (R := Rr) hF hq ⟨_, ho⟩ :=
      Equiv.ext fun i => Fin.ext (by
        rw [wfPerm_val, rotY_idx hF, ← hy]; rfl)
    rw [hπ] at he
    exact Exec.cast he rfl (by simp)
  | rotB neg off =>
    have hy : rotTgt F off = F.b := by rcases ho with rfl | rfl | rfl <;> rfl
    have hq' : fieldOff len (rotTgt F off) + len (rotTgt F off) ≤ q := by
      rw [hy]; exact hq _ (Or.inl rfl)
    obtain ⟨v', m, hu, hm, he⟩ := cxRotPass_exec body hι hF hO hK hG hGK off neg hq' hB hl hlen
      hS'.ctr hS'.cnt v _ hsrc rfl rfl hS'.tmp hS'.ctmp hS'.out hS'.dst hS'.aux hS'.inv
    refine ⟨v', m, hu, by simp only [opCost]; exact_mod_cast hm, ?_⟩
    have hπ : rotPerm (R := Rr) neg (rotTgt_high (p := p) hO off) hq' = wfPerm (R := Rr) hF hq ⟨_, ho⟩ :=
      Equiv.ext fun i => Fin.ext (by
        rw [wfPerm_val, rotB_idx hF, ← hy]; rfl)
    rw [hπ] at he
    exact Exec.cast he rfl (by simp)
  | swapT =>
    have h12 : F.b < swapFld F 0 := hO.b_y.trans hO.y_t
    obtain ⟨v', m, hu, hm, he⟩ := cxSwap_exec body cxHd cxPay cxHd_inj hQ (bank 0) (hb.inj 0) hT
      (ι .src) (ι .tmp) (hι.ne (by decide)) (fun j => hb.ne 0 j _) (fun j => hb.ne 0 j _) h12
      hF.lb hF.lt hRr (by rw [← hF.lt]; exact hq _ (Or.inr (Or.inl rfl)))
      (wfPerm (R := Rr) hF hq ⟨.swapT, ho⟩) (fun r => rfl) hB l hl hlen (fun x hx => (hlB x hx).2) (hs 0)
      (hv 0) (hc 0) v _ hS'.L hsrc hS'.tmp (hS'.pay 0) (hS'.priv 0) (hS'.hdr 0)
      (fun i hi hk => absurd (Fin.eq_last_of_not_lt (fun h => hk ⟨i, h⟩ (Fin.ext rfl))) hi)
    refine ⟨v', m, hu, ?_, Exec.cast he rfl (by simp)⟩
    simpa [opCost, Function.update_of_ne (hb.ne 0 _ .src)] using hm
  | swapU =>
    have h12 : F.b < swapFld F 1 := hO.b_u
    obtain ⟨v', m, hu, hm, he⟩ := cxSwap_exec body cxHd cxPay cxHd_inj hQ (bank 1) (hb.inj 1) hT
      (ι .src) (ι .tmp) (hι.ne (by decide)) (fun j => hb.ne 1 j _) (fun j => hb.ne 1 j _) h12
      hF.lb hF.lu hRr (by rw [← hF.lu]; exact hq _ (Or.inr (Or.inr (Or.inl rfl))))
      (wfPerm (R := Rr) hF hq ⟨.swapU, ho⟩) (fun r => rfl) hB l hl hlen (fun x hx => (hlB x hx).2) (hs 1)
      (hv 1) (hc 1) v _ hS'.L hsrc hS'.tmp (hS'.pay 1) (hS'.priv 1) (hS'.hdr 1)
      (fun i hi hk => absurd (Fin.eq_last_of_not_lt (fun h => hk ⟨i, h⟩ (Fin.ext rfl))) hi)
    refine ⟨v', m, hu, ?_, Exec.cast he rfl (by simp)⟩
    simpa [opCost, Function.update_of_ne (hb.ne 1 _ .src)] using hm

/-! ### The gadget program -/

lemma prog_wf : ∀ o ∈ prog, Op.WF o := by
  simp [prog, E, Op.WF]

/-- The instructions of the gadget program with their well-formedness. -/
def progW : List {o : Op // o.WF} := prog.attach.map fun o => ⟨o.1, prog_wf o.1 o.2⟩

lemma progW_val : progW.map Subtype.val = prog := by
  simp [progW, List.map_map, Function.comp_def]

variable (ι) in
/-- The passes of the gadget program. -/
noncomputable def progPass (hb : Banks ι bank) (hQ : swapStates cxHd cxPay cxHd_inj ≤ Q)
    (hT : swapT 6 ≤ T) : Pr P T Q (prime + K) U :=
  Prog.seqList (progW.map fun o => opPass (ι := ι) F hb hQ hT o.1)

variable (body) in
/-- **The gadget program on the record stream** moves the records by its index map
`runIdx prog`. -/
theorem progPass_exec (hι : Function.Injective ι) (hF : F.Valid p len) (hO : F.Order)
    (hK : 0 < p.K) (hG : 0 < p.G) (hGK : p.G < p.K) (hb : Banks ι bank)
    (hQ : swapStates cxHd cxPay cxHd_inj ≤ Q) (hT : swapT 6 ≤ T) {Rr q B : ℕ} (hRr : 0 < Rr)
    (hq : ∀ g, touched F g → fieldOff len g + len g ≤ q) (hB : 1 ≤ B)
    (hs : Fin 2 → Fin 5 → List Bool)
    (hv : ∀ c k, Counter.value (hs c k) = swapValues
      (swapDimsIdx (len := len) F.b (swapFld F c) p.wc Rr q B).1
      (swapDimsIdx (len := len) F.b (swapFld F c) p.wc Rr q B).2.1
      (swapDimsIdx (len := len) F.b (swapFld F c) p.wc Rr q B).2.2 p.wc p.wc k)
    (hc : ∀ c k, GrowingCounterData.Canonical (hs c k))
    (S₀ : Stacks T (prime + K)) (hS : PassState ι bank p len B (Rr * 2 ^ q) hs S₀)
    (l : List (List (Fin (prime + K + 4)))) (hl : l.length = Rr * 2 ^ q)
    (hlB : ∀ r ∈ l, r.length = B ∧ ∀ s ∈ r, s.val < 8) (v : HS T Q (prime + K) U) :
    ∃ (v' : HS T Q (prime + K) U) (m : ℕ), v'.user = v.user ∧
      (m : ℝ) ≤ (prog.map (opCost p len T Rr q B fun c => ∑ j, (S₀.R (bank c j)).length)).sum +
        1 ∧
      Exec body (progPass (ι := ι) F hb hQ hT)
        (mk v { S₀ with R := Function.update S₀.R (ι .src) l.flatten }) m
        (mk v' { S₀ with
          R := Function.update S₀.R (ι .src) (moveRecs (listPerm (wfPerm (R := Rr) hF hq) progW)
            l).flatten }) := by
  obtain ⟨v', m, hu, hm, he⟩ := seqList_moveRecs body (fun o => opPass (ι := ι) F hb hQ hT o.1)
    (wfPerm (R := Rr) hF hq) (fun o => opCost p len T Rr q B
      (fun c => ∑ j, (S₀.R (bank c j)).length) o.1) (ι .src) S₀
    (fun r => r.length = B ∧ ∀ s ∈ r, s.val < 8) progW
    (fun o _ l' hl' hlB' v' => opPass_exec body F hι hF hO hK hG hGK hb hQ hT hRr hq hB hs hv hc
      S₀ hS o l' hl' hlB' v') l hl hlB v
  refine ⟨v', m, hu, ?_, he⟩
  rw [← progW_val, List.map_map] at *
  exact hm

end Ops

end IntegerMultBounds.MathlibTM2.Node
