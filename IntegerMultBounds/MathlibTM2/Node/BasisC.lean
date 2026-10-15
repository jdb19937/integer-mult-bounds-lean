module

public import IntegerMultBounds.MathlibTM2.Node.Basis
public import IntegerMultBounds.MathlibTM2.Node.CompactSlotXorPasses
public import IntegerMultBounds.MathlibTM2.Node.CompactParams

/-!
# The basis change of a factor by the compact slot XOR

`basisProgC v j` runs the compact slot XOR `compactXorProg` for `x = j`, `y = j'` for every
`j' ∈ basisTargets v j`, on the data `cxLayout m a₀ K ρ L R n rw k G j j'` whose control fields
are placed by `cxParams` (`Node/CompactParams.lean`): the parameter registers hold
`K ρ a₀ L rows n rw G k bB pT pU` (`cxParOf`).

**Main theorem** (`basisProgC_exec`). Under the hypotheses of `compactXor_exec`, with a control
field fitting below the slots and three above (`(k - 1) G ≤ a₀`, `a₀ + m L + 3 (k - 1) G ≤ n`),
the program takes `src` from `encZ A w Z` to `encZ A w (pullM e (basisMap v j) Z)`, every other
register and `user` as before, within the sum over `j' ∈ basisTargets v j` of the bounds
`cxCost A (cxLayout … j j') T` (`basisCostC`), plus one step.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Node

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Layer.PackedXor IntegerMultBounds.MathlibTM2.Layer.CompactXor
open IntegerMultBounds.Networks (BinaryWalsh.Address)
open IntegerMultBounds.MathlibTM2.Layer (ZArr encZ pullM basisMap m)

section ProgC

open IntegerMultBounds.Networks.Shared50ModularControl (prime)

variable {T Q Ka : ℕ} {U P : Type}
variable {ι : CXReg → Fin T} {par : CXPar → Fin T} {src st : Fin T}

/-- **The basis change** along `v` at `j`: the compact slot XOR of `j` into every
`j' ∈ basisTargets v j`. -/
noncomputable def basisProgC (henv : CxEnv ι par src) (hQ : swapStates sxHd sxPay sxHd_inj ≤ Q)
    (st : Fin T) (v : BinaryWalsh.Address m) (j : Fin m) : Pr P T Q (prime + Ka) U :=
  Prog.seqList ((basisTargets v j).map fun (j' : Fin m) =>
    compactXorProg henv hQ st (CxD.ofXY (j : ℕ) (j' : ℕ)))

/-- The parameter values of the slot XORs of a node: they do not depend on the slots. -/
def cxParOf (a₀ K ρ L R n rw k G : ℕ) : CXPar → ℕ :=
  (cxLayout m a₀ K ρ L R n rw k G 0 0).par

lemma cxLayout_par (a₀ K ρ L R n rw k G x y : ℕ) :
    (cxLayout m a₀ K ρ L R n rw k G x y).par = cxParOf a₀ K ρ L R n rw k G := by
  funext p; cases p <;> rfl

/-- The step bound of the slot XOR of `j` into `j'`. -/
noncomputable def basisCostC (A T a₀ K ρ L R n rw k G : ℕ) (j j' : Fin m) : ℝ :=
  cxCost A (cxLayout m a₀ K ρ L R n rw k G j j') T

variable (body : P → Pr P T Q (prime + Ka) U)

/-- The slot XORs of `j` into the slots `l`, from any array. -/
theorem basisListC_exec (henv : CxEnv ι par src) (hst : ∀ x, ι x ≠ st) (hsrcst : src ≠ st)
    (hA : 12 ≤ prime + Ka) (hQ : swapStates sxHd sxPay sxHd_inj ≤ Q)
    {a₀ K ρ k L R n r w G : ℕ} (hρ : ρ < K) (hLK : L = K * k) (hk : 2 ≤ k) (hR : 1 ≤ R)
    (hrw : 1 ≤ r * w) (hG : 1 ≤ G) (hGK : G + 3 ≤ K) (hfront : (k - 1) * G ≤ a₀)
    (hback : a₀ + m * L + 3 * ((k - 1) * G) ≤ n) {e : Fin (m * k) → Fin n}
    (he : ∀ i, (e i : ℕ) = a₀ + ρ + K * i) (j : Fin m) :
    ∀ (l : List (Fin m)), (∀ j' ∈ l, j' ≠ j) →
    ∀ (Z : ZArr (Fin R × Fin r) n) (v : HS T Q (prime + Ka) U) (S : Stacks T (prime + Ka)),
      (∀ y, S.L y = []) → S.R src = encZ (prime + Ka) w Z →
      (∀ p, (S.R (par p)).length = cxParOf a₀ K ρ L R n (r * w) k G p) →
      (∀ x, S.R (ι x) = []) →
      ∃ (v' : HS T Q (prime + Ka) U) (c : ℕ), v'.user = v.user ∧
        (c : ℝ) ≤ (l.map fun j' => basisCostC (prime + Ka) T a₀ K ρ L R n (r * w) k G j j').sum + 1 ∧
        Exec body (Prog.seqList (l.map fun (j' : Fin m) =>
            compactXorProg henv hQ st (CxD.ofXY (j : ℕ) (j' : ℕ)))) (mk v S) c
          (mk v' { S with
            R := Function.update S.R src (encZ (prime + Ka) w (pullM e (basisFold j l) Z)) })
  | [], _, Z, v, S, _, hSsrc, _, _ => by
      refine ⟨v, 1, rfl, by simp, Exec.cast (Exec.act (body := body) .done (mk v S)) rfl ?_⟩
      have hid : basisFold j [] = id := rfl
      rw [run_done, hid, basis_pullM_id, ← hSsrc, Function.update_eq_self]
  | j' :: l, hl, Z, v, S, hL, hSsrc, hpar, hrest => by
      have hj' : j' ≠ j := hl j' List.mem_cons_self
      have hv : (cxLayout m a₀ K ρ L R n (r * w) k G j j').Valid :=
        cxLayout_valid hρ hLK hk hR hrw (fun h => hj' (Fin.ext h).symm) j.isLt j'.isLt hG hGK
          hfront hback
      obtain ⟨v₁, c₁, hu₁, hc₁, he₁⟩ := compactXor_exec body henv hQ hst hsrcst hA hv
        (r := r) (w := w) rfl (x := j) (y := j') rfl rfl he Z v S hL hSsrc
        (fun p => by rw [hpar p, cxLayout_par]) hrest
      rw [← compactXorProg_ofXY henv hQ st (cxLayout m a₀ K ρ L R n (r * w) k G j j')] at he₁
      set Z₁ := pullM e (sxXorCol j j') Z with hZ₁
      obtain ⟨v₂, c₂, hu₂, hc₂, he₂⟩ := basisListC_exec henv hst hsrcst hA hQ hρ hLK hk hR hrw
        hG hGK hfront hback he j l (fun j'' h => hl j'' (List.mem_cons_of_mem _ h)) Z₁ v₁
        { S with R := Function.update S.R src (encZ (prime + Ka) w Z₁) } hL
        (by simp)
        (fun p => by simp only [Function.update_of_ne (henv.hsrcp p)]; exact hpar p)
        (fun x => by simp only [Function.update_of_ne (henv.hsrc x)]; exact hrest x)
      have hfold : pullM e (basisFold j l) Z₁ = pullM e (basisFold j (j' :: l)) Z := by
        rw [hZ₁, basis_pullM_pullM (basis_e_inj (by omega) he)]
        rfl
      refine ⟨v₂, c₁ + c₂, hu₂.trans hu₁, ?_, ?_⟩
      · simp only [List.map_cons, List.sum_cons]
        push_cast
        have h1 : (c₁ : ℝ) ≤ basisCostC (prime + Ka) T a₀ K ρ L R n (r * w) k G j j' := hc₁
        linarith
      · refine Exec.cast (Exec.seq he₁ he₂) rfl ?_
        rw [Function.update_idem, hfold]

/-- **The basis change.** For `v j = 1`, on the stream register `src` holding `encZ A w Z`, the
program `basisProgC v j` leaves `encZ A w (pullM e (basisMap v j) Z)` on `src`; every other
register ends as it started and `user` is kept. The step bound is the sum of the slot-XOR bounds
(`basisCostC`, from `compactXor_exec`) over the slots `j' ∈ basisTargets v j`, plus one. -/
theorem basisProgC_exec (henv : CxEnv ι par src) (hst : ∀ x, ι x ≠ st) (hsrcst : src ≠ st)
    (hA : 12 ≤ prime + Ka) (hQ : swapStates sxHd sxPay sxHd_inj ≤ Q)
    {a₀ K ρ k L R n r w G : ℕ} (hρ : ρ < K) (hLK : L = K * k) (hk : 2 ≤ k) (hR : 1 ≤ R)
    (hrw : 1 ≤ r * w) (hG : 1 ≤ G) (hGK : G + 3 ≤ K) (hfront : (k - 1) * G ≤ a₀)
    (hback : a₀ + m * L + 3 * ((k - 1) * G) ≤ n) {e : Fin (m * k) → Fin n}
    (he : ∀ i, (e i : ℕ) = a₀ + ρ + K * i) (vv : BinaryWalsh.Address m) (j : Fin m)
    (hvj : vv j = 1) (Z : ZArr (Fin R × Fin r) n) (v : HS T Q (prime + Ka) U)
    (S : Stacks T (prime + Ka)) (hL : ∀ y, S.L y = []) (hSsrc : S.R src = encZ (prime + Ka) w Z)
    (hpar : ∀ p, (S.R (par p)).length = cxParOf a₀ K ρ L R n (r * w) k G p)
    (hrest : ∀ x, S.R (ι x) = []) :
    ∃ (v' : HS T Q (prime + Ka) U) (c : ℕ), v'.user = v.user ∧
      (c : ℝ) ≤ ((basisTargets vv j).map fun j' =>
          basisCostC (prime + Ka) T a₀ K ρ L R n (r * w) k G j j').sum + 1 ∧
      Exec body (basisProgC henv hQ st vv j) (mk v S) c
        (mk v' { S with
          R := Function.update S.R src (encZ (prime + Ka) w (pullM e (basisMap vv j) Z)) }) := by
  obtain ⟨v', c, hu, hc, hex⟩ := basisListC_exec body henv hst hsrcst hA hQ hρ hLK hk hR hrw hG
    hGK hfront hback he j (basisTargets vv j) (fun j' h => (mem_basisTargets.1 h).2) Z v S hL
    hSsrc hpar hrest
  rw [basisFold_eq vv j hvj] at hex
  exact ⟨v', c, hu, hc, hex⟩

end ProgC

/-! ### The single-column slot XOR -/

section Fix1

variable {T Q A : ℕ} {U P : Type} (body : P → Pr P T Q A U)
variable {ι : CXReg → Fin T} {par : CXPar → Fin T} {src st : Fin T}

/-- The five-field tiling of a single-column slot XOR of slot `x` into slot `y` (`x ≠ y`): the
bits below the lower slot, the lower slot, the gap, the upper slot and the bits above. -/
def len5 (a₀ L n x y : ℕ) : Fin 5 → ℕ :=
  ![a₀ + min x y * L, L, (max x y - min x y - 1) * L, L, n - (a₀ + (max x y + 1) * L)]

/-- The source field. -/
def fX5 (x y : ℕ) : Fin 5 := if x < y then 1 else 3

/-- The target field. -/
def fY5 (x y : ℕ) : Fin 5 := if x < y then 3 else 1

lemma fX5_ne_fY5 (x y : ℕ) : fX5 x y ≠ fY5 x y := by unfold fX5 fY5; split_ifs <;> decide

lemma len5_fX5 (a₀ L n x y : ℕ) : len5 a₀ L n x y (fX5 x y) = L := by
  unfold fX5 len5; split_ifs <;> rfl

lemma len5_fY5 (a₀ L n x y : ℕ) : len5 a₀ L n x y (fY5 x y) = L := by
  unfold fY5 len5; split_ifs <;> rfl

lemma max_mul_of_ne {x y L : ℕ} (hxy : x ≠ y) :
    max x y * L = min x y * L + L + (max x y - min x y - 1) * L := by
  obtain ⟨d, hd⟩ : ∃ d, max x y = min x y + 1 + d := ⟨max x y - min x y - 1, by omega⟩
  rw [show max x y - min x y - 1 = d by omega, hd]
  ring

/-- The entries of the five-field tiling. -/
lemma len5_val (a₀ L n x y : ℕ) :
    (∀ h : 0 < 5, len5 a₀ L n x y ⟨0, h⟩ = a₀ + min x y * L) ∧
      (∀ h : 1 < 5, len5 a₀ L n x y ⟨1, h⟩ = L) ∧
      (∀ h : 2 < 5, len5 a₀ L n x y ⟨2, h⟩ = (max x y - min x y - 1) * L) ∧
      (∀ h : 3 < 5, len5 a₀ L n x y ⟨3, h⟩ = L) ∧
      (∀ h : 4 < 5, len5 a₀ L n x y ⟨4, h⟩ = n - (a₀ + (max x y + 1) * L)) :=
  ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩

lemma foff5 {a₀ L n x y : ℕ} (hxy : x ≠ y) :
    foff (len5 a₀ L n x y) 1 = a₀ + min x y * L ∧
      foff (len5 a₀ L n x y) 3 = a₀ + max x y * L := by
  have hm := max_mul_of_ne (L := L) hxy
  obtain ⟨l0, l1, l2, l3, l4⟩ := len5_val a₀ L n x y
  show foff (len5 a₀ L n x y) ⟨1, by omega⟩ = _ ∧ foff (len5 a₀ L n x y) ⟨3, by omega⟩ = _
  simp only [foff_eq_sum_range, Finset.sum_range_succ, Finset.sum_range_zero, Nat.reduceLT,
    dite_true, l0, l1, l2]
  constructor <;> omega

lemma foff5_fX5 {a₀ L n x y : ℕ} (hxy : x ≠ y) :
    foff (len5 a₀ L n x y) (fX5 x y) = a₀ + x * L := by
  obtain ⟨h1, h3⟩ := foff5 (a₀ := a₀) (L := L) (n := n) hxy
  unfold fX5
  split_ifs with h
  · rw [h1, min_eq_left h.le]
  · rw [h3, max_eq_left (by omega)]

lemma foff5_fY5 {a₀ L n x y : ℕ} (hxy : x ≠ y) :
    foff (len5 a₀ L n x y) (fY5 x y) = a₀ + y * L := by
  obtain ⟨h1, h3⟩ := foff5 (a₀ := a₀) (L := L) (n := n) hxy
  unfold fY5
  split_ifs with h
  · rw [h3, max_eq_right h.le]
  · rw [h1, min_eq_right (by omega)]

lemma hSY5 {a₀ L n x y : ℕ} (hxy : x ≠ y) (hx : x < m) (hy : y < m) (hfit : a₀ + m * L ≤ n) :
    foff (len5 a₀ L n x y) (fY5 x y) + len5 a₀ L n x y (fY5 x y) ≤ n := by
  rw [foff5_fY5 hxy, len5_fY5]
  have : (y + 1) * L ≤ m * L := Nat.mul_le_mul_right _ hy
  rw [Nat.add_mul, one_mul] at this
  omega

lemma len5_sum {a₀ L n x y : ℕ} (hxy : x ≠ y) (hy : y < m) (hx : x < m)
    (hfit : a₀ + m * L ≤ n) : ∑ g, len5 a₀ L n x y g = n := by
  have hm := max_mul_of_ne (L := L) hxy
  have hmL : (max x y + 1) * L ≤ m * L := Nat.mul_le_mul_right _ (by omega)
  have e : (max x y + 1) * L = max x y * L + L := by rw [Nat.add_mul, one_mul]
  obtain ⟨l0, l1, l2, l3, l4⟩ := len5_val a₀ L n x y
  rw [Fin.sum_univ_five]
  show len5 a₀ L n x y ⟨0, by omega⟩ + len5 a₀ L n x y ⟨1, by omega⟩ +
    len5 a₀ L n x y ⟨2, by omega⟩ + len5 a₀ L n x y ⟨3, by omega⟩ +
    len5 a₀ L n x y ⟨4, by omega⟩ = n
  rw [l0, l1, l2, l3, l4]
  rw [e] at hmL ⊢
  omega

/-- With no carry column the top fixup is the full XOR. -/
lemma moveRecs_topFix_zero {nf : ℕ} (len : Fin nf → ℕ) {X Y : Fin nf} (hXY : X ≠ Y)
    (hLXY : len X = len Y) {R S : ℕ} (hSY : foff len Y + len Y ≤ S) {K : ℕ} (ρ : ℕ) (hK : 1 ≤ K)
    (l : List (List (Fin (A + 4)))) :
    moveRecs (topFixPermC len X Y K ρ 0 (R := R) hXY hLXY hSY) l =
      moveRecs (fullXorPermC len X Y K ρ 0 (R := R) hXY hLXY hSY) l := by
  congr 1
  exact Equiv.ext fun a => Fin.ext (by
    rw [topFixPermC_apply, fullXorPermC_apply, fullXorC_eq len hK hXY hLXY]
    unfold idealC
    simp [selMask, setDig_dig])

/-- The field register of the five-field tiling. -/
def fld5 (g : Fin 5) : CXReg := .fld ⟨g.val, by omega⟩

/-- The registers of the single-column slot XOR built from the parameters: `ctrB` (`rw`),
`cnt` (`R 2^n`), the mask `tm = binSyms L (2^ρ)` on `mtopC`, and the five zero fields of
`len5` on `fld 0` … `fld 4`. -/
noncomputable def fix1Setup (ι : CXReg → Fin T) (par : CXPar → Fin T) (x y : ℕ) :
    Pr P T Q A U :=
  .seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (ucopy (par .rw) (ι (.sx .ctrB)) (ι (.ts 0)))
    (ucopy (par .rows) (ι (.sx .cnt)) (ι (.ts 0))))
    (upow2 (par .n) (ι (.sx .cnt)) (ι (.ts 0)) (ι (.ts 1))))
    (bitMask (par .L) (par .ρ) (ι .mtopC) (ι (.ts 0)) (ι (.ts 1)) (ι (.ts 2))))
    (ucopy (par .a₀) (ι (.ts 0)) (ι (.ts 1))))
    (umul (min x y) (par .L) (ι (.ts 0)) (ι (.ts 1))))
    (zeroBits (ι (.ts 0)) (ι (fld5 0)) (ι (.ts 1))))
    (uclear (ι (.ts 0))))
    (zeroBits (par .L) (ι (fld5 1)) (ι (.ts 1))))
    (umul (max x y - min x y - 1) (par .L) (ι (.ts 0)) (ι (.ts 1))))
    (zeroBits (ι (.ts 0)) (ι (fld5 2)) (ι (.ts 1))))
    (uclear (ι (.ts 0))))
    (zeroBits (par .L) (ι (fld5 3)) (ι (.ts 1))))
    (ucopy (par .n) (ι (.ts 0)) (ι (.ts 1))))
    (usub (par .a₀) (ι (.ts 0)) (ι (.ts 1))))
    (umul (max x y + 1) (par .L) (ι (.ts 2)) (ι (.ts 1))))
    (usub (ι (.ts 2)) (ι (.ts 0)) (ι (.ts 1))))
    (uclear (ι (.ts 2))))
    (zeroBits (ι (.ts 0)) (ι (fld5 4)) (ι (.ts 1))))
    (uclear (ι (.ts 0)))

/-- The step bound of `fix1Setup`. -/
def fix1SetupCost (a₀ ρ L R n rw : ℕ) : ℕ :=
  4 * rw + 4 * R + 4 * (2 ^ n * R) + 9 * n + 10 * L + 4 * ρ + 40 * a₀ + 40 * (m * L) +
    20 * n + 100

/-- The registers of `fix1Setup`. -/
def Fix1Regs (ι : CXReg → Fin T) (a₀ L R n rw ρ x y : ℕ)
    (R' : Fin T → List (Fin (A + 4))) : Prop :=
  (R' (ι (.sx .ctrB))).length = rw ∧ (R' (ι (.sx .cnt))).length = R * 2 ^ n ∧
    R' (ι .mtopC) = binSyms L (2 ^ ρ) ∧ ∀ g : Fin 5, R' (ι (fld5 g)) = binSyms (len5 a₀ L n x y g) 0

set_option hygiene false in
macro "f1simp" : tactic => `(tactic|
  simp [Function.update_of_ne, henv.hι.eq_iff, henv.hpar.eq_iff, henv.hpι, henv.hpι', hrest,
    Fin.ext_iff, hK, hρr, ha₀, hLr, hrows, hn, hrwr, fld5])

set_option hygiene false in
macro "f1simp" "at" h:ident : tactic => `(tactic|
  simp [Function.update_of_ne, henv.hι.eq_iff, henv.hpar.eq_iff, henv.hpι, henv.hpι', hrest,
    Fin.ext_iff, hK, hρr, ha₀, hLr, hrows, hn, hrwr, fld5] at $h:ident ⊢)

/-- The registers the single-column setup leaves alone. -/
def Fix1Untouched (ι : CXReg → Fin T) (t : Fin T) : Prop :=
  t ≠ ι (.sx .ctrB) ∧ t ≠ ι (.sx .cnt) ∧ t ≠ ι .mtopC ∧ (∀ g : Fin 5, t ≠ ι (fld5 g)) ∧
    t ≠ ι (.ts 0) ∧ t ≠ ι (.ts 1) ∧ t ≠ ι (.ts 2)

set_option maxHeartbeats 2000000 in
theorem fix1Setup_exec (henv : CxEnv ι par src) {a₀ K ρ L R n rw : ℕ} (x y : ℕ)
    (hxy : x ≠ y) (hx : x < m) (hy : y < m) (hfit : a₀ + m * L ≤ n)
    (v : HS T Q A U) (S : Stacks T A) (hrest : ∀ z, S.R (ι z) = [])
    (hK : (S.R (par .K)).length = K) (hρr : (S.R (par .ρ)).length = ρ)
    (ha₀ : (S.R (par .a₀)).length = a₀) (hLr : (S.R (par .L)).length = L)
    (hrows : (S.R (par .rows)).length = R) (hn : (S.R (par .n)).length = n)
    (hrwr : (S.R (par .rw)).length = rw) :
    ∃ (v' : HS T Q A U) (R' : Fin T → List (Fin (A + 4))) (c : ℕ), v'.user = v.user ∧
      c ≤ fix1SetupCost a₀ ρ L R n rw ∧
      Exec body (fix1Setup ι par x y) (mk v S) c (mk v' { S with R := R' }) ∧
      Fix1Regs ι a₀ L R n rw ρ x y R' ∧
      (R' (ι (.ts 0)) = [] ∧ R' (ι (.ts 1)) = [] ∧ R' (ι (.ts 2)) = []) ∧
      ∀ t, Fix1Untouched ι t → R' t = S.R t := by
  have hm := max_mul_of_ne (L := L) hxy
  have hmL : (max x y + 1) * L ≤ m * L := Nat.mul_le_mul_right _ (by omega)
  have hminL : min x y * L ≤ m * L := Nat.mul_le_mul_right _ (by omega)
  have hgapL : (max x y - min x y - 1) * L ≤ m * L := Nat.mul_le_mul_right _ (by omega)
  have hLm : L ≤ m * L := Nat.le_mul_of_pos_left _ (by norm_num [m])
  have hpU : ∀ p, Fix1Untouched ι (par p) := fun p =>
    ⟨henv.hpι' _ _, henv.hpι' _ _, henv.hpι' _ _, fun _ => henv.hpι' _ _, henv.hpι' _ _,
      henv.hpι' _ _, henv.hpι' _ _⟩
  have hne : ∀ {a b : CXReg}, a ≠ b → ι a ≠ ι b := fun h => henv.hι.ne h
  -- the distinctness facts
  have hc0 : ι (.ts 0) ≠ ι (.sx .ctrB) := hne (by simp)
  have hc1 : ι (.ts 0) ≠ ι (.sx .cnt) := hne (by simp)
  have hc2 : ι (.ts 0) ≠ ι .mtopC := hne (by simp)
  have hc3 : ∀ g : Fin 5, ι (.ts 0) ≠ ι (fld5 g) := fun g => hne (by simp [fld5])
  have hc4 : ι (.ts 1) ≠ ι (.ts 0) := hne (by simp)
  have hc5 : ι (.ts 2) ≠ ι (.ts 0) := hne (by simp)
  have hd0 : ι (.ts 1) ≠ ι (.sx .ctrB) := hne (by simp)
  have hd1 : ι (.ts 1) ≠ ι (.sx .cnt) := hne (by simp)
  have hd2 : ι (.ts 1) ≠ ι .mtopC := hne (by simp)
  have hd3 : ∀ g : Fin 5, ι (.ts 1) ≠ ι (fld5 g) := fun g => hne (by simp [fld5])
  have hd5 : ι (.ts 2) ≠ ι (.ts 1) := hne (by simp)
  have he0 : ι (.ts 2) ≠ ι (.sx .ctrB) := hne (by simp)
  have he1' : ι (.ts 2) ≠ ι (.sx .cnt) := hne (by simp)
  have he2' : ι (.ts 2) ≠ ι .mtopC := hne (by simp)
  have he3 : ∀ g : Fin 5, ι (.ts 2) ≠ ι (fld5 g) := fun g => hne (by simp [fld5])
  have hf : ∀ g g' : Fin 5, g ≠ g' → ι (fld5 g) ≠ ι (fld5 g') := fun g g' h =>
    hne (by simp [fld5, Fin.ext_iff]; omega)
  have hf5 : ∀ g : Fin 5, ι (.sx .ctrB) ≠ ι (fld5 g) := fun g => hne (by simp [fld5])
  have hf5' : ∀ g : Fin 5, ι (.sx .cnt) ≠ ι (fld5 g) := fun g => hne (by simp [fld5])
  have hf5'' : ∀ g : Fin 5, ι .mtopC ≠ ι (fld5 g) := fun g => hne (by simp [fld5])
  -- 1. `ctrB`
  obtain ⟨v₁, hu₁, he₁⟩ := ucopy_exec body (a := par .rw) (b := ι (.sx .ctrB)) (t := ι (.ts 0))
    (by f1simp) (by f1simp) (by f1simp) v S (hrest _)
  rw [hrwr, hrest, List.append_nil] at he₁
  set R₁ := Function.update S.R (ι (.sx .ctrB)) (List.replicate rw tick) with hR₁
  have hR₁S : ∀ t, t ≠ ι (.sx .ctrB) → R₁ t = S.R t := fun t ht => by
    rw [hR₁, Function.update_of_ne ht]
  have hR₁c : R₁ (ι (.sx .ctrB)) = List.replicate rw tick := by rw [hR₁, Function.update_self]
  -- 2. `cnt`
  obtain ⟨v₂, hu₂, he₂⟩ := ucopy_exec body (a := par .rows) (b := ι (.sx .cnt)) (t := ι (.ts 0))
    (by f1simp) (by f1simp) (by f1simp) v₁ { S with R := R₁ }
    (by show R₁ _ = []; rw [hR₁S _ hc0]; exact hrest _)
  dsimp only at he₂
  rw [hR₁S _ (hpU _).1, hrows, hR₁S _ (hne (by simp)), hrest, List.append_nil] at he₂
  set R₂ := Function.update R₁ (ι (.sx .cnt)) (List.replicate R tick) with hR₂
  have hR₂S : ∀ t, t ≠ ι (.sx .ctrB) → t ≠ ι (.sx .cnt) → R₂ t = S.R t := fun t h1 h2 => by
    rw [hR₂, Function.update_of_ne h2, hR₁S _ h1]
  have hR₂c : R₂ (ι (.sx .cnt)) = List.replicate R tick := by rw [hR₂, Function.update_self]
  -- 3. `cnt := R 2^n`
  obtain ⟨v₃, m₃, hu₃, hm₃, he₃⟩ := upow2_exec body (a := par .n) (b := ι (.sx .cnt))
    (t₁ := ι (.ts 0)) (t₂ := ι (.ts 1)) (by f1simp) v₂ { S with R := R₂ }
    (by show R₂ _ = []; rw [hR₂S _ hc0 hc1]; exact hrest _)
    (by show R₂ _ = []; rw [hR₂S _ hd0 hd1]; exact hrest _)
  dsimp only at he₃ hm₃
  rw [hR₂S _ (hpU _).1 (hpU _).2.1, hn, hR₂c, flatMap_replicate_of_replicate] at he₃
  rw [hR₂S _ (hpU _).1 (hpU _).2.1, hn, hR₂c, List.length_replicate] at hm₃
  set R₃ := Function.update R₂ (ι (.sx .cnt)) (List.replicate (R * 2 ^ n) tick) with hR₃
  have hR₃S : ∀ t, t ≠ ι (.sx .ctrB) → t ≠ ι (.sx .cnt) → R₃ t = S.R t := fun t h1 h2 => by
    rw [hR₃, Function.update_of_ne h2, hR₂S _ h1 h2]
  have hR₃c : R₃ (ι (.sx .cnt)) = List.replicate (R * 2 ^ n) tick := by
    rw [hR₃, Function.update_self]
  have hR₃b : R₃ (ι (.sx .ctrB)) = List.replicate rw tick := by
    rw [hR₃, Function.update_of_ne (hne (by simp)), hR₂, Function.update_of_ne (hne (by simp)), hR₁c]
  -- 4. the mask
  obtain ⟨v₄, hu₄, he₄⟩ := bitMask_exec body (nR := par .L) (tR := par .ρ) (z := ι .mtopC)
    (cnt := ι (.ts 0)) (w := ι (.ts 1)) (t₁ := ι (.ts 2)) (by f1simp) (n := L) (t := ρ) v₃
    { S with R := R₃ } (by show (R₃ _).length = L; rw [hR₃S _ (hpU _).1 (hpU _).2.1]; exact hLr)
    (by show (R₃ _).length = ρ; rw [hR₃S _ (hpU _).1 (hpU _).2.1]; exact hρr)
    (by show R₃ _ = []; rw [hR₃S _ hc0 hc1]; exact hrest _)
    (by show R₃ _ = []; rw [hR₃S _ hd0 hd1]; exact hrest _)
    (by show R₃ _ = []; rw [hR₃S _ he0 he1']; exact hrest _)
  dsimp only at he₄
  rw [hR₃S _ (hne (by simp)) (hne (by simp)), hrest, List.append_nil] at he₄
  set R₄ := Function.update R₃ (ι .mtopC) (binSyms L (2 ^ ρ)) with hR₄
  have hR₄S : ∀ t, t ≠ ι (.sx .ctrB) → t ≠ ι (.sx .cnt) → t ≠ ι .mtopC → R₄ t = S.R t :=
    fun t h1 h2 h3 => by rw [hR₄, Function.update_of_ne h3, hR₃S _ h1 h2]
  -- the fields: a generic step
  have hfld : ∀ (F : Fin T → List (Fin (A + 4))) (v : HS T Q A U) (g : Fin 5) (val : ℕ)
      (hts0 : (F (ι (.ts 0))).length = val) (hts1 : F (ι (.ts 1)) = [])
      (hfg : F (ι (fld5 g)) = []),
      ∃ v' : HS T Q A U, v'.user = v.user ∧
        Exec body (zeroBits (ι (.ts 0)) (ι (fld5 g)) (ι (.ts 1))) (mk v { S with R := F })
          (4 * val + 4) (mk v' { S with R := Function.update F (ι (fld5 g)) (binSyms val 0) }) := by
    intro F v g val hts0 hts1 hfg
    obtain ⟨v', hu, he⟩ := zeroBits_exec body (len := ι (.ts 0)) (z := ι (fld5 g)) (t := ι (.ts 1))
      (hc3 g) hc4.symm (hd3 g).symm v { S with R := F } hts1
    dsimp only at he
    rw [hts0, hfg, List.append_nil] at he
    exact ⟨v', hu, he⟩
  -- 5. `ts 0 := a₀`
  obtain ⟨v₅, hu₅, he₅⟩ := ucopy_exec body (a := par .a₀) (b := ι (.ts 0)) (t := ι (.ts 1))
    (by f1simp) (by f1simp) hc4.symm v₄ { S with R := R₄ }
    (by show R₄ _ = []; rw [hR₄S _ hd0 hd1 hd2]; exact hrest _)
  dsimp only at he₅
  rw [hR₄S _ (hpU _).1 (hpU _).2.1 (hpU _).2.2.1, ha₀, hR₄S _ hc0 hc1 hc2, hrest,
    List.append_nil] at he₅
  set R₅ := Function.update R₄ (ι (.ts 0)) (List.replicate a₀ tick) with hR₅
  have hs₅ : ∀ t, t ≠ ι (.ts 0) → R₅ t = R₄ t := fun t h => by rw [hR₅, Function.update_of_ne h]
  -- 6. `ts 0 += min x y · L`
  obtain ⟨v₆, hu₆, he₆⟩ := umul_exec body (min x y) (a := par .L) (b := ι (.ts 0)) (t := ι (.ts 1))
    (by f1simp) (by f1simp) hc4.symm v₅ { S with R := R₅ }
    (by show R₅ _ = []; rw [hs₅ _ hc4, hR₄S _ hd0 hd1 hd2]; exact hrest _)
  dsimp only at he₆
  rw [hs₅ _ (hpU _).2.2.2.2.1, hR₄S _ (hpU _).1 (hpU _).2.1 (hpU _).2.2.1, hLr, hR₅,
    Function.update_self, List.replicate_append_replicate] at he₆
  set R₆ := Function.update R₅ (ι (.ts 0)) (List.replicate (min x y * L + a₀) tick) with hR₆
  have hs₆ : ∀ t, t ≠ ι (.ts 0) → R₆ t = R₅ t := fun t h => by rw [hR₆, Function.update_of_ne h]
  have hR₆0 : R₆ (ι (.ts 0)) = List.replicate (min x y * L + a₀) tick := by
    rw [hR₆, Function.update_self]
  -- 7. field 0
  obtain ⟨v₇, hu₇, he₇⟩ := hfld R₆ v₆ 0 (min x y * L + a₀) (by rw [hR₆0, List.length_replicate])
    (by rw [hs₆ _ hc4, hs₅ _ hc4, hR₄S _ hd0 hd1 hd2]; exact hrest _)
    (by rw [hs₆ _ (hc3 0).symm, hs₅ _ (hc3 0).symm, hR₄S _ (hne (by simp [fld5]))
      (hne (by simp [fld5])) (hne (by simp [fld5]))]; exact hrest _)
  set R₇ := Function.update R₆ (ι (fld5 0)) (binSyms (min x y * L + a₀) 0) with hR₇
  have hs₇ : ∀ t, t ≠ ι (fld5 0) → R₇ t = R₆ t := fun t h => by rw [hR₇, Function.update_of_ne h]
  -- 8. clear `ts 0`
  obtain ⟨v₈, hu₈, he₈⟩ := uclear_exec body (ι (.ts 0)) v₇ { S with R := R₇ }
  dsimp only at he₈
  rw [hs₇ _ (hc3 0), hR₆0] at he₈
  set R₈ := Function.update R₇ (ι (.ts 0)) [] with hR₈
  have hs₈ : ∀ t, t ≠ ι (.ts 0) → R₈ t = R₇ t := fun t h => by rw [hR₈, Function.update_of_ne h]
  have hR₈0 : R₈ (ι (.ts 0)) = [] := by rw [hR₈, Function.update_self]
  -- 9. field 1
  obtain ⟨v₉, hu₉, he₉⟩ := zeroBits_exec body (len := par .L) (z := ι (fld5 1)) (t := ι (.ts 1))
    (by f1simp) (by f1simp) (hd3 1).symm v₈ { S with R := R₈ }
    (by show R₈ _ = []; rw [hs₈ _ hc4, hs₇ _ (hd3 0), hs₆ _ hc4, hs₅ _ hc4, hR₄S _ hd0 hd1 hd2]
        exact hrest _)
  dsimp only at he₉
  rw [hs₈ _ (hpU _).2.2.2.2.1, hs₇ _ ((hpU _).2.2.2.1 0), hs₆ _ (hpU _).2.2.2.2.1,
    hs₅ _ (hpU _).2.2.2.2.1, hR₄S _ (hpU _).1 (hpU _).2.1 (hpU _).2.2.1, hLr,
    hs₈ _ (hc3 1).symm, hs₇ _ (hf 1 0 (by decide)), hs₆ _ (hc3 1).symm, hs₅ _ (hc3 1).symm,
    hR₄S _ (hne (by simp [fld5])) (hne (by simp [fld5])) (hne (by simp [fld5])), hrest,
    List.append_nil] at he₉
  set R₉ := Function.update R₈ (ι (fld5 1)) (binSyms L 0) with hR₉
  have hs₉ : ∀ t, t ≠ ι (fld5 1) → R₉ t = R₈ t := fun t h => by rw [hR₉, Function.update_of_ne h]
  -- 10. `ts 0 := (max x y - min x y - 1) L`
  obtain ⟨v₁₀, hu₁₀, he₁₀⟩ := umul_exec body (max x y - min x y - 1) (a := par .L)
    (b := ι (.ts 0)) (t := ι (.ts 1)) (by f1simp) (by f1simp) hc4.symm v₉ { S with R := R₉ }
    (by show R₉ _ = []; rw [hs₉ _ (hd3 1), hs₈ _ hc4, hs₇ _ (hd3 0), hs₆ _ hc4, hs₅ _ hc4,
          hR₄S _ hd0 hd1 hd2]
        exact hrest _)
  dsimp only at he₁₀
  rw [hs₉ _ ((hpU _).2.2.2.1 1), hs₈ _ (hpU _).2.2.2.2.1, hs₇ _ ((hpU _).2.2.2.1 0),
    hs₆ _ (hpU _).2.2.2.2.1, hs₅ _ (hpU _).2.2.2.2.1, hR₄S _ (hpU _).1 (hpU _).2.1 (hpU _).2.2.1,
    hLr, hs₉ _ (hc3 1), hR₈0, List.append_nil] at he₁₀
  set R₁₀ := Function.update R₉ (ι (.ts 0)) (List.replicate ((max x y - min x y - 1) * L) tick)
    with hR₁₀
  have hs₁₀ : ∀ t, t ≠ ι (.ts 0) → R₁₀ t = R₉ t := fun t h => by
    rw [hR₁₀, Function.update_of_ne h]
  have hR₁₀0 : R₁₀ (ι (.ts 0)) = List.replicate ((max x y - min x y - 1) * L) tick := by
    rw [hR₁₀, Function.update_self]
  -- 11. field 2
  obtain ⟨v₁₁, hu₁₁, he₁₁⟩ := hfld R₁₀ v₁₀ 2 ((max x y - min x y - 1) * L)
    (by rw [hR₁₀0, List.length_replicate])
    (by rw [hs₁₀ _ hc4, hs₉ _ (hd3 1), hs₈ _ hc4, hs₇ _ (hd3 0), hs₆ _ hc4, hs₅ _ hc4,
          hR₄S _ hd0 hd1 hd2]
        exact hrest _)
    (by rw [hs₁₀ _ (hc3 2).symm, hs₉ _ (hf 2 1 (by decide)), hs₈ _ (hc3 2).symm,
          hs₇ _ (hf 2 0 (by decide)), hs₆ _ (hc3 2).symm, hs₅ _ (hc3 2).symm,
          hR₄S _ (hne (by simp [fld5])) (hne (by simp [fld5])) (hne (by simp [fld5]))]
        exact hrest _)
  set R₁₁ := Function.update R₁₀ (ι (fld5 2)) (binSyms ((max x y - min x y - 1) * L) 0) with hR₁₁
  have hs₁₁ : ∀ t, t ≠ ι (fld5 2) → R₁₁ t = R₁₀ t := fun t h => by
    rw [hR₁₁, Function.update_of_ne h]
  -- 12. clear `ts 0`
  obtain ⟨v₁₂, hu₁₂, he₁₂⟩ := uclear_exec body (ι (.ts 0)) v₁₁ { S with R := R₁₁ }
  dsimp only at he₁₂
  rw [hs₁₁ _ (hc3 2), hR₁₀0] at he₁₂
  set R₁₂ := Function.update R₁₁ (ι (.ts 0)) [] with hR₁₂
  have hs₁₂ : ∀ t, t ≠ ι (.ts 0) → R₁₂ t = R₁₁ t := fun t h => by
    rw [hR₁₂, Function.update_of_ne h]
  have hR₁₂0 : R₁₂ (ι (.ts 0)) = [] := by rw [hR₁₂, Function.update_self]
  -- a frame for the parameters and `ts 1` through steps 5–12
  have hpar₁₂ : ∀ p, R₁₂ (par p) = S.R (par p) := fun p => by
    rw [hs₁₂ _ (hpU _).2.2.2.2.1, hs₁₁ _ ((hpU _).2.2.2.1 2), hs₁₀ _ (hpU _).2.2.2.2.1,
      hs₉ _ ((hpU _).2.2.2.1 1), hs₈ _ (hpU _).2.2.2.2.1, hs₇ _ ((hpU _).2.2.2.1 0),
      hs₆ _ (hpU _).2.2.2.2.1, hs₅ _ (hpU _).2.2.2.2.1,
      hR₄S _ (hpU _).1 (hpU _).2.1 (hpU _).2.2.1]
  have hts1₁₂ : R₁₂ (ι (.ts 1)) = [] := by
    rw [hs₁₂ _ hc4, hs₁₁ _ (hd3 2), hs₁₀ _ hc4, hs₉ _ (hd3 1), hs₈ _ hc4, hs₇ _ (hd3 0),
      hs₆ _ hc4, hs₅ _ hc4, hR₄S _ hd0 hd1 hd2]
    exact hrest _
  have hts2₁₂ : R₁₂ (ι (.ts 2)) = [] := by
    rw [hs₁₂ _ hc5, hs₁₁ _ (he3 2), hs₁₀ _ hc5, hs₉ _ (he3 1), hs₈ _ hc5, hs₇ _ (he3 0),
      hs₆ _ hc5, hs₅ _ hc5, hR₄S _ he0 he1' he2']
    exact hrest _
  have hf3₁₂ : R₁₂ (ι (fld5 3)) = [] := by
    rw [hs₁₂ _ (hc3 3).symm, hs₁₁ _ (hf 3 2 (by decide)), hs₁₀ _ (hc3 3).symm,
      hs₉ _ (hf 3 1 (by decide)), hs₈ _ (hc3 3).symm, hs₇ _ (hf 3 0 (by decide)),
      hs₆ _ (hc3 3).symm, hs₅ _ (hc3 3).symm,
      hR₄S _ (hne (by simp [fld5])) (hne (by simp [fld5])) (hne (by simp [fld5]))]
    exact hrest _
  have hf4₁₂ : R₁₂ (ι (fld5 4)) = [] := by
    rw [hs₁₂ _ (hc3 4).symm, hs₁₁ _ (hf 4 2 (by decide)), hs₁₀ _ (hc3 4).symm,
      hs₉ _ (hf 4 1 (by decide)), hs₈ _ (hc3 4).symm, hs₇ _ (hf 4 0 (by decide)),
      hs₆ _ (hc3 4).symm, hs₅ _ (hc3 4).symm,
      hR₄S _ (hne (by simp [fld5])) (hne (by simp [fld5])) (hne (by simp [fld5]))]
    exact hrest _
  -- 13. field 3
  obtain ⟨v₁₃, hu₁₃, he₁₃⟩ := zeroBits_exec body (len := par .L) (z := ι (fld5 3)) (t := ι (.ts 1))
    (by f1simp) (by f1simp) (hd3 3).symm v₁₂ { S with R := R₁₂ } hts1₁₂
  dsimp only at he₁₃
  rw [hpar₁₂, hLr, hf3₁₂, List.append_nil] at he₁₃
  set R₁₃ := Function.update R₁₂ (ι (fld5 3)) (binSyms L 0) with hR₁₃
  have hs₁₃ : ∀ t, t ≠ ι (fld5 3) → R₁₃ t = R₁₂ t := fun t h => by
    rw [hR₁₃, Function.update_of_ne h]
  -- 14. `ts 0 := n`
  obtain ⟨v₁₄, hu₁₄, he₁₄⟩ := ucopy_exec body (a := par .n) (b := ι (.ts 0)) (t := ι (.ts 1))
    (by f1simp) (by f1simp) hc4.symm v₁₃ { S with R := R₁₃ }
    (by show R₁₃ _ = []; rw [hs₁₃ _ (hd3 3)]; exact hts1₁₂)
  dsimp only at he₁₄
  rw [hs₁₃ _ ((hpU _).2.2.2.1 3), hpar₁₂, hn, hs₁₃ _ (hc3 3), hR₁₂0, List.append_nil] at he₁₄
  set R₁₄ := Function.update R₁₃ (ι (.ts 0)) (List.replicate n tick) with hR₁₄
  have hs₁₄ : ∀ t, t ≠ ι (.ts 0) → R₁₄ t = R₁₃ t := fun t h => by
    rw [hR₁₄, Function.update_of_ne h]
  -- 15. `ts 0 -= a₀`
  obtain ⟨v₁₅, hu₁₅, he₁₅⟩ := usub_exec body (a := par .a₀) (b := ι (.ts 0)) (t := ι (.ts 1))
    (by f1simp) (by f1simp) hc4.symm v₁₄ { S with R := R₁₄ }
    (by show R₁₄ _ = []; rw [hs₁₄ _ hc4, hs₁₃ _ (hd3 3)]; exact hts1₁₂)
  dsimp only at he₁₅
  rw [hs₁₄ _ (hpU _).2.2.2.2.1, hs₁₃ _ ((hpU _).2.2.2.1 3), hpar₁₂, ha₀, hR₁₄, Function.update_self,
    List.drop_replicate] at he₁₅
  set R₁₅ := Function.update R₁₄ (ι (.ts 0)) (List.replicate (n - a₀) tick) with hR₁₅
  have hs₁₅ : ∀ t, t ≠ ι (.ts 0) → R₁₅ t = R₁₄ t := fun t h => by
    rw [hR₁₅, Function.update_of_ne h]
  have hR₁₅0 : R₁₅ (ι (.ts 0)) = List.replicate (n - a₀) tick := by
    rw [hR₁₅, Function.update_self]
  -- 16. `ts 2 := (max x y + 1) L`
  obtain ⟨v₁₆, hu₁₆, he₁₆⟩ := umul_exec body (max x y + 1) (a := par .L) (b := ι (.ts 2))
    (t := ι (.ts 1)) (by f1simp) (by f1simp) hd5 v₁₅ { S with R := R₁₅ }
    (by show R₁₅ _ = []; rw [hs₁₅ _ hc4, hs₁₄ _ hc4, hs₁₃ _ (hd3 3)]; exact hts1₁₂)
  dsimp only at he₁₆
  rw [hs₁₅ _ (hpU _).2.2.2.2.1, hs₁₄ _ (hpU _).2.2.2.2.1, hs₁₃ _ ((hpU _).2.2.2.1 3), hpar₁₂, hLr,
    hs₁₅ _ hc5, hs₁₄ _ hc5, hs₁₃ _ (he3 3), hts2₁₂, List.append_nil] at he₁₆
  set R₁₆ := Function.update R₁₅ (ι (.ts 2)) (List.replicate ((max x y + 1) * L) tick) with hR₁₆
  have hs₁₆ : ∀ t, t ≠ ι (.ts 2) → R₁₆ t = R₁₅ t := fun t h => by
    rw [hR₁₆, Function.update_of_ne h]
  have hR₁₆2 : R₁₆ (ι (.ts 2)) = List.replicate ((max x y + 1) * L) tick := by
    rw [hR₁₆, Function.update_self]
  -- 17. `ts 0 -= ts 2`
  obtain ⟨v₁₇, hu₁₇, he₁₇⟩ := usub_exec body (a := ι (.ts 2)) (b := ι (.ts 0)) (t := ι (.ts 1))
    hc5 hd5 hc4.symm v₁₆ { S with R := R₁₆ }
    (by show R₁₆ _ = []; rw [hs₁₆ _ hd5.symm, hs₁₅ _ hc4, hs₁₄ _ hc4, hs₁₃ _ (hd3 3)]
        exact hts1₁₂)
  dsimp only at he₁₇
  rw [hR₁₆2, hs₁₆ _ hc5.symm, hR₁₅0, List.length_replicate, List.drop_replicate] at he₁₇
  set R₁₇ := Function.update R₁₆ (ι (.ts 0))
    (List.replicate (n - a₀ - (max x y + 1) * L) tick) with hR₁₇
  have hs₁₇ : ∀ t, t ≠ ι (.ts 0) → R₁₇ t = R₁₆ t := fun t h => by
    rw [hR₁₇, Function.update_of_ne h]
  have hR₁₇0 : R₁₇ (ι (.ts 0)) = List.replicate (n - a₀ - (max x y + 1) * L) tick := by
    rw [hR₁₇, Function.update_self]
  -- 18. clear `ts 2`
  obtain ⟨v₁₈, hu₁₈, he₁₈⟩ := uclear_exec body (ι (.ts 2)) v₁₇ { S with R := R₁₇ }
  dsimp only at he₁₈
  rw [hs₁₇ _ hc5, hR₁₆2] at he₁₈
  set R₁₈ := Function.update R₁₇ (ι (.ts 2)) [] with hR₁₈
  have hs₁₈ : ∀ t, t ≠ ι (.ts 2) → R₁₈ t = R₁₇ t := fun t h => by
    rw [hR₁₈, Function.update_of_ne h]
  -- 19. field 4
  obtain ⟨v₁₉, hu₁₉, he₁₉⟩ := hfld R₁₈ v₁₈ 4 (n - a₀ - (max x y + 1) * L)
    (by rw [hs₁₈ _ hc5.symm, hR₁₇0, List.length_replicate])
    (by rw [hs₁₈ _ hd5.symm, hs₁₇ _ hc4, hs₁₆ _ hd5.symm, hs₁₅ _ hc4, hs₁₄ _ hc4, hs₁₃ _ (hd3 3)]
        exact hts1₁₂)
    (by rw [hs₁₈ _ (he3 4).symm, hs₁₇ _ (hc3 4).symm, hs₁₆ _ (he3 4).symm, hs₁₅ _ (hc3 4).symm,
          hs₁₄ _ (hc3 4).symm, hs₁₃ _ (hf 4 3 (by decide))]
        exact hf4₁₂)
  set R₁₉ := Function.update R₁₈ (ι (fld5 4)) (binSyms (n - a₀ - (max x y + 1) * L) 0) with hR₁₉
  have hs₁₉ : ∀ t, t ≠ ι (fld5 4) → R₁₉ t = R₁₈ t := fun t h => by
    rw [hR₁₉, Function.update_of_ne h]
  -- 20. clear `ts 0`
  obtain ⟨v₂₀, hu₂₀, he₂₀⟩ := uclear_exec body (ι (.ts 0)) v₁₉ { S with R := R₁₉ }
  dsimp only at he₂₀
  rw [hs₁₉ _ (hc3 4), hs₁₈ _ hc5.symm, hR₁₇0] at he₂₀
  set R₂₀ := Function.update R₁₉ (ι (.ts 0)) [] with hR₂₀
  have hs₂₀ : ∀ t, t ≠ ι (.ts 0) → R₂₀ t = R₁₉ t := fun t h => by
    rw [hR₂₀, Function.update_of_ne h]
  -- the frame from step 5 on
  have hs₅₂₀ : ∀ t, t ≠ ι (.ts 0) → t ≠ ι (.ts 2) → (∀ g : Fin 5, t ≠ ι (fld5 g)) →
      R₂₀ t = R₄ t := fun t h0 h2 hg => by
    rw [hs₂₀ _ h0, hs₁₉ _ (hg 4), hs₁₈ _ h2, hs₁₇ _ h0, hs₁₆ _ h2, hs₁₅ _ h0, hs₁₄ _ h0,
      hs₁₃ _ (hg 3), hs₁₂ _ h0, hs₁₁ _ (hg 2), hs₁₀ _ h0, hs₉ _ (hg 1), hs₈ _ h0, hs₇ _ (hg 0),
      hs₆ _ h0, hs₅ _ h0]
  refine ⟨v₂₀, R₂₀, _, by rw [hu₂₀, hu₁₉, hu₁₈, hu₁₇, hu₁₆, hu₁₅, hu₁₄, hu₁₃, hu₁₂, hu₁₁, hu₁₀,
    hu₉, hu₈, hu₇, hu₆, hu₅, hu₄, hu₃, hu₂, hu₁], ?_,
    Exec.seq (Exec.seq (Exec.seq (Exec.seq (Exec.seq (Exec.seq (Exec.seq (Exec.seq (Exec.seq
      (Exec.seq (Exec.seq (Exec.seq (Exec.seq (Exec.seq (Exec.seq (Exec.seq (Exec.seq (Exec.seq
      (Exec.seq he₁ he₂) he₃) he₄) he₅) he₆) he₇) he₈) he₉) he₁₀) he₁₁) he₁₂) he₁₃) he₁₄) he₁₅)
      he₁₆) he₁₇) he₁₈) he₁₉) he₂₀, ?_, ?_, ?_⟩
  · -- the step bound
    simp only [List.length_replicate]
    unfold fix1SetupCost
    omega
  · refine ⟨?_, ?_, ?_, fun g => ?_⟩
    · rw [hs₅₂₀ _ hc0.symm he0.symm hf5, hR₄, Function.update_of_ne (hne (by simp)),
        hR₃b, List.length_replicate]
    · rw [hs₅₂₀ _ hc1.symm he1'.symm hf5', hR₄,
        Function.update_of_ne (hne (by simp)), hR₃c, List.length_replicate]
    · rw [hs₅₂₀ _ hc2.symm he2'.symm hf5'', hR₄, Function.update_self]
    · fin_cases g
      · show R₂₀ (ι (fld5 0)) = _
        rw [hs₂₀ _ (hc3 0).symm, hs₁₉ _ (hf 0 4 (by decide)), hs₁₈ _ (he3 0).symm,
          hs₁₇ _ (hc3 0).symm, hs₁₆ _ (he3 0).symm, hs₁₅ _ (hc3 0).symm, hs₁₄ _ (hc3 0).symm,
          hs₁₃ _ (hf 0 3 (by decide)), hs₁₂ _ (hc3 0).symm, hs₁₁ _ (hf 0 2 (by decide)),
          hs₁₀ _ (hc3 0).symm, hs₉ _ (hf 0 1 (by decide)), hs₈ _ (hc3 0).symm, hR₇,
          Function.update_self]
        show _ = binSyms (a₀ + min x y * L) 0
        rw [Nat.add_comm (min x y * L) a₀]
      · show R₂₀ (ι (fld5 1)) = _
        rw [hs₂₀ _ (hc3 1).symm, hs₁₉ _ (hf 1 4 (by decide)), hs₁₈ _ (he3 1).symm,
          hs₁₇ _ (hc3 1).symm, hs₁₆ _ (he3 1).symm, hs₁₅ _ (hc3 1).symm, hs₁₄ _ (hc3 1).symm,
          hs₁₃ _ (hf 1 3 (by decide)), hs₁₂ _ (hc3 1).symm, hs₁₁ _ (hf 1 2 (by decide)),
          hs₁₀ _ (hc3 1).symm, hR₉, Function.update_self]
        rfl
      · show R₂₀ (ι (fld5 2)) = _
        rw [hs₂₀ _ (hc3 2).symm, hs₁₉ _ (hf 2 4 (by decide)), hs₁₈ _ (he3 2).symm,
          hs₁₇ _ (hc3 2).symm, hs₁₆ _ (he3 2).symm, hs₁₅ _ (hc3 2).symm, hs₁₄ _ (hc3 2).symm,
          hs₁₃ _ (hf 2 3 (by decide)), hs₁₂ _ (hc3 2).symm, hR₁₁, Function.update_self]
        rfl
      · show R₂₀ (ι (fld5 3)) = _
        rw [hs₂₀ _ (hc3 3).symm, hs₁₉ _ (hf 3 4 (by decide)), hs₁₈ _ (he3 3).symm,
          hs₁₇ _ (hc3 3).symm, hs₁₆ _ (he3 3).symm, hs₁₅ _ (hc3 3).symm, hs₁₄ _ (hc3 3).symm,
          hR₁₃, Function.update_self]
        rfl
      · show R₂₀ (ι (fld5 4)) = _
        rw [hs₂₀ _ (hc3 4).symm, hR₁₉, Function.update_self]
        show _ = binSyms (n - (a₀ + (max x y + 1) * L)) 0
        rw [Nat.sub_sub]
  · refine ⟨by rw [hR₂₀, Function.update_self], ?_, ?_⟩
    · rw [hs₅₂₀ _ hc4 hd5.symm hd3, hR₄S _ hd0 hd1 hd2]; exact hrest _
    · rw [hs₂₀ _ hc5, hs₁₉ _ (he3 4), hR₁₈, Function.update_self]
  · intro t ht
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := ht
    rw [hs₅₂₀ _ h5 h7 h4, hR₄S _ h1 h2 h3]


/-- Clear the registers of the single-column slot XOR. -/
noncomputable def fix1Clean (ι : CXReg → Fin T) : Pr P T Q A U :=
  .seq (.seq (.seq (.seq (.seq (.seq (.seq (uclear (ι (.sx .ctrB))) (uclear (ι (.sx .cnt))))
    (uclear (ι .mtopC))) (uclear (ι (fld5 0)))) (uclear (ι (fld5 1)))) (uclear (ι (fld5 2))))
    (uclear (ι (fld5 3)))) (uclear (ι (fld5 4)))

/-- The single-column slot XOR of slot `x` into slot `y`: the setup, the fix pass and the
cleanup. -/
noncomputable def fix1Prog (ι : CXReg → Fin T) (par : CXPar → Fin T) (src st : Fin T)
    (x y : ℕ) : Pr P T Q A U :=
  .seq (.seq (fix1Setup ι par x y)
    (fixPassC (fX5 x y) (fY5 x y) src (ι (.sx (.fr 0))) (ι (.sx (.fr 1))) (ι (.sx (.fr 2)))
      (ι (.sx (.fr 3))) (ι (.sx (.fq 0))) (ι (.sx (.fq 1))) (ι (.sx (.fq 2))) (ι (.sx (.fq 3)))
      (ι (.sx .ctrB)) (ι (.sx .cnt)) (ι (.sx .ftmp)) (ι .mtopC) st (fun g => ι (fld5 g))
      (fun r => ι (.sx (.fus r)))))
    (fix1Clean ι)

/-- The step bound of `fix1Prog`. -/
def fix1Cost (a₀ ρ L R n rw : ℕ) : ℕ :=
  fix1SetupCost a₀ ρ L R n rw +
    (R * 2 ^ n * (18 * rw + 12 * L + 8 * n + 8 * 5 + 28) + 8 * n + 8 * 5 + 18) +
    (2 * rw + 2 * (R * 2 ^ n) + 2 * L + 2 * n + 16)

set_option maxHeartbeats 1000000 in
/-- **The single-column slot XOR.** -/
theorem fix1_exec (henv : CxEnv ι par src) (hst : ∀ z, ι z ≠ st) (hsrcst : src ≠ st)
    (hA : 4 ≤ A) {a₀ K ρ L R n r w : ℕ} (hρ : ρ < K) (hLK : L = K) (hR : 1 ≤ R)
    (hrw : 1 ≤ r * w) (hfit : a₀ + m * L ≤ n) {x y : Fin m} (hxy : x ≠ y)
    {e : Fin (m * 1) → Fin n} (he : ∀ i, (e i : ℕ) = a₀ + ρ + K * i)
    (Z : ZArr (Fin R × Fin r) n) (v : HS T Q A U) (S : Stacks T A)
    (hSsrc : S.R src = encZ A w Z)
    (hK : (S.R (par .K)).length = K) (hρr : (S.R (par .ρ)).length = ρ)
    (ha₀ : (S.R (par .a₀)).length = a₀) (hLr : (S.R (par .L)).length = L)
    (hrows : (S.R (par .rows)).length = R) (hn : (S.R (par .n)).length = n)
    (hrwr : (S.R (par .rw)).length = r * w) (hrest : ∀ z, S.R (ι z) = []) :
    ∃ (v' : HS T Q A U) (c : ℕ), v'.user = v.user ∧ c ≤ fix1Cost a₀ ρ L R n (r * w) ∧
      Exec body (fix1Prog ι par src st x y) (mk v S) c
        (mk v' { S with
          R := Function.update S.R src (encZ A w (pullM e (sxXorCol x y) Z)) }) := by
  have hxy' : (x : ℕ) ≠ y := fun h => hxy (Fin.ext h)
  obtain ⟨hl, hlB, hl8⟩ := sx_recSyms_facts hA (w := w) Z
  set l := (IntegerMultBounds.MathlibTM2.Layer.recList w Z).map
    (IntegerMultBounds.MathlibTM2.Layer.recSyms A w) with hldef
  have hne : ∀ {a b : CXReg}, a ≠ b → ι a ≠ ι b := fun h => henv.hι.ne h
  -- the setup
  obtain ⟨v₁, R₁, c₁, hu₁, hc₁, he₁, hregs, ⟨hts0, hts1, hts2⟩, hfr⟩ := fix1Setup_exec body henv x y
    hxy' x.isLt y.isLt hfit v S hrest hK hρr ha₀ hLr hrows hn hrwr
  obtain ⟨hctr, hcnt, htm, hcf⟩ := hregs
  have hsx : ∀ r : SXReg, r ≠ .ctrB → r ≠ .cnt → R₁ (ι (.sx r)) = [] := fun r h1 h2 => by
    rw [hfr _ ⟨hne (by simp [h1]), hne (by simp [h2]), hne (by simp), fun g => hne (by simp [fld5]),
      hne (by simp), hne (by simp), hne (by simp)⟩]
    exact hrest _
  have hsrc₁ : R₁ src = l.flatten := by
    rw [hfr _ ⟨(henv.hsrc _).symm, (henv.hsrc _).symm, (henv.hsrc _).symm,
      fun g => (henv.hsrc _).symm, (henv.hsrc _).symm, (henv.hsrc _).symm, (henv.hsrc _).symm⟩,
      hSsrc, sx_encZ_eq_flatten]
  -- the fix pass
  obtain ⟨v₂, c₂, hu₂, hc₂, he₂⟩ := fixPassC_exec body (len5 a₀ L n x y) (fX5_ne_fY5 x y)
    (by rw [len5_fX5, len5_fY5]) (R := R) (S := n) (hSY5 hxy' x.isLt y.isLt hfit)
    (K := K) (ρ := ρ) (n := 0) (by rw [len5_fY5]; omega)
    (src := src) (r0 := ι (.sx (.fr 0))) (r1 := ι (.sx (.fr 1))) (r2 := ι (.sx (.fr 2)))
    (r3 := ι (.sx (.fr 3))) (q0 := ι (.sx (.fq 0))) (q1 := ι (.sx (.fq 1))) (q2 := ι (.sx (.fq 2)))
    (q3 := ι (.sx (.fq 3))) (ctrB := ι (.sx .ctrB)) (cnt := ι (.sx .cnt)) (tmp := ι (.sx .ftmp))
    (tm := ι .mtopC) (st := st) (cf := fun g => ι (fld5 g)) (us := fun r => ι (.sx (.fus r)))
    (by
      refine nodup_append_ofFn (nodup_append_ofFn ?_ ?_ ?_) (fun a b h => by
        have := henv.hι h; simpa [fld5, Fin.ext_iff] using this) ?_
      · simp [henv.hι.eq_iff, henv.hsrc, fun x => (henv.hsrc x).symm, Fin.ext_iff]
      · intro a b h; have := henv.hι h; simpa [Fin.ext_iff] using this
      · intro a ha r
        simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at ha
        rcases ha with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | rfl <;>
          simp [henv.hι.eq_iff, henv.hsrc, fun x => (henv.hsrc x).symm, Fin.ext_iff, fld5]
      · intro a ha j
        simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_ofFn] at ha
        rcases ha with ((rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | rfl)
          | ⟨r, rfl⟩ <;> simp [henv.hι.eq_iff, henv.hsrc, fun x => (henv.hsrc x).symm, Fin.ext_iff, fld5])
    (by
      simp only [List.mem_append, List.mem_singleton, List.mem_ofFn, not_or, not_exists]
      exact ⟨⟨(hst _).symm, fun r e => hst _ e⟩, fun j e => hst _ e⟩)
    hrw l hl hlB v₁ { S with R := R₁ } hsrc₁
    (hsx _ (by decide) (by decide)) (hsx _ (by decide) (by decide)) (hsx _ (by decide) (by decide))
    (hsx _ (by decide) (by decide)) (hsx _ (by decide) (by decide)) (hsx _ (by decide) (by decide))
    (hsx _ (by decide) (by decide)) (hsx _ (by decide) (by decide)) hctr hcnt
    (hsx _ (by decide) (by decide)) (by simp only [len5_fY5, Nat.zero_mul, Nat.add_zero]; exact htm)
    (fun r => hsx _ (by simp) (by simp)) hcf
  dsimp only at he₂
  rw [moveRecs_topFix_zero _ _ _ _ ρ (by omega), hldef,
    moveRecs_fullXorPermC (k := 1) (len5 a₀ L n x y) (fX5_ne_fY5 x y) hρ (by rw [hLK]; ring)
      le_rfl (foff5_fX5 hxy') (len5_fX5 _ _ _ _ _) (foff5_fY5 hxy') (len5_fY5 _ _ _ _ _)
      (by rw [len5_fX5, len5_fY5]) (hSY5 hxy' x.isLt y.isLt hfit) he Z] at he₂
  set R₂ := Function.update R₁ src (encZ A w (pullM e (sxXorCol x y) Z)) with hR₂
  have hR₂f : ∀ t, t ≠ src → R₂ t = R₁ t := fun t h => by rw [hR₂, Function.update_of_ne h]
  -- the cleanup
  obtain ⟨v₃, hu₃, he₃⟩ := uclear_exec body (ι (.sx .ctrB)) v₂ { S with R := R₂ }
  dsimp only at he₃
  set R₃ := Function.update R₂ (ι (.sx .ctrB)) [] with hR₃
  obtain ⟨v₄, hu₄, he₄⟩ := uclear_exec body (ι (.sx .cnt)) v₃ { S with R := R₃ }
  dsimp only at he₄
  set R₄ := Function.update R₃ (ι (.sx .cnt)) [] with hR₄
  obtain ⟨v₅, hu₅, he₅⟩ := uclear_exec body (ι .mtopC) v₄ { S with R := R₄ }
  dsimp only at he₅
  set R₅ := Function.update R₄ (ι .mtopC) [] with hR₅
  obtain ⟨v₆, hu₆, he₆⟩ := uclear_exec body (ι (fld5 0)) v₅ { S with R := R₅ }
  dsimp only at he₆
  set R₆ := Function.update R₅ (ι (fld5 0)) [] with hR₆
  obtain ⟨v₇, hu₇, he₇⟩ := uclear_exec body (ι (fld5 1)) v₆ { S with R := R₆ }
  dsimp only at he₇
  set R₇ := Function.update R₆ (ι (fld5 1)) [] with hR₇
  obtain ⟨v₈, hu₈, he₈⟩ := uclear_exec body (ι (fld5 2)) v₇ { S with R := R₇ }
  dsimp only at he₈
  set R₈ := Function.update R₇ (ι (fld5 2)) [] with hR₈
  obtain ⟨v₉, hu₉, he₉⟩ := uclear_exec body (ι (fld5 3)) v₈ { S with R := R₈ }
  dsimp only at he₉
  set R₉ := Function.update R₈ (ι (fld5 3)) [] with hR₉
  obtain ⟨v₁₀, hu₁₀, he₁₀⟩ := uclear_exec body (ι (fld5 4)) v₉ { S with R := R₉ }
  dsimp only at he₁₀
  -- the lengths cleared
  have hf : ∀ g g' : Fin 5, g ≠ g' → ι (fld5 g) ≠ ι (fld5 g') := fun g g' h =>
    hne (by simp [fld5, Fin.ext_iff]; omega)
  have hsrcne : ∀ z : CXReg, src ≠ ι z := fun z => (henv.hsrc z).symm
  have l3 : (R₂ (ι (.sx .ctrB))).length = r * w := by rw [hR₂f _ (henv.hsrc _)]; exact hctr
  have l4 : (R₃ (ι (.sx .cnt))).length = R * 2 ^ n := by
    rw [hR₃, Function.update_of_ne (hne (by simp)), hR₂f _ (henv.hsrc _)]; exact hcnt
  have l5 : (R₄ (ι .mtopC)).length = L := by
    rw [hR₄, Function.update_of_ne (hne (by simp)), hR₃, Function.update_of_ne (hne (by simp)),
      hR₂f _ (henv.hsrc _), htm, length_binSyms]
  have l6 : (R₅ (ι (fld5 0))).length = len5 a₀ L n x y 0 := by
    rw [hR₅, Function.update_of_ne (hne (by simp [fld5])), hR₄,
      Function.update_of_ne (hne (by simp [fld5])), hR₃, Function.update_of_ne (hne (by simp [fld5])),
      hR₂f _ (henv.hsrc _), hcf, length_binSyms]
  have l7 : (R₆ (ι (fld5 1))).length = len5 a₀ L n x y 1 := by
    rw [hR₆, Function.update_of_ne (hf 1 0 (by decide)), hR₅,
      Function.update_of_ne (hne (by simp [fld5])), hR₄,
      Function.update_of_ne (hne (by simp [fld5])), hR₃, Function.update_of_ne (hne (by simp [fld5])),
      hR₂f _ (henv.hsrc _), hcf, length_binSyms]
  have l8 : (R₇ (ι (fld5 2))).length = len5 a₀ L n x y 2 := by
    rw [hR₇, Function.update_of_ne (hf 2 1 (by decide)), hR₆,
      Function.update_of_ne (hf 2 0 (by decide)), hR₅,
      Function.update_of_ne (hne (by simp [fld5])), hR₄,
      Function.update_of_ne (hne (by simp [fld5])), hR₃, Function.update_of_ne (hne (by simp [fld5])),
      hR₂f _ (henv.hsrc _), hcf, length_binSyms]
  have l9 : (R₈ (ι (fld5 3))).length = len5 a₀ L n x y 3 := by
    rw [hR₈, Function.update_of_ne (hf 3 2 (by decide)), hR₇,
      Function.update_of_ne (hf 3 1 (by decide)), hR₆,
      Function.update_of_ne (hf 3 0 (by decide)), hR₅,
      Function.update_of_ne (hne (by simp [fld5])), hR₄,
      Function.update_of_ne (hne (by simp [fld5])), hR₃, Function.update_of_ne (hne (by simp [fld5])),
      hR₂f _ (henv.hsrc _), hcf, length_binSyms]
  have l10 : (R₉ (ι (fld5 4))).length = len5 a₀ L n x y 4 := by
    rw [hR₉, Function.update_of_ne (hf 4 3 (by decide)), hR₈,
      Function.update_of_ne (hf 4 2 (by decide)), hR₇,
      Function.update_of_ne (hf 4 1 (by decide)), hR₆,
      Function.update_of_ne (hf 4 0 (by decide)), hR₅,
      Function.update_of_ne (hne (by simp [fld5])), hR₄,
      Function.update_of_ne (hne (by simp [fld5])), hR₃, Function.update_of_ne (hne (by simp [fld5])),
      hR₂f _ (henv.hsrc _), hcf, length_binSyms]
  have hsum := len5_sum hxy' y.isLt x.isLt hfit
  have hsum5 : len5 a₀ L n x y 0 + len5 a₀ L n x y 1 + len5 a₀ L n x y 2 + len5 a₀ L n x y 3 +
      len5 a₀ L n x y 4 = n := by rw [Fin.sum_univ_five] at hsum; exact hsum
  -- the final register file
  have hfinal : Function.update R₉ (ι (fld5 4)) [] =
      Function.update S.R src (encZ A w (pullM e (sxXorCol x y) Z)) := by
    funext t
    by_cases h0 : t = src
    · subst h0
      rw [Function.update_of_ne (hsrcne _), hR₉, Function.update_of_ne (hsrcne _), hR₈,
        Function.update_of_ne (hsrcne _), hR₇, Function.update_of_ne (hsrcne _), hR₆,
        Function.update_of_ne (hsrcne _), hR₅, Function.update_of_ne (hsrcne _), hR₄,
        Function.update_of_ne (hsrcne _), hR₃, Function.update_of_ne (hsrcne _), hR₂,
        Function.update_self, Function.update_self]
    rw [Function.update_of_ne h0]
    by_cases h1 : t = ι (.sx .ctrB)
    · subst h1
      rw [Function.update_of_ne (hne (by simp [fld5])), hR₉, Function.update_of_ne (hne (by simp [fld5])),
        hR₈, Function.update_of_ne (hne (by simp [fld5])), hR₇,
        Function.update_of_ne (hne (by simp [fld5])), hR₆, Function.update_of_ne (hne (by simp [fld5])),
        hR₅, Function.update_of_ne (hne (by simp)), hR₄, Function.update_of_ne (hne (by simp)), hR₃,
        Function.update_self, hrest]
    by_cases h2 : t = ι (.sx .cnt)
    · subst h2
      rw [Function.update_of_ne (hne (by simp [fld5])), hR₉, Function.update_of_ne (hne (by simp [fld5])),
        hR₈, Function.update_of_ne (hne (by simp [fld5])), hR₇,
        Function.update_of_ne (hne (by simp [fld5])), hR₆, Function.update_of_ne (hne (by simp [fld5])),
        hR₅, Function.update_of_ne (hne (by simp)), hR₄, Function.update_self, hrest]
    by_cases h3 : t = ι .mtopC
    · subst h3
      rw [Function.update_of_ne (hne (by simp [fld5])), hR₉, Function.update_of_ne (hne (by simp [fld5])),
        hR₈, Function.update_of_ne (hne (by simp [fld5])), hR₇,
        Function.update_of_ne (hne (by simp [fld5])), hR₆, Function.update_of_ne (hne (by simp [fld5])),
        hR₅, Function.update_self, hrest]
    by_cases h4 : t = ι (fld5 0)
    · subst h4
      rw [Function.update_of_ne (hf 0 4 (by decide)), hR₉, Function.update_of_ne (hf 0 3 (by decide)),
        hR₈, Function.update_of_ne (hf 0 2 (by decide)), hR₇,
        Function.update_of_ne (hf 0 1 (by decide)), hR₆, Function.update_self, hrest]
    by_cases h5 : t = ι (fld5 1)
    · subst h5
      rw [Function.update_of_ne (hf 1 4 (by decide)), hR₉, Function.update_of_ne (hf 1 3 (by decide)),
        hR₈, Function.update_of_ne (hf 1 2 (by decide)), hR₇, Function.update_self, hrest]
    by_cases h6 : t = ι (fld5 2)
    · subst h6
      rw [Function.update_of_ne (hf 2 4 (by decide)), hR₉, Function.update_of_ne (hf 2 3 (by decide)),
        hR₈, Function.update_self, hrest]
    by_cases h7 : t = ι (fld5 3)
    · subst h7
      rw [Function.update_of_ne (hf 3 4 (by decide)), hR₉, Function.update_self, hrest]
    by_cases h8 : t = ι (fld5 4)
    · subst h8
      rw [Function.update_self, hrest]
    rw [Function.update_of_ne h8, hR₉, Function.update_of_ne h7, hR₈, Function.update_of_ne h6, hR₇,
      Function.update_of_ne h5, hR₆, Function.update_of_ne h4, hR₅, Function.update_of_ne h3, hR₄,
      Function.update_of_ne h2, hR₃, Function.update_of_ne h1, hR₂, Function.update_of_ne h0]
    by_cases hts : t = ι (.ts 0) ∨ t = ι (.ts 1) ∨ t = ι (.ts 2)
    · rcases hts with rfl | rfl | rfl
      · rw [hts0, hrest]
      · rw [hts1, hrest]
      · rw [hts2, hrest]
    · push_neg at hts
      exact hfr t ⟨h1, h2, h3, fun g => by
        intro h; fin_cases g <;> simp_all, hts.1, hts.2.1, hts.2.2⟩
  refine ⟨v₁₀, _, by rw [hu₁₀, hu₉, hu₈, hu₇, hu₆, hu₅, hu₄, hu₃, hu₂, hu₁], ?_,
    Exec.cast (Exec.seq (Exec.seq he₁ he₂) (Exec.seq (Exec.seq (Exec.seq (Exec.seq (Exec.seq
      (Exec.seq (Exec.seq he₃ he₄) he₅) he₆) he₇) he₈) he₉) he₁₀)) rfl (by rw [hfinal])⟩
  -- the step bound
  rw [l3, l4, l5, l6, l7, l8, l9, l10]
  rw [len5_fY5, hsum] at hc₂
  unfold fix1Cost
  omega

/-- **The single-column basis change** along `v` at `j`: `fix1Prog` for every
`j' ∈ basisTargets v j`. -/
noncomputable def basisProg1 (ι : CXReg → Fin T) (par : CXPar → Fin T) (src st : Fin T)
    (v : BinaryWalsh.Address m) (j : Fin m) : Pr P T Q A U :=
  Prog.seqList ((basisTargets v j).map fun (j' : Fin m) => fix1Prog ι par src st j j')

/-- The step bound of `basisProg1`. -/
def basisCost1 (a₀ ρ L R n rw : ℕ) : ℕ := m * fix1Cost a₀ ρ L R n rw + 1

lemma length_basisTargets_le (v : BinaryWalsh.Address m) (j : Fin m) :
    (basisTargets v j).length ≤ m := by
  unfold basisTargets
  exact (List.length_filter_le _ _).trans (by simp)

/-- The single-column slot XORs of `j` into the slots `l`, from any array. -/
theorem basisList1_exec (henv : CxEnv ι par src) (hst : ∀ z, ι z ≠ st) (hsrcst : src ≠ st)
    (hA : 4 ≤ A) {a₀ K ρ L R n r w : ℕ} (hρ : ρ < K) (hLK : L = K) (hR : 1 ≤ R)
    (hrw : 1 ≤ r * w) (hfit : a₀ + m * L ≤ n) {e : Fin (m * 1) → Fin n}
    (he : ∀ i, (e i : ℕ) = a₀ + ρ + K * i) (j : Fin m) :
    ∀ (l : List (Fin m)), (∀ j' ∈ l, j' ≠ j) →
    ∀ (Z : ZArr (Fin R × Fin r) n) (v : HS T Q A U) (S : Stacks T A),
      S.R src = encZ A w Z →
      (S.R (par .K)).length = K → (S.R (par .ρ)).length = ρ → (S.R (par .a₀)).length = a₀ →
      (S.R (par .L)).length = L → (S.R (par .rows)).length = R → (S.R (par .n)).length = n →
      (S.R (par .rw)).length = r * w → (∀ z, S.R (ι z) = []) →
      ∃ (v' : HS T Q A U) (c : ℕ), v'.user = v.user ∧
        c ≤ l.length * fix1Cost a₀ ρ L R n (r * w) + 1 ∧
        Exec body (Prog.seqList (l.map fun (j' : Fin m) => fix1Prog ι par src st j j')) (mk v S) c
          (mk v' { S with
            R := Function.update S.R src (encZ A w (pullM e (basisFold j l) Z)) })
  | [], _, Z, v, S, hSsrc, _, _, _, _, _, _, _, _ => by
      refine ⟨v, 1, rfl, by simp, Exec.cast (Exec.act (body := body) .done (mk v S)) rfl ?_⟩
      have hid : basisFold j [] = id := rfl
      rw [run_done, hid, basis_pullM_id, ← hSsrc, Function.update_eq_self]
  | j' :: l, hl, Z, v, S, hSsrc, hK, hρr, ha₀, hLr, hrows, hn, hrwr, hrest => by
      have hj' : j' ≠ j := hl j' List.mem_cons_self
      obtain ⟨v₁, c₁, hu₁, hc₁, he₁⟩ := fix1_exec body henv hst hsrcst hA hρ hLK hR hrw hfit
        (x := j) (y := j') (Ne.symm hj') he Z v S hSsrc hK hρr ha₀ hLr hrows hn hrwr hrest
      set Z₁ := pullM e (sxXorCol j j') Z with hZ₁
      obtain ⟨v₂, c₂, hu₂, hc₂, he₂⟩ := basisList1_exec henv hst hsrcst hA hρ hLK hR hrw hfit he j
        l (fun j'' h => hl j'' (List.mem_cons_of_mem _ h)) Z₁ v₁
        { S with R := Function.update S.R src (encZ A w Z₁) } (by simp)
        (by simp only [Function.update_of_ne (henv.hsrcp _)]; exact hK)
        (by simp only [Function.update_of_ne (henv.hsrcp _)]; exact hρr)
        (by simp only [Function.update_of_ne (henv.hsrcp _)]; exact ha₀)
        (by simp only [Function.update_of_ne (henv.hsrcp _)]; exact hLr)
        (by simp only [Function.update_of_ne (henv.hsrcp _)]; exact hrows)
        (by simp only [Function.update_of_ne (henv.hsrcp _)]; exact hn)
        (by simp only [Function.update_of_ne (henv.hsrcp _)]; exact hrwr)
        (fun z => by simp only [Function.update_of_ne (henv.hsrc z)]; exact hrest z)
      have hfold : pullM e (basisFold j l) Z₁ = pullM e (basisFold j (j' :: l)) Z := by
        rw [hZ₁, basis_pullM_pullM (basis_e_inj (by omega) he)]
        rfl
      refine ⟨v₂, c₁ + c₂, hu₂.trans hu₁, ?_, ?_⟩
      · simp only [List.length_cons]
        have : (l.length + 1) * fix1Cost a₀ ρ L R n (r * w) =
            fix1Cost a₀ ρ L R n (r * w) + l.length * fix1Cost a₀ ρ L R n (r * w) := by ring
        omega
      · refine Exec.cast (Exec.seq he₁ he₂) rfl ?_
        rw [Function.update_idem, hfold]

/-- **The single-column basis change.** -/
theorem basisProg1_exec (henv : CxEnv ι par src) (hst : ∀ z, ι z ≠ st) (hsrcst : src ≠ st)
    (hA : 4 ≤ A) {a₀ K ρ L R n r w : ℕ} (hρ : ρ < K) (hLK : L = K) (hR : 1 ≤ R)
    (hrw : 1 ≤ r * w) (hfit : a₀ + m * L ≤ n) {e : Fin (m * 1) → Fin n}
    (he : ∀ i, (e i : ℕ) = a₀ + ρ + K * i) (vv : BinaryWalsh.Address m) (j : Fin m)
    (hvj : vv j = 1) (Z : ZArr (Fin R × Fin r) n) (v : HS T Q A U) (S : Stacks T A)
    (hSsrc : S.R src = encZ A w Z)
    (hK : (S.R (par .K)).length = K) (hρr : (S.R (par .ρ)).length = ρ)
    (ha₀ : (S.R (par .a₀)).length = a₀) (hLr : (S.R (par .L)).length = L)
    (hrows : (S.R (par .rows)).length = R) (hn : (S.R (par .n)).length = n)
    (hrwr : (S.R (par .rw)).length = r * w) (hrest : ∀ z, S.R (ι z) = []) :
    ∃ (v' : HS T Q A U) (c : ℕ), v'.user = v.user ∧ c ≤ basisCost1 a₀ ρ L R n (r * w) ∧
      Exec body (basisProg1 ι par src st vv j) (mk v S) c
        (mk v' { S with
          R := Function.update S.R src (encZ A w (pullM e (basisMap vv j) Z)) }) := by
  obtain ⟨v', c, hu, hc, hex⟩ := basisList1_exec body henv hst hsrcst hA hρ hLK hR hrw hfit he j
    (basisTargets vv j) (fun j' h => (mem_basisTargets.1 h).2) Z v S hSsrc hK hρr ha₀ hLr hrows
    hn hrwr hrest
  rw [basisFold_eq vv j hvj] at hex
  refine ⟨v', c, hu, ?_, hex⟩
  unfold basisCost1
  have := Nat.mul_le_mul_right (fix1Cost a₀ ρ L R n (r * w)) (length_basisTargets_le vv j)
  omega

end Fix1

/-! ### The basis-change registers of the layer machine -/

/-- The parameter and layout registers of the compact slot XOR held by the layer machine: the
digit width `G` (a parameter of the run) and the per-node layout values `k`, `bB`, `pT`, `pU`
(empty at rest). -/
inductive CPar where
  | G | kk | bB | pT | pU
  deriving DecidableEq

instance : Fintype CPar :=
  Fintype.ofList [.G, .kk, .bB, .pT, .pU] (by intro x; cases x <;> simp)

instance : Fintype CXVal :=
  Fintype.ofList [.L, .nGa, .nGb, .ρa, .ρb, .ρc, .z1, .z2, .Ka, .Kb, .Ga, .Gb, .nn, .padKG,
    .padK, .padG] (by intro x; cases x <;> simp)

instance : Fintype BReg :=
  Fintype.ofList [.comp, .mD, .mG, .padR, .sT, .sU, .sY, .t₁, .t₂, .t₃, .t₄, .acc, .ct, .cu]
    (by intro x; cases x <;> simp)

noncomputable section
deriving instance Fintype for CXReg
end

/-- The basis-change registers of the layer machine: the registers of the compact machine and
the layout parameters. -/
abbrev CReg : Type := CXReg ⊕ CPar

/-- The rest state of the basis-change registers: all empty except `G`, which holds the digit
width. -/
def bcRestC {A : ℕ} (G : ℕ) : CReg → List (Fin (A + 4)) → Prop
  | .inl _, l => l = []
  | .inr .G, l => l.length = G
  | .inr _, l => l = []

end IntegerMultBounds.MathlibTM2.Node
