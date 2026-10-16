module

public import IntegerMultBounds.MathlibTM2.Node.SlotXor

/-!
# The basis change of a factor

A factor of the node along `v` (`v j = 1`) is realized on the slot `j` after the change of basis
`basisMap v j a = a + a j • (v + e_j)`, applied in every column of the active bits
(`IntegerMultBounds.MathlibTM2.Layer.pullM e (basisMap v j)`). In column `c`, the change adds the bit of slot `j` to the
bit of every slot `j' ≠ j` with `v j' = 1`: it is the composition of the slot XORs
`sxXorCol j j'` over these slots (`basisTargets v j`, in increasing order). The XORs read slot `j`
and write distinct slots, so they commute; `basisFold_apply` computes their composition
coordinatewise and `basisFold_eq` identifies it with `basisMap v j`.

`basisProg v j` runs `slotXorProg` for `x = j`, `y = j'`, with a third slot `basisZ j j'`
distinct from both, for every `j' ∈ basisTargets v j`.

**Main theorem** (`basisProg_exec`). Under the hypotheses of `slotXor_exec`, with the parameter
registers also outside `src`, the program takes `src` from `encZ A w Z` to
`encZ A w (pullM e (basisMap v j) Z)`, every other register and `user` as before, within the sum
over `j' ∈ basisTargets v j` of the bounds of `slotXor_exec` for the slots `(j, j', basisZ j j')`
(`basisCost`, in closed form `basisCost_le`), plus one step.
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Node

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Layer.PackedXor
open IntegerMultBounds.Networks (BinaryWalsh.Address)
open IntegerMultBounds.MathlibTM2.Layer (ZArr encZ pullM colBits merge ofCols toCols bitIdx basisMap m)

set_option linter.unusedSimpArgs false

/-! ### The slot XORs of a basis change -/

section Fold

/-- A slot distinct from `j` and `j'`. -/
def basisZ (j j' : Fin m) : Fin m :=
  if (0 : Fin m) ≠ j ∧ (0 : Fin m) ≠ j' then 0
  else if (1 : Fin m) ≠ j ∧ (1 : Fin m) ≠ j' then 1 else 2

lemma basisZ_ne (j j' : Fin m) : basisZ j j' ≠ j ∧ basisZ j j' ≠ j' := by
  have e0 : ((0 : Fin m) : ℕ) = 0 := rfl
  have e1 : ((1 : Fin m) : ℕ) = 1 := rfl
  have e2 : ((2 : Fin m) : ℕ) = 2 := rfl
  unfold basisZ
  split_ifs with h0 h1
  · exact ⟨fun h => h0.1 h, fun h => h0.2 h⟩
  · exact ⟨fun h => h1.1 h, fun h => h1.2 h⟩
  · simp only [ne_eq, Fin.ext_iff, e0, e1, e2, not_and_or, not_not] at h0 h1 ⊢
    omega

/-- The slots written by the basis change along `v` at `j`: `v j' = 1`, `j' ≠ j`, increasing. -/
def basisTargets (v : BinaryWalsh.Address m) (j : Fin m) : List (Fin m) :=
  (List.finRange m).filter fun j' => decide (v j' = 1 ∧ j' ≠ j)

lemma mem_basisTargets {v : BinaryWalsh.Address m} {j j' : Fin m} :
    j' ∈ basisTargets v j ↔ v j' = 1 ∧ j' ≠ j := by
  simp [basisTargets]

lemma basisTargets_nodup (v : BinaryWalsh.Address m) (j : Fin m) :
    (basisTargets v j).Nodup :=
  (List.nodup_finRange m).filter _

/-- The composition of the slot XORs of `j` into the slots `l`, the head outermost. -/
def basisFold (j : Fin m) (l : List (Fin m)) (a : BinaryWalsh.Address m) :
    BinaryWalsh.Address m :=
  l.foldr (fun j' a => sxXorCol j j' a) a

lemma basisFold_apply (j : Fin m) :
    ∀ (l : List (Fin m)), l.Nodup → j ∉ l → ∀ (a : BinaryWalsh.Address m) (i : Fin m),
      basisFold j l a i = a i + if i ∈ l then a j else 0
  | [], _, _, a, i => by simp [basisFold]
  | j' :: l, hnd, hj, a, i => by
      rw [List.nodup_cons] at hnd
      have hj' : j ∉ l := fun h => hj (List.mem_cons_of_mem _ h)
      have hjj : j' ≠ j := fun h => hj (h ▸ List.mem_cons_self)
      have ih := basisFold_apply j l hnd.2 hj' a
      have hfold : basisFold j (j' :: l) a = sxXorCol j j' (basisFold j l a) := rfl
      rw [hfold, sxXorCol, Pi.add_apply, ih i, ih j, ite_eq_right hj', add_zero]
      by_cases hi : i = j'
      · subst hi
        simp [hnd.1]
      · simp [Pi.single_apply, hi]

/-- **The basis change as slot XORs.** -/
lemma basisFold_eq (v : BinaryWalsh.Address m) (j : Fin m) (hv : v j = 1) :
    basisFold j (basisTargets v j) = basisMap v j := by
  funext a i
  rw [basisFold_apply j _ (basisTargets_nodup v j)
    (fun h => (mem_basisTargets.1 h).2 rfl), basisMap, Pi.add_apply, Pi.smul_apply,
    Pi.add_apply, smul_eq_mul]
  refine congrArg (a i + ·) ?_
  split_ifs with hmem
  · rw [mem_basisTargets] at hmem
    rw [hmem.1, Pi.single_eq_of_ne hmem.2, add_zero, mul_one]
  · rw [mem_basisTargets] at hmem
    by_cases hij : i = j
    · subst hij
      have h2 : (1 : ZMod 2) + 1 = 0 := by decide
      rw [hv, Pi.single_eq_same, h2, mul_zero]
    · have hv0 : v i = 0 := by
        have hv01 : ∀ t : ZMod 2, t = 0 ∨ t = 1 := by decide
        rcases hv01 (v i) with h | h
        · exact h
        · exact absurd ⟨h, hij⟩ hmem
      rw [hv0, Pi.single_eq_of_ne hij, add_zero, mul_zero]

variable {n k : ℕ} {e : Fin (m * k) → Fin n}

/-- The active bits are distinct. -/
lemma basis_e_inj {a₀ ρ K : ℕ} (hK : 0 < K) (he : ∀ i, (e i : ℕ) = a₀ + ρ + K * i) :
    Function.Injective e := by
  intro i i' h
  have h1 := congrArg Fin.val h
  rw [he, he] at h1
  exact Fin.ext (Nat.eq_of_mul_eq_mul_left hK (by omega))

/-- Pulling back twice composes the column maps. -/
lemma basis_pullM_pullM {Y : Type} (he : Function.Injective e)
    (L₁ L₂ : BinaryWalsh.Address m → BinaryWalsh.Address m) (f : ZArr Y n) :
    pullM e L₁ (pullM e L₂ f) = pullM e (L₂ ∘ L₁) f := by
  funext p
  simp only [pullM, IntegerMultBounds.MathlibTM2.Layer.colBits_merge he, IntegerMultBounds.MathlibTM2.Layer.toCols_ofCols,
    IntegerMultBounds.MathlibTM2.Layer.merge_merge, Function.comp_apply]

lemma basis_pullM_id {Y : Type} (f : ZArr Y n) : pullM e id f = f := by
  funext p
  have h : (ofCols fun c => (id (colBits e c p.2) : BinaryWalsh.Address m)) =
      fun i => p.2 (e i) := by
    have : (fun c => (id (colBits e c p.2) : BinaryWalsh.Address m)) =
        toCols (fun i => p.2 (e i)) := by
      funext c j; rfl
    rw [this, IntegerMultBounds.MathlibTM2.Layer.ofCols_toCols]
  simp only [pullM, h, IntegerMultBounds.MathlibTM2.Layer.merge_extract]

end Fold

/-! ### The basis-change program -/

section Prog

open IntegerMultBounds.Networks.Shared50ModularControl (prime)

variable {T Q Ka : ℕ} {U P : Type}

/-- **The basis change** along `v` at `j`: the slot XOR of `j` into every `j' ∈ basisTargets v j`,
with the third slot `basisZ j j'`. -/
noncomputable def basisProg {ι : SXReg → Fin T} (hι : Function.Injective ι)
    (hQ : swapStates sxHd sxPay sxHd_inj ≤ Q) (par : SXPar → Fin T) (src st : Fin T)
    (v : BinaryWalsh.Address m) (j : Fin m) : Pr P T Q (prime + Ka) U :=
  Prog.seqList ((basisTargets v j).map fun (j' : Fin m) =>
    slotXorProg hι hQ par src st (j : ℕ) (j' : ℕ) (basisZ j j' : ℕ))

/-- The data of the slot XOR of `j` into `j'`. -/
def basisData (a₀ K ρ L R n rw k : ℕ) (j j' : Fin m) : SxD :=
  ⟨a₀, K, ρ, L, R, n, rw, k, j, j', basisZ j j'⟩

/-- The step bound of the slot XOR of `j` into `j'` (`slotXor_exec`). -/
noncomputable def basisCost (T : ℕ) (d : SxD) : ℝ :=
  10 * sxSwapReal d T + (sxNatCost d T (sxBad d) : ℕ)

/-- The closed form of `basisCost` (`sxNatCost_le`), with `M = R 2^n`, `k' = n + rb`. -/
lemma basisCost_le {a₀ K ρ k L R n rw : ℕ} (hρ : ρ < K) (hLK : L = K * k) (hk : 1 ≤ k)
    (hR : 1 ≤ R) (hrw : 1 ≤ rw) (hfit : a₀ + m * L ≤ n) {j j' : Fin m} (hj' : j' ≠ j) (T : ℕ) :
    basisCost T (basisData a₀ K ρ L R n rw k j j') ≤
      30 * swapConst * ((T + 12 * swapT 6 + 5 : ℕ) : ℝ) *
          ((R * 2 ^ n * (rw + (n + (sxBits R).length)) : ℕ) : ℝ) *
          ((max 1 L : ℕ) : ℝ) ^ Parameters.tau +
        ((20000 * (R * 2 ^ n * (rw + (n + (sxBits R).length) + 1)) +
          13 * (sxBad (basisData a₀ K ρ L R n rw k j j') * (n + (sxBits R).length) *
            (rw + (n + (sxBits R).length) + 1)) + 20 * T + 60 * swapT 6 + 20000 : ℕ) : ℝ) := by
  obtain ⟨hz1, hz2⟩ := basisZ_ne j j'
  have hfit' : a₀ + (sxPos j j' (basisZ j j') 0 + 1) * L ≤ n :=
    le_trans (Nat.add_le_add_left (Nat.mul_le_mul_right L (sxPos_lt_m 0)) a₀) hfit
  have hv : (basisData a₀ K ρ L R n rw k j j').Valid :=
    ⟨hρ, hLK, hk, hR, hrw, fun h => hj' (Fin.ext h).symm, fun h => hz1 (Fin.ext h).symm,
      fun h => hz2 (Fin.ext h).symm, hfit'⟩
  have hnat := (Nat.cast_le (α := ℝ)).2 (sxNatCost_le hv T (sxBad (basisData a₀ K ρ L R n rw k j j')))
  have hreal : 10 * sxSwapReal (basisData a₀ K ρ L R n rw k j j') T =
      30 * swapConst * ((T + 12 * swapT 6 + 5 : ℕ) : ℝ) *
        ((R * 2 ^ n * (rw + (n + (sxBits R).length)) : ℕ) : ℝ) *
        ((max 1 L : ℕ) : ℝ) ^ Parameters.tau := by
    unfold sxSwapReal
    have hMB : ((SxD.M (basisData a₀ K ρ L R n rw k j j') *
        SxD.Bk (basisData a₀ K ρ L R n rw k j j') : ℕ) : ℝ) =
        ((R * 2 ^ n * (rw + (n + (sxBits R).length)) : ℕ) : ℝ) := rfl
    have hL : (basisData a₀ K ρ L R n rw k j j').L = L := rfl
    rw [hMB, hL]
    ring
  unfold basisCost
  rw [hreal]
  exact add_le_add le_rfl hnat

variable (body : P → Pr P T Q (prime + Ka) U)

/-- The slot XORs of `j` into the slots `l`, from any array. -/
theorem basisList_exec {ι : SXReg → Fin T} {par : SXPar → Fin T} (henv : SxEnv ι par)
    {src st : Fin T} (hsrc : ∀ x, ι x ≠ src) (hsrcp : ∀ p, par p ≠ src) (hst : ∀ x, ι x ≠ st)
    (hA : 14 ≤ prime + Ka) (hQ : swapStates sxHd sxPay sxHd_inj ≤ Q)
    {a₀ K ρ k L R n r w : ℕ} (hρ : ρ < K) (hLK : L = K * k) (hk : 1 ≤ k) (hR : 1 ≤ R)
    (hrw : 1 ≤ r * w) (hfit : a₀ + m * L ≤ n) {e : Fin (m * k) → Fin n}
    (he : ∀ i, (e i : ℕ) = a₀ + ρ + K * i) (j : Fin m) :
    ∀ (l : List (Fin m)), (∀ j' ∈ l, j' ≠ j) →
    ∀ (Z : ZArr (Fin R × Fin r) n) (v : HS T Q (prime + Ka) U) (S : Stacks T (prime + Ka)),
      (∀ y, S.L y = []) → S.R src = encZ (prime + Ka) w Z →
      (∀ p, (S.R (par p)).length = SxD.par (basisData a₀ K ρ L R n (r * w) k j j) p) →
      (∀ x, S.R (ι x) = []) →
      ∃ (v' : HS T Q (prime + Ka) U) (c : ℕ), v'.user = v.user ∧
        (c : ℝ) ≤ (l.map fun j' => basisCost T (basisData a₀ K ρ L R n (r * w) k j j')).sum + 1 ∧
        Exec body (Prog.seqList (l.map fun (j' : Fin m) =>
            slotXorProg henv.hι hQ par src st (j : ℕ) (j' : ℕ) (basisZ j j' : ℕ))) (mk v S) c
          (mk v' { S with
            R := Function.update S.R src (encZ (prime + Ka) w (pullM e (basisFold j l) Z)) })
  | [], _, Z, v, S, _, hSsrc, _, _ => by
      refine ⟨v, 1, rfl, by simp, Exec.cast (Exec.act (body := body) .done (mk v S)) rfl ?_⟩
      have hid : basisFold j [] = id := rfl
      rw [run_done, hid, basis_pullM_id, ← hSsrc, Function.update_eq_self]
  | j' :: l, hl, Z, v, S, hL, hSsrc, hpar, hrest => by
      have hj' : j' ≠ j := hl j' List.mem_cons_self
      obtain ⟨hz1, hz2⟩ := basisZ_ne j j'
      have hpar' : ∀ p, (S.R (par p)).length =
          SxD.par ⟨a₀, K, ρ, L, R, n, r * w, k, (j : ℕ), (j' : ℕ), (basisZ j j' : ℕ)⟩ p := by
        intro p; rw [hpar p]; cases p <;> rfl
      obtain ⟨v₁, c₁, hu₁, hc₁, he₁⟩ := slotXor_exec body henv hsrc hst hA hQ (Ne.symm hj')
        (Ne.symm hz1) (Ne.symm hz2) hρ hLK hk hR hrw hfit he Z v S hL hSsrc hpar' hrest
      set Z₁ := pullM e (sxXorCol j j') Z with hZ₁
      obtain ⟨v₂, c₂, hu₂, hc₂, he₂⟩ := basisList_exec henv hsrc hsrcp hst hA hQ hρ hLK hk hR
        hrw hfit he j l (fun j'' h => hl j'' (List.mem_cons_of_mem _ h)) Z₁ v₁
        { S with R := Function.update S.R src (encZ (prime + Ka) w Z₁) } hL
        (by simp)
        (fun p => by simp only [Function.update_of_ne (hsrcp p)]; exact hpar p)
        (fun x => by simp only [Function.update_of_ne (hsrc x)]; exact hrest x)
      have hfold : pullM e (basisFold j l) Z₁ = pullM e (basisFold j (j' :: l)) Z := by
        rw [hZ₁, basis_pullM_pullM (basis_e_inj (by omega) he)]
        rfl
      refine ⟨v₂, c₁ + c₂, hu₂.trans hu₁, ?_, ?_⟩
      · simp only [List.map_cons, List.sum_cons]
        push_cast
        have h1 : (c₁ : ℝ) ≤ basisCost T (basisData a₀ K ρ L R n (r * w) k j j') := hc₁
        linarith
      · refine Exec.cast (Exec.seq he₁ he₂) rfl ?_
        rw [Function.update_idem, hfold]

/-- **The basis change.** For `v j = 1`, on the stream register `src` holding `encZ A w Z`, the
program `basisProg v j` leaves `encZ A w (pullM e (basisMap v j) Z)` on `src`; every other register
ends as it started and `user` is kept. The step bound is the sum of the slot-XOR bounds
(`basisCost`, from `slotXor_exec`) over the slots `j' ∈ basisTargets v j`, plus one. -/
theorem basisProg_exec {ι : SXReg → Fin T} {par : SXPar → Fin T} (henv : SxEnv ι par)
    {src st : Fin T} (hsrc : ∀ x, ι x ≠ src) (hsrcp : ∀ p, par p ≠ src) (hst : ∀ x, ι x ≠ st)
    (hA : 14 ≤ prime + Ka) (hQ : swapStates sxHd sxPay sxHd_inj ≤ Q)
    {a₀ K ρ k L R n r w : ℕ} (hρ : ρ < K) (hLK : L = K * k) (hk : 1 ≤ k) (hR : 1 ≤ R)
    (hrw : 1 ≤ r * w) (hfit : a₀ + m * L ≤ n) {e : Fin (m * k) → Fin n}
    (he : ∀ i, (e i : ℕ) = a₀ + ρ + K * i) (vv : BinaryWalsh.Address m) (j : Fin m)
    (hvj : vv j = 1) (Z : ZArr (Fin R × Fin r) n) (v : HS T Q (prime + Ka) U)
    (S : Stacks T (prime + Ka)) (hL : ∀ y, S.L y = []) (hSsrc : S.R src = encZ (prime + Ka) w Z)
    (hpar : ∀ p, (S.R (par p)).length = SxD.par (basisData a₀ K ρ L R n (r * w) k j j) p)
    (hrest : ∀ x, S.R (ι x) = []) :
    ∃ (v' : HS T Q (prime + Ka) U) (c : ℕ), v'.user = v.user ∧
      (c : ℝ) ≤ ((basisTargets vv j).map fun j' =>
          basisCost T (basisData a₀ K ρ L R n (r * w) k j j')).sum + 1 ∧
      Exec body (basisProg henv.hι hQ par src st vv j) (mk v S) c
        (mk v' { S with
          R := Function.update S.R src (encZ (prime + Ka) w (pullM e (basisMap vv j) Z)) }) := by
  obtain ⟨v', c, hu, hc, hex⟩ := basisList_exec body henv hsrc hsrcp hst hA hQ hρ hLK hk hR hrw
    hfit he j (basisTargets vv j) (fun j' h => (mem_basisTargets.1 h).2) Z v S hL hSsrc hpar hrest
  rw [basisFold_eq vv j hvj] at hex
  exact ⟨v', c, hu, hc, hex⟩

end Prog

end IntegerMultBounds.MathlibTM2.Node
