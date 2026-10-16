module

public import IntegerMultBounds.MathlibTM2.Layer.Spectators

/-!
# Column arrays as arrays on `h · k` active bits

Bit `bitIdx j c` is the bit of slot `j` in column `c`; slots are consecutive groups of `k`
bits. `lift T` applies an operator on the vendored column arrays `Arrays h k` pointwise in the
spectator. Lifted column kernels are single-bit kernels (`lift_columnKernel`), the lifted
factor for a coordinate direction is the product of kernels on one slot (`lift_vf_single`), and
the lifted full frame is `Cfull` (`lift_fullFrame`).
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Layer

open IntegerMultBounds.Networks BinaryWalsh BinaryPhase BinaryColumns ComplexEndpoints


variable {Y : Type} {h k : ℕ}

/-- The bit of slot `j` in column `c`. -/
def bitIdx (j : Fin h) (c : Fin k) : Fin (h * k) := finProdFinEquiv (j, c)

lemma bitIdx_inj {j j' : Fin h} {c c' : Fin k} : bitIdx j c = bitIdx j' c' ↔ j = j' ∧ c = c' := by
  simp [bitIdx, finProdFinEquiv.apply_eq_iff_eq, Prod.ext_iff]

/-- Column arrays read from a bit vector. -/
def toCols (b : Fin (h * k) → ZMod 2) : BinaryColumns.Address h k := fun c j => b (bitIdx j c)

/-- The bit vector of a column address. -/
def ofCols (x : BinaryColumns.Address h k) : Fin (h * k) → ZMod 2 :=
  fun t => x (finProdFinEquiv.symm t).2 (finProdFinEquiv.symm t).1

@[simp] lemma toCols_ofCols (x : BinaryColumns.Address h k) : toCols (ofCols x) = x := by
  funext c j; simp [toCols, ofCols, bitIdx]

@[simp] lemma ofCols_toCols (b : Fin (h * k) → ZMod 2) : ofCols (toCols b) = b := by
  funext t
  simp only [ofCols, toCols, bitIdx, Prod.mk.eta, Equiv.apply_symm_apply]

/-- Apply an operator on column arrays pointwise in the spectator. -/
noncomputable def lift (T : BinaryColumns.Arrays h k → BinaryColumns.Arrays h k)
    (f : Arr Y (h * k)) : Arr Y (h * k) :=
  fun p => T (fun x => f (p.1, ofCols x)) (toCols p.2)

lemma lift_comp (T S : BinaryColumns.Arrays h k → BinaryColumns.Arrays h k) (f : Arr Y (h * k)) :
    lift (fun g => T (S g)) f = lift T (lift S f) := by
  funext p
  simp only [lift, toCols_ofCols]

lemma ofCols_shift_single (c : Fin k) (j : Fin h) (x : BinaryColumns.Address h k) :
    ofCols (shift c (Pi.single j 1) x) = flip (bitIdx j c) (ofCols x) := by
  funext t
  obtain ⟨⟨j', c'⟩, rfl⟩ := finProdFinEquiv.surjective t
  simp only [ofCols, Equiv.symm_apply_apply, shift, flip, Pi.add_apply]
  by_cases hc : c' = c
  · subst hc
    by_cases hj : j' = j
    · subst hj; simp [bitIdx]
    · simp [Function.update_self, hj, bitIdx, finProdFinEquiv.apply_eq_iff_eq]
  · simp [bitIdx, finProdFinEquiv.apply_eq_iff_eq, hc]

lemma lift_columnKernel (c : Fin k) (j : Fin h) (q : ZMod 4) (f : Arr Y (h * k)) :
    lift (fun g => columnKernel c q (Pi.single j 1) g) f = kBit q (bitIdx j c) f := by
  funext p
  simp only [lift, columnKernel_apply, kBit_apply, ofCols_shift_single, ofCols_toCols]

/-- Lifting turns operator products into products. -/
lemma lift_prod (ops : List (BinaryColumns.Operator h k)) (ks : List (Arr Y (h * k) →ₗ[ℂ] Arr Y (h * k)))
    (hk : List.Forall₂ (fun T K => ∀ f, lift (fun g => T g) f = K f) ops ks) (f : Arr Y (h * k)) :
    lift (fun g => ops.prod g) f = ks.prod f := by
  induction hk generalizing f with
  | nil => funext p; simp [lift]
  | cons hTK _ ih =>
      simp only [List.prod_cons, Module.End.mul_apply]
      rw [lift_comp, ih, hTK]

/-- The lifted factor for a coordinate direction: kernels on the bits of one slot. -/
lemma lift_vf_single (q : ZMod 4) (j : Fin h) (f : Arr Y (h * k)) :
    lift (fun g => BinaryColumns.vectorFactor k (q, Pi.single j 1) g) f =
      (List.ofFn (fun c : Fin k => kBit q (bitIdx j c))).prod f := by
  apply lift_prod
  rw [List.forall₂_iff_get]
  refine ⟨by simp, fun i _ _ g => ?_⟩
  simp only [List.get_ofFn]
  exact lift_columnKernel _ j q g

/-- The enumeration of all bits by slot, then column. -/
def slotOrder (k : ℕ) : List (Fin (h * k)) :=
  (List.ofFn fun j : Fin h => List.ofFn fun c : Fin k => bitIdx j c).flatten

lemma slotOrder_perm : (slotOrder k).Perm (List.finRange (h * k)) := by
  apply (List.perm_ext_iff_of_nodup _ (List.nodup_finRange _)).2
  · intro t
    obtain ⟨⟨j, c⟩, rfl⟩ := finProdFinEquiv.surjective t
    simp only [List.mem_finRange, iff_true, slotOrder]
    exact List.mem_flatten.2 ⟨_, List.mem_ofFn.2 ⟨j, rfl⟩, List.mem_ofFn.2 ⟨c, rfl⟩⟩
  · rw [slotOrder, List.nodup_flatten]
    refine ⟨?_, ?_⟩
    · intro l hl
      obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hl
      rw [List.nodup_ofFn]
      intro c c' h
      exact (bitIdx_inj.1 h).2
    · rw [List.pairwise_ofFn]
      intro j j' hjj' a ha hb
      obtain ⟨c, rfl⟩ := List.mem_ofFn.1 ha
      obtain ⟨c', hc'⟩ := List.mem_ofFn.1 hb
      exact ne_of_lt hjj' (bitIdx_inj.1 hc').1.symm

lemma slotOrder_prod (f : Arr Y (h * k)) :
    ((slotOrder k).map (kBit 1)).prod f =
      (List.ofFn fun j : Fin h => (List.ofFn fun c : Fin k => kBit (X := Y) 1 (bitIdx j c)).prod).prod f := by
  rw [slotOrder, List.map_flatten, List.prod_flatten]
  simp only [List.map_ofFn, Function.comp_def]

/-- The lifted full frame is `C` on every bit. -/
theorem lift_fullFrame (f : Arr Y (h * k)) : lift (fun g => fullFrame k g) f = Cfull Y (h * k) f := by
  have hff : ∀ g, fullFrame (h := h) k g =
      (((coordinateKernels h).map (BinaryColumns.vectorFactor k)).prod) g :=
    fun g => congrArg (fun T : BinaryColumns.Operator h k => T g) (fullFrame_coordinate_product k)
  simp only [hff]
  rw [← prod_perm_Cfull (slotOrder k) slotOrder_perm, slotOrder_prod]
  apply lift_prod
  rw [coordinateKernels, List.map_ofFn, List.forall₂_iff_get]
  refine ⟨by simp, fun i _ _ g => ?_⟩
  simp only [List.get_ofFn, Function.comp_apply]
  exact lift_vf_single 1 _ g

/-! ### Factors along arbitrary directions -/

/-- Pull a column array back along a map applied to every column. -/
def pullCols (L : BinaryWalsh.Address h → BinaryWalsh.Address h) (f : BinaryColumns.Arrays h k) :
    BinaryColumns.Arrays h k :=
  fun x => f (fun c => L (x c))

lemma columnKernel_pull (L : BinaryWalsh.Address h → BinaryWalsh.Address h)
    (hL : ∀ a b, L (a + b) = L a + L b) (c : Fin k) (q : ZMod 4) (w : BinaryWalsh.Address h)
    (f : BinaryColumns.Arrays h k) :
    columnKernel c q w (pullCols L f) = pullCols L (columnKernel c q (L w) f) := by
  funext x
  simp only [columnKernel_apply, pullCols]
  congr 2
  congr 1
  funext c'
  by_cases hc : c' = c
  · subst hc; simp [shift, hL]
  · simp [shift, Function.update_of_ne hc]

lemma vectorFactor_pull (L : BinaryWalsh.Address h → BinaryWalsh.Address h)
    (hL : ∀ a b, L (a + b) = L a + L b) (q : ZMod 4) (w : BinaryWalsh.Address h)
    (f : BinaryColumns.Arrays h k) :
    BinaryColumns.vectorFactor k (q, w) (pullCols L f) =
      pullCols L (BinaryColumns.vectorFactor k (q, L w) f) := by
  unfold BinaryColumns.vectorFactor
  generalize (List.ofFn fun c : Fin k => c) = cs
  have key : ∀ (cs : List (Fin k)) (f : BinaryColumns.Arrays h k),
      (cs.map fun c => columnKernel c q w).prod (pullCols L f) =
        pullCols L ((cs.map fun c => columnKernel c q (L w)).prod f) := by
    intro cs
    induction cs with
    | nil => intro f; rfl
    | cons c cs ih =>
        intro f
        simp only [List.map_cons, List.prod_cons, Module.End.mul_apply, ih, columnKernel_pull L hL]
  have hw : (List.ofFn fun c : Fin k => columnKernel c q w) =
      (List.ofFn fun c : Fin k => c).map fun c => columnKernel c q w := by
    rw [List.map_ofFn]; rfl
  have hLw : (List.ofFn fun c : Fin k => columnKernel c q (L w)) =
      (List.ofFn fun c : Fin k => c).map fun c => columnKernel c q (L w) := by
    rw [List.map_ofFn]; rfl
  rw [hw, hLw]
  exact key _ f

/-- The involutive change of basis adding coordinate `j` along `v + e_j`. -/
def basisMap (v : BinaryWalsh.Address h) (j : Fin h) (a : BinaryWalsh.Address h) :
    BinaryWalsh.Address h :=
  a + a j • (v + Pi.single j 1)

lemma basisMap_add (v : BinaryWalsh.Address h) (j : Fin h) (a b : BinaryWalsh.Address h) :
    basisMap v j (a + b) = basisMap v j a + basisMap v j b := by
  simp only [basisMap, Pi.add_apply, add_smul]; abel

lemma basisMap_single (v : BinaryWalsh.Address h) (j : Fin h) :
    basisMap v j (Pi.single j 1) = v := by
  have h2 : (Pi.single j 1 : BinaryWalsh.Address h) + Pi.single j 1 = 0 := by
    funext i; by_cases hi : i = j
    · subst hi; simp; decide
    · simp [hi]
  simp only [basisMap, Pi.single_eq_same, one_smul]
  calc Pi.single j 1 + (v + Pi.single j 1) = v + (Pi.single j 1 + Pi.single j 1) := by abel
    _ = v := by rw [h2, add_zero]

lemma basisMap_invol (v : BinaryWalsh.Address h) (j : Fin h) (hv : v j = 1) (a : BinaryWalsh.Address h) :
    basisMap v j (basisMap v j a) = a := by
  have h2 : (1 : ZMod 2) + 1 = 0 := by decide
  have hj : basisMap v j a j = a j := by
    simp [basisMap, hv, CharTwo.add_self_eq_zero]
  rw [basisMap, hj, basisMap, add_assoc, ← add_smul, CharTwo.add_self_eq_zero, zero_smul, add_zero]

lemma pullCols_invol (v : BinaryWalsh.Address h) (j : Fin h) (hv : v j = 1)
    (f : BinaryColumns.Arrays h k) : pullCols (basisMap v j) (pullCols (basisMap v j) f) = f := by
  funext x; simp [pullCols, basisMap_invol v j hv]

/-- A factor along `v` is a factor along `e_j` conjugated by the change of basis. -/
theorem vectorFactor_basis (q : ZMod 4) (v : BinaryWalsh.Address h) (j : Fin h) (hv : v j = 1)
    (f : BinaryColumns.Arrays h k) :
    BinaryColumns.vectorFactor k (q, v) f =
      pullCols (basisMap v j)
        (BinaryColumns.vectorFactor k (q, Pi.single j 1) (pullCols (basisMap v j) f)) := by
  rw [vectorFactor_pull _ (basisMap_add v j), basisMap_single, pullCols_invol v j hv]

/-- Complex conjugation of an array. -/
def conjA (f : BinaryColumns.Arrays h k) : BinaryColumns.Arrays h k := fun x => star (f x)

/-- The inverse factor is the forward factor conjugated by complex conjugation. -/
theorem vectorFactor_neg (w : BinaryWalsh.Address h) (f : BinaryColumns.Arrays h k) :
    BinaryColumns.vectorFactor k (-1, w) f = conjA (BinaryColumns.vectorFactor k (1, w) (conjA f)) := by
  unfold BinaryColumns.vectorFactor
  have key : ∀ (cs : List (Fin k)) (f : BinaryColumns.Arrays h k),
      (cs.map fun c => columnKernel c (-1) w).prod f =
        conjA ((cs.map fun c => columnKernel c 1 w).prod (conjA f)) := by
    intro cs
    induction cs with
    | nil => intro f; funext x; simp [conjA]
    | cons c cs ih =>
        intro f
        simp only [List.map_cons, List.prod_cons, Module.End.mul_apply, ih]
        funext x
        simp only [columnKernel_apply, conjA, phase_one, phase_neg_one, star_add, star_mul', 
          star_div₀, star_ofNat, Complex.star_def, map_sub, map_one, Complex.conj_I]
  have h1 : (List.ofFn fun c : Fin k => columnKernel c (-1) w) =
      (List.ofFn fun c : Fin k => c).map fun c => columnKernel c (-1) w := by
    rw [List.map_ofFn]; rfl
  have h2 : (List.ofFn fun c : Fin k => columnKernel c 1 w) =
      (List.ofFn fun c : Fin k => c).map fun c => columnKernel c 1 w := by
    rw [List.map_ofFn]; rfl
  rw [h1, h2]
  exact key _ f

end IntegerMultBounds.MathlibTM2.Layer
