module

public import IntegerMultBounds.MathlibTM2.Node.CompactSlotXor

/-!
# The tilings of the compact slot XOR

The instructions of the compact slot XOR run over the eleven-field tiling `len11`, whose fields
sum to the address width `n`, with the row index above them. The layer theory (`LayE`, `LayL`,
the agreement and exceptional-set theorems) needs a tiling covering the whole index below
`R · 2^n`: the twelve-field tiling `len12 = Fin.snoc len11 rb` with the row bits as the top
field. The key pass uses the eight-field tiling `len8`. The three tilings agree on the offsets
and lengths of the shared fields, and every map involved (`dig`, `setDig`, the rotations and
swaps, the offset functions, the ideal XOR and the top fixup) depends on a field only through
its offset and length, so the permutations coincide.

* `foff_eq_sum_range`, `CxD.foff11`, `CxD.foff8`, `CxD.foff12`: the concrete offsets;
* `dig_of_foff`, `setDig_of_foff`, `rotF_of_foff`, `swapF_of_foff`, `offYW_of_foff`,
  `offYb_of_foff`, `offBb_of_foff`, `offBx_of_foff`, `idealC_of_foff`, `topFixC_of_foff`,
  `fullXorC_of_foff`, `cbad_of_foff`: invariance under a change of tiling;
* `CxD.progPerm_eq_progEPerm`, `CxD.progPerm_eq_progLPerm`: the program permutation over
  `len11` is the layer permutation over `len12`;
* `CxD.idealPerm_eq8`, `CxD.idealPerm_eq12`: the ideal permutation over the three tilings;
* `CxD.cbad_iff_badE`, `CxD.cbad_iff_badL`: the exceptional sets;
* `CxD.fullXorPermC_eq`: the full XOR is the ideal permutation followed by the top fixup.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Node

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Layer.PackedXor
  IntegerMultBounds.MathlibTM2.Layer.CompactXor

/-! ### Offsets as prefix sums -/

section Offsets

variable {nf : ℕ}

/-- The offset of field `j` is the sum of the lengths of the fields below it. -/
lemma foff_eq_sum_range (len : Fin nf → ℕ) (j : ℕ) (h : j < nf) :
    foff len ⟨j, h⟩ = ∑ i ∈ Finset.range j, (if hi : i < nf then len ⟨i, hi⟩ else 0) := by
  induction j with
  | zero => exact foff_zero len _ rfl
  | succ j ih =>
    rw [foff_succ len j h, ih (by omega), Finset.sum_range_succ, dite_eq_left (show j < nf by omega)]

/-- Appending a top field changes no lower offset. -/
lemma foff_snoc (len : Fin nf → ℕ) (v : ℕ) (f : Fin nf) :
    foff (Fin.snoc (α := fun _ => ℕ) len v) f.castSucc = foff len f := by
  obtain ⟨j, hj⟩ := f
  rw [show Fin.castSucc (⟨j, hj⟩ : Fin nf) = ⟨j, by omega⟩ from rfl, foff_eq_sum_range,
    foff_eq_sum_range]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.mem_range] at hi
  rw [dite_eq_left (show i < nf + 1 by omega), dite_eq_left (show i < nf by omega)]
  exact Fin.snoc_castSucc (α := fun _ => ℕ) (p := len) (x := v) (i := ⟨i, by omega⟩)

end Offsets

/-! ### Invariance under a change of tiling -/

section Invariance

variable {nf nf' : ℕ} {len : Fin nf → ℕ} {len' : Fin nf' → ℕ}

/-- Field `f` of `len` and field `f'` of `len'` have the same offset and length. -/
abbrev SameField (len : Fin nf → ℕ) (len' : Fin nf' → ℕ) (f : Fin nf) (f' : Fin nf') : Prop :=
  foff len f = foff len' f' ∧ len f = len' f'

lemma dig_of_foff {f : Fin nf} {f' : Fin nf'} (h1 : foff len f = foff len' f')
    (h2 : len f = len' f') (i : ℕ) : dig len f i = dig len' f' i := by
  unfold dig; rw [h1, h2]

lemma setDig_of_foff {f : Fin nf} {f' : Fin nf'} (h1 : foff len f = foff len' f')
    (h2 : len f = len' f') (i v : ℕ) : setDig len f i v = setDig len' f' i v := by
  unfold setDig; rw [h1, h2]

lemma rotF_of_foff {f : Fin nf} {f' : Fin nf'} (h1 : foff len f = foff len' f')
    (h2 : len f = len' f') (neg : Bool) (off : ℕ → ℕ) (i : ℕ) :
    rotF len f neg off i = rotF len' f' neg off i := by
  unfold rotF; rw [setDig_of_foff h1 h2, dig_of_foff h1 h2, h2]

lemma swapF_of_foff {f g : Fin nf} {f' g' : Fin nf'} (hf1 : foff len f = foff len' f')
    (hf2 : len f = len' f') (hg1 : foff len g = foff len' g') (hg2 : len g = len' g') (i : ℕ) :
    swapF len f g i = swapF len' f' g' i := by
  unfold swapF
  rw [setDig_of_foff hf1 hf2, setDig_of_foff hg1 hg2, dig_of_foff hf1 hf2, dig_of_foff hg1 hg2]

lemma offYW_of_foff {T A : Fin nf} {T' A' : Fin nf'} {K ρ G n oA sA : ℕ}
    (hT1 : foff len T = foff len' T') (hT2 : len T = len' T') (hA1 : foff len A = foff len' A')
    (hA2 : len A = len' A') :
    offYW len T K ρ G n A oA sA = offYW len' T' K ρ G n A' oA sA := by
  funext i
  unfold offYW bitAt digAt
  rw [dig_of_foff hT1 hT2, dig_of_foff hA1 hA2]

lemma offYb_of_foff {A : Fin nf} {A' : Fin nf'} {K ρ n oA sA : ℕ}
    (hA1 : foff len A = foff len' A') (hA2 : len A = len' A') :
    offYb len K ρ n A oA sA = offYb len' K ρ n A' oA sA := by
  funext i
  unfold offYb bitAt
  rw [dig_of_foff hA1 hA2]

lemma offBb_of_foff {A : Fin nf} {A' : Fin nf'} {G n oA sA : ℕ}
    (hA1 : foff len A = foff len' A') (hA2 : len A = len' A') :
    offBb len G n A oA sA = offBb len' G n A' oA sA := by
  funext i
  unfold offBb bitAt
  rw [dig_of_foff hA1 hA2]

lemma offBx_of_foff {Y A : Fin nf} {Y' A' : Fin nf'} {K ρ G n oA sA : ℕ}
    (hY1 : foff len Y = foff len' Y') (hY2 : len Y = len' Y') (hA1 : foff len A = foff len' A')
    (hA2 : len A = len' A') :
    offBx len Y K ρ G n A oA sA = offBx len' Y' K ρ G n A' oA sA := by
  funext i
  unfold offBx bitAt
  rw [dig_of_foff hY1 hY2, dig_of_foff hA1 hA2]

lemma idealC_of_foff {X Y : Fin nf} {X' Y' : Fin nf'} {K ρ n : ℕ}
    (hX1 : foff len X = foff len' X') (hX2 : len X = len' X') (hY1 : foff len Y = foff len' Y')
    (hY2 : len Y = len' Y') (i : ℕ) : idealC len X Y K ρ n i = idealC len' X' Y' K ρ n i := by
  unfold idealC
  rw [setDig_of_foff hY1 hY2, dig_of_foff hY1 hY2, dig_of_foff hX1 hX2]

lemma topFixC_of_foff {X Y : Fin nf} {X' Y' : Fin nf'} {K ρ n : ℕ}
    (hX1 : foff len X = foff len' X') (hX2 : len X = len' X') (hY1 : foff len Y = foff len' Y')
    (hY2 : len Y = len' Y') (i : ℕ) : topFixC len X Y K ρ n i = topFixC len' X' Y' K ρ n i := by
  unfold topFixC
  rw [setDig_of_foff hY1 hY2, dig_of_foff hY1 hY2, dig_of_foff hX1 hX2]

lemma fullXorC_of_foff {X Y : Fin nf} {X' Y' : Fin nf'} {K ρ n : ℕ}
    (hX1 : foff len X = foff len' X') (hX2 : len X = len' X') (hY1 : foff len Y = foff len' Y')
    (hY2 : len Y = len' Y') (i : ℕ) : fullXorC len X Y K ρ n i = fullXorC len' X' Y' K ρ n i := by
  unfold fullXorC
  rw [setDig_of_foff hY1 hY2, dig_of_foff hY1 hY2, dig_of_foff hX1 hX2]

lemma cbad_of_foff {U T Y : Fin nf} {U' T' Y' : Fin nf'} {K ρ G n : ℕ}
    (hU : SameField len len' U U') (hT : SameField len len' T T') (hY : SameField len len' Y Y')
    (useU : Bool) (i : ℕ) :
    CBad len useU U T Y K ρ G n i ↔ CBad len' useU U' T' Y' K ρ G n i := by
  unfold CBad
  rw [dig_of_foff hT.1 hT.2, dig_of_foff hU.1 hU.2, dig_of_foff hY.1 hY.2]

/-- The core sequence runs identically over two tilings agreeing on its fields. -/
lemma core_runC_eq {T Y B A : Fin nf} {T' Y' B' A' : Fin nf'} {K ρ G n oA sA : ℕ}
    (hT : SameField len len' T T') (hY : SameField len len' Y Y') (hB : SameField len len' B B')
    (hA : SameField len len' A A') (i : ℕ) :
    runC len (Layer.CompactXor.core len T Y B K ρ G n A oA sA) i =
      runC len' (Layer.CompactXor.core len' T' Y' B' K ρ G n A' oA sA) i := by
  simp only [Layer.CompactXor.core, runC_cons, runC_nil, CInstr.run,
    offYW_of_foff hT.1 hT.2 hA.1 hA.2, offBb_of_foff hY.1 hY.2, offYb_of_foff hA.1 hA.2,
    offBx_of_foff hY.1 hY.2 hA.1 hA.2, rotF_of_foff hY.1 hY.2, rotF_of_foff hB.1 hB.2,
    swapF_of_foff hT.1 hT.2 hB.1 hB.2]

/-- The load of `U` runs identically over two tilings agreeing on its fields. -/
lemma loadU_runC_eq {U X B : Fin nf} {U' X' B' : Fin nf'} {K ρ G n : ℕ}
    (hU : SameField len len' U U') (hX : SameField len len' X X') (hB : SameField len len' B B')
    (neg : Bool) (i : ℕ) :
    runC len (Layer.CompactXor.loadU len U X B K ρ G n neg) i =
      runC len' (Layer.CompactXor.loadU len' U' X' B' K ρ G n neg) i := by
  simp only [Layer.CompactXor.loadU, runC_cons, runC_nil, CInstr.run, offBb_of_foff hX.1 hX.2,
    rotF_of_foff hB.1 hB.2, swapF_of_foff hU.1 hU.2 hB.1 hB.2]

lemma progE_runC_eq {T X Y B : Fin nf} {T' X' Y' B' : Fin nf'} {K ρ G n : ℕ}
    (hT : SameField len len' T T') (hX : SameField len len' X X') (hY : SameField len len' Y Y')
    (hB : SameField len len' B B') (i : ℕ) :
    runC len (progE len T X Y B K ρ G n) i = runC len' (progE len' T' X' Y' B' K ρ G n) i :=
  core_runC_eq hT hY hB hX i

lemma progL_runC_eq {U T X Y B : Fin nf} {U' T' X' Y' B' : Fin nf'} {K ρ G n : ℕ}
    (hU : SameField len len' U U') (hT : SameField len len' T T') (hX : SameField len len' X X')
    (hY : SameField len len' Y Y') (hB : SameField len len' B B') (i : ℕ) :
    runC len (progL len U T X Y B K ρ G n) i = runC len' (progL len' U' T' X' Y' B' K ρ G n) i := by
  simp only [progL, runC_append, core_runC_eq hT hY hB hU, loadU_runC_eq hU hX hB]

end Invariance

/-! ### The tilings of the compact slot XOR -/

namespace CxD

variable (d : CxD)

/-- The twelve-field tiling of the layer theory: the eleven fields with the row bits on top. -/
def len12 : Fin 12 → ℕ := Fin.snoc (α := fun _ => ℕ) d.len11 d.rb

lemma R_le : d.R ≤ 2 ^ d.rb := (lt_two_pow_length_sxBits d.R).le

lemma K_pos (hv : d.Valid) : 1 ≤ d.K := by have := hv.hGK; omega

/-- The slot width is `(nn + 1) K`. -/
lemma L_eq (hv : d.Valid) : d.L = (d.nn + 1) * d.K := by
  rw [hv.hLK]
  unfold CxD.nn
  have := hv.hk
  rw [Nat.sub_add_cancel (show 1 ≤ d.k by omega), mul_comm]

/-- The entries of the eleven-field tiling. -/
lemma len11_val :
    (∀ h : 0 < 11, d.len11 ⟨0, h⟩ = d.bB) ∧ (∀ h : 1 < 11, d.len11 ⟨1, h⟩ = d.nG) ∧
      (∀ h : 2 < 11, d.len11 ⟨2, h⟩ = d.a₀ + d.lo * d.L - (d.bB + d.nG)) ∧
      (∀ h : 3 < 11, d.len11 ⟨3, h⟩ = d.L) ∧
      (∀ h : 4 < 11, d.len11 ⟨4, h⟩ = (d.hi - d.lo - 1) * d.L) ∧
      (∀ h : 5 < 11, d.len11 ⟨5, h⟩ = d.L) ∧
      (∀ h : 6 < 11, d.len11 ⟨6, h⟩ = d.bT - (d.a₀ + (d.hi + 1) * d.L)) ∧
      (∀ h : 7 < 11, d.len11 ⟨7, h⟩ = d.nG) ∧
      (∀ h : 8 < 11, d.len11 ⟨8, h⟩ = (d.pU - d.pT - 1) * d.nG) ∧
      (∀ h : 9 < 11, d.len11 ⟨9, h⟩ = d.nG) ∧
      (∀ h : 10 < 11, d.len11 ⟨10, h⟩ = d.n - (d.bU + d.nG)) :=
  ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl,
    fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩

/-- The entries of the eleven-field tiling at the named fields. -/
lemma len11_lit :
    d.len11 1 = d.nG ∧ d.len11 3 = d.L ∧ d.len11 5 = d.L ∧ d.len11 7 = d.nG ∧ d.len11 9 = d.nG :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- The entries of the eight-field tiling. -/
lemma len8_val :
    (∀ h : 0 < 8, d.len8 ⟨0, h⟩ = d.a₀ + d.lo * d.L) ∧ (∀ h : 1 < 8, d.len8 ⟨1, h⟩ = d.L) ∧
      (∀ h : 2 < 8, d.len8 ⟨2, h⟩ = (d.hi - d.lo - 1) * d.L) ∧ (∀ h : 3 < 8, d.len8 ⟨3, h⟩ = d.L) ∧
      (∀ h : 4 < 8, d.len8 ⟨4, h⟩ = d.n - (d.a₀ + (d.hi + 1) * d.L)) ∧
      (∀ h : 5 < 8, d.len8 ⟨5, h⟩ = d.rb) ∧ (∀ h : 6 < 8, d.len8 ⟨6, h⟩ = 0) ∧
      (∀ h : 7 < 8, d.len8 ⟨7, h⟩ = 0) :=
  ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl,
    fun _ => rfl⟩

lemma len8_lit : d.len8 1 = d.L ∧ d.len8 3 = d.L := ⟨rfl, rfl⟩

/-- `hi = lo + 1 + (hi - lo - 1)` multiplied by `L`. -/
lemma hi_mul (hxy : d.x ≠ d.y) : d.hi * d.L = d.lo * d.L + d.L + (d.hi - d.lo - 1) * d.L := by
  have hlt : d.lo + 1 ≤ d.hi := by
    unfold CxD.lo CxD.hi
    rw [Nat.min_def, Nat.max_def]
    split_ifs <;> omega
  obtain ⟨m, hm⟩ : ∃ m, d.hi = d.lo + 1 + m := ⟨d.hi - d.lo - 1, by omega⟩
  rw [show d.hi - d.lo - 1 = m by omega, hm]
  ring

/-- `pU = pT + 1 + (pU - pT - 1)` multiplied by `nG`. -/
lemma pU_mul (hpTU : d.pT < d.pU) :
    d.pU * d.nG = d.pT * d.nG + d.nG + (d.pU - d.pT - 1) * d.nG := by
  obtain ⟨m, hm⟩ : ∃ m, d.pU = d.pT + 1 + m := ⟨d.pU - d.pT - 1, by omega⟩
  rw [show d.pU - d.pT - 1 = m by omega, hm]
  ring

/-- The arithmetic of a valid datum in the form `omega` uses. -/
lemma arith (hv : d.Valid) :
    d.hi * d.L = d.lo * d.L + d.L + (d.hi - d.lo - 1) * d.L ∧
      (d.hi + 1) * d.L = d.hi * d.L + d.L ∧
      d.pU * d.nG = d.pT * d.nG + d.nG + (d.pU - d.pT - 1) * d.nG ∧
      d.bT = d.bB + d.pT * d.nG ∧ d.bU = d.bB + d.pU * d.nG ∧
      d.bB + d.nG ≤ d.a₀ + d.lo * d.L ∧ d.a₀ + (d.hi + 1) * d.L ≤ d.bT ∧ d.bU + d.nG ≤ d.n ∧
      d.pT * d.nG ≤ d.pU * d.nG :=
  ⟨d.hi_mul hv.hxy, by rw [Nat.add_mul, Nat.one_mul], d.pU_mul hv.hpTU, rfl, rfl, hv.hBlo,
    hv.hhiT, hv.hUn, Nat.mul_le_mul_right _ hv.hpTU.le⟩

/-- The offsets of the named fields of the eleven-field tiling. -/
lemma foff11 (hv : d.Valid) :
    foff d.len11 1 = d.bB ∧ foff d.len11 3 = d.a₀ + d.lo * d.L ∧
      foff d.len11 5 = d.a₀ + d.hi * d.L ∧ foff d.len11 7 = d.bT ∧ foff d.len11 9 = d.bU := by
  obtain ⟨hhiL, hhi1, hpU, hbT, hbU, hBlo, hhiT, hUn, hpT⟩ := d.arith hv
  obtain ⟨l0, l1, l2, l3, l4, l5, l6, l7, l8, l9, l10⟩ := d.len11_val
  show foff d.len11 ⟨1, by omega⟩ = _ ∧ foff d.len11 ⟨3, by omega⟩ = _ ∧
    foff d.len11 ⟨5, by omega⟩ = _ ∧ foff d.len11 ⟨7, by omega⟩ = _ ∧
    foff d.len11 ⟨9, by omega⟩ = _
  simp only [foff_eq_sum_range, Finset.sum_range_succ, Finset.sum_range_zero, Nat.reduceLT,
    dite_true, l0, l1, l2, l3, l4, l5, l6, l7, l8]
  omega

/-- The eleven fields cover the address bits. -/
lemma sum_len11 (hv : d.Valid) : ∑ g, d.len11 g = d.n := by
  obtain ⟨hhiL, hhi1, hpU, hbT, hbU, hBlo, hhiT, hUn, hpT⟩ := d.arith hv
  obtain ⟨l0, l1, l2, l3, l4, l5, l6, l7, l8, l9, l10⟩ := d.len11_val
  rw [← foff_last d.len11 10 (by omega) rfl]
  simp only [foff_eq_sum_range, Finset.sum_range_succ, Finset.sum_range_zero, Nat.reduceLT,
    dite_true, l0, l1, l2, l3, l4, l5, l6, l7, l8, l9, l10]
  omega

/-- The offsets of the slot fields of the eight-field tiling. -/
lemma foff8 (hv : d.Valid) :
    foff d.len8 1 = d.a₀ + d.lo * d.L ∧ foff d.len8 3 = d.a₀ + d.hi * d.L := by
  obtain ⟨hhiL, hhi1, hpU, hbT, hbU, hBlo, hhiT, hUn, hpT⟩ := d.arith hv
  obtain ⟨l0, l1, l2, l3, l4, l5, l6, l7⟩ := d.len8_val
  show foff d.len8 ⟨1, by omega⟩ = _ ∧ foff d.len8 ⟨3, by omega⟩ = _
  simp only [foff_eq_sum_range, Finset.sum_range_succ, Finset.sum_range_zero, Nat.reduceLT,
    dite_true, l0, l1, l2]
  omega

/-- The eight fields cover the key bits. -/
lemma sum_len8 (hv : d.Valid) : ∑ g, d.len8 g = d.n + d.rb := by
  obtain ⟨hhiL, hhi1, hpU, hbT, hbU, hBlo, hhiT, hUn, hpT⟩ := d.arith hv
  obtain ⟨l0, l1, l2, l3, l4, l5, l6, l7⟩ := d.len8_val
  rw [← foff_last d.len8 7 (by omega) rfl]
  simp only [foff_eq_sum_range, Finset.sum_range_succ, Finset.sum_range_zero, Nat.reduceLT,
    dite_true, l0, l1, l2, l3, l4, l5, l6, l7]
  omega

lemma len12_castSucc (f : Fin 11) : d.len12 f.castSucc = d.len11 f := by
  unfold CxD.len12
  exact Fin.snoc_castSucc (α := fun _ => ℕ) d.rb d.len11 f

lemma len12_last : d.len12 (Fin.last 11) = d.rb := by
  unfold CxD.len12
  exact Fin.snoc_last (α := fun _ => ℕ) d.rb d.len11

/-- The twelve-field tiling agrees with the eleven-field tiling on the eleven fields. -/
lemma foff12 (f : Fin 11) :
    foff d.len12 f.castSucc = foff d.len11 f ∧ d.len12 f.castSucc = d.len11 f :=
  ⟨foff_snoc d.len11 d.rb f, d.len12_castSucc f⟩

/-- The same, as a field correspondence from `len11` to `len12`. -/
lemma same12 (f : Fin 11) : SameField d.len11 d.len12 f f.castSucc :=
  ⟨(d.foff12 f).1.symm, (d.foff12 f).2.symm⟩

lemma dig12 (f : Fin 11) (i : ℕ) : dig d.len12 f.castSucc i = dig d.len11 f i :=
  dig_of_foff (d.foff12 f).1 (d.foff12 f).2 i

/-- The twelve fields cover the whole index. -/
lemma sum_len12 (hv : d.Valid) : ∑ g, d.len12 g = d.n + d.rb := by
  rw [Fin.sum_univ_castSucc]
  simp only [d.len12_castSucc, d.len12_last, d.sum_len11 hv]

/-! ### The fields -/

lemma fX_ne_fY : d.fX ≠ d.fY := by
  unfold CxD.fX CxD.fY
  split_ifs <;> decide

lemma len11_fX_fY : d.len11 d.fX = d.len11 d.fY := by
  unfold CxD.fX CxD.fY
  split_ifs <;> rfl

lemma kX_ne_kY : d.kX ≠ d.kY := by
  unfold CxD.kX CxD.kY
  split_ifs <;> decide

lemma len8_kX_kY : d.len8 d.kX = d.len8 d.kY := by
  unfold CxD.kX CxD.kY
  split_ifs <;> rfl

lemma fX_ne_fY12 : d.fX.castSucc ≠ d.fY.castSucc := fun h => d.fX_ne_fY (Fin.castSucc_inj.mp h)

lemma len12_fX_fY : d.len12 d.fX.castSucc = d.len12 d.fY.castSucc := by
  rw [d.len12_castSucc, d.len12_castSucc]
  exact d.len11_fX_fY

/-- The control and slot fields of the eleven-field tiling lie below bit `n`. -/
lemma field_bounds (hv : d.Valid) :
    foff d.len11 CxD.fT + d.len11 CxD.fT ≤ d.n ∧ foff d.len11 CxD.fB + d.len11 CxD.fB ≤ d.n ∧
      foff d.len11 CxD.fU + d.len11 CxD.fU ≤ d.n ∧ foff d.len11 d.fX + d.len11 d.fX ≤ d.n ∧
      foff d.len11 d.fY + d.len11 d.fY ≤ d.n := by
  obtain ⟨hhiL, hhi1, hpU, hbT, hbU, hBlo, hhiT, hUn, hpT⟩ := d.arith hv
  obtain ⟨o1, o3, o5, o7, o9⟩ := d.foff11 hv
  obtain ⟨l1, l3, l5, l7, l9⟩ := d.len11_lit
  have h3 : foff d.len11 3 + d.len11 3 ≤ d.n := by rw [o3, l3]; omega
  have h5 : foff d.len11 5 + d.len11 5 ≤ d.n := by rw [o5, l5]; omega
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · show foff d.len11 7 + d.len11 7 ≤ d.n
    rw [o7, l7]; omega
  · show foff d.len11 1 + d.len11 1 ≤ d.n
    rw [o1, l1]; omega
  · show foff d.len11 9 + d.len11 9 ≤ d.n
    rw [o9, l9]; omega
  · unfold CxD.fX
    split_ifs <;> assumption
  · unfold CxD.fY
    split_ifs <;> assumption

lemma hSY11 (hv : d.Valid) : foff d.len11 d.fY + d.len11 d.fY ≤ d.n :=
  (d.field_bounds hv).2.2.2.2

lemma hSY12 (hv : d.Valid) : foff d.len12 d.fY.castSucc + d.len12 d.fY.castSucc ≤ d.n := by
  rw [(d.foff12 _).1, (d.foff12 _).2]
  exact d.hSY11 hv

/-- The slot fields of the key tiling and of the eleven-field tiling correspond. -/
lemma same8 (hv : d.Valid) :
    SameField d.len8 d.len11 d.kX d.fX ∧ SameField d.len8 d.len11 d.kY d.fY := by
  obtain ⟨o1, o3, o5, -, -⟩ := d.foff11 hv
  obtain ⟨p1, p3⟩ := d.foff8 hv
  unfold CxD.kX CxD.kY CxD.fX CxD.fY
  split_ifs
  · exact ⟨⟨by rw [p1, o3], rfl⟩, ⟨by rw [p3, o5], rfl⟩⟩
  · exact ⟨⟨by rw [p3, o5], rfl⟩, ⟨by rw [p1, o3], rfl⟩⟩

lemma hSY8 (hv : d.Valid) : foff d.len8 d.kY + d.len8 d.kY ≤ d.n := by
  rw [(d.same8 hv).2.1, (d.same8 hv).2.2]
  exact d.hSY11 hv

/-! ### The program -/

/-- The program is well formed below bit `n`. -/
lemma prog_WF (hv : d.Valid) : ∀ ins ∈ d.prog, ins.WF d.len11 d.n := by
  obtain ⟨hST, hSB, hSU, hSX, hSY⟩ := d.field_bounds hv
  unfold CxD.prog
  by_cases hxy : d.x < d.y
  · have hX : d.fX = 3 := ite_eq_left hxy
    have hY : d.fY = 5 := ite_eq_left hxy
    rw [ite_eq_left hxy]
    exact progL_WF d.len11 rfl rfl rfl (by rw [hY]; decide) (by rw [hY]; decide) (by decide)
      (by rw [hY]; decide) (by decide) (by rw [hX]; decide) hSU hST hSY hSB
  · have hX : d.fX = 5 := ite_eq_right hxy
    have hY : d.fY = 3 := ite_eq_right hxy
    rw [ite_eq_right hxy]
    exact progE_WF d.len11 rfl rfl (by rw [hY]; decide) (by rw [hY]; decide) (by decide)
      (by rw [hX, hY]; decide) (by rw [hX]; decide) hST hSY hSB

/-- The layer hypotheses of the earlier source over the twelve-field tiling. -/
lemma layE (hv : d.Valid) (hxy : ¬ d.x < d.y) :
    LayE d.len12 CxD.fT.castSucc d.fX.castSucc d.fY.castSucc CxD.fB.castSucc d.K d.ρ d.G d.nn
      d.R d.n := by
  have hX : d.fX = 5 := ite_eq_right hxy
  have hY : d.fY = 3 := ite_eq_right hxy
  obtain ⟨hST, hSB, hSU, hSX, hSY⟩ := d.field_bounds hv
  have hL := d.L_eq hv
  refine ⟨d.K_pos hv, hv.hρ, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (d.len12_castSucc _).trans (by rw [hY]; exact hL)
  · exact (d.len12_castSucc _).trans (by rw [hX]; exact hL)
  · exact (d.len12_castSucc _).trans rfl
  · exact (d.len12_castSucc _).trans rfl
  · rw [hY]; decide
  · rw [hY]; decide
  · decide
  · rw [hX, hY]; decide
  · rw [hX]; decide
  · rw [hX]; decide
  · rw [(d.foff12 _).1, (d.foff12 _).2]; exact hST
  · rw [(d.foff12 _).1, (d.foff12 _).2]; exact hSY
  · rw [(d.foff12 _).1, (d.foff12 _).2]; exact hSB
  · rw [d.sum_len12 hv, pow_add, mul_comm]
    exact Nat.mul_le_mul_left _ d.R_le

/-- The layer hypotheses of the later source over the twelve-field tiling. -/
lemma layL (hv : d.Valid) (hxy : d.x < d.y) :
    LayL d.len12 CxD.fU.castSucc CxD.fT.castSucc d.fX.castSucc d.fY.castSucc CxD.fB.castSucc
      d.K d.ρ d.G d.nn d.R d.n := by
  have hX : d.fX = 3 := ite_eq_left hxy
  have hY : d.fY = 5 := ite_eq_left hxy
  obtain ⟨hST, hSB, hSU, hSX, hSY⟩ := d.field_bounds hv
  have hL := d.L_eq hv
  refine ⟨d.K_pos hv, hv.hG, hv.hρ, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_⟩
  · exact (d.len12_castSucc _).trans (by rw [hY]; exact hL)
  · exact (d.len12_castSucc _).trans (by rw [hX]; exact hL)
  · exact (d.len12_castSucc _).trans rfl
  · exact (d.len12_castSucc _).trans rfl
  · exact (d.len12_castSucc _).trans rfl
  · rw [hY]; decide
  · rw [hY]; decide
  · decide
  · rw [hY]; decide
  · decide
  · decide
  · rw [hX, hY]; decide
  · rw [hX]; decide
  · rw [hX]; decide
  · rw [hX]; decide
  · rw [(d.foff12 _).1, (d.foff12 _).2]; exact hSU
  · rw [(d.foff12 _).1, (d.foff12 _).2]; exact hST
  · rw [(d.foff12 _).1, (d.foff12 _).2]; exact hSY
  · rw [(d.foff12 _).1, (d.foff12 _).2]; exact hSB
  · rw [d.sum_len12 hv, pow_add, mul_comm]
    exact Nat.mul_le_mul_left _ d.R_le

/-- **Earlier source**: the program permutation over `len11` is the layer permutation over
`len12`. -/
theorem progPerm_eq_progEPerm (hv : d.Valid) (hxy : ¬ d.x < d.y) :
    Layer.CompactXor.progPerm d.len11 (R := d.R) (S := d.n) d.prog (d.prog_WF hv) =
      progEPerm d.len12 (d.layE hv hxy) :=
  Equiv.ext fun a => Fin.ext (by
    rw [Layer.CompactXor.progPerm_apply, progEPerm_apply]
    unfold CxD.prog
    rw [ite_eq_right hxy]
    exact progE_runC_eq (d.same12 _) (d.same12 _) (d.same12 _) (d.same12 _) a)

/-- **Later source**: the program permutation over `len11` is the layer permutation over
`len12`. -/
theorem progPerm_eq_progLPerm (hv : d.Valid) (hxy : d.x < d.y) :
    Layer.CompactXor.progPerm d.len11 (R := d.R) (S := d.n) d.prog (d.prog_WF hv) =
      progLPerm d.len12 (d.layL hv hxy) :=
  Equiv.ext fun a => Fin.ext (by
    rw [Layer.CompactXor.progPerm_apply, progLPerm_apply]
    unfold CxD.prog
    rw [ite_eq_left hxy]
    exact progL_runC_eq (d.same12 _) (d.same12 _) (d.same12 _) (d.same12 _) (d.same12 _) a)

/-! ### The ideal permutation, the exceptional sets and the full XOR -/

/-- The ideal permutation of the key tiling is that of the eleven-field tiling. -/
theorem idealPerm_eq8 (hv : d.Valid) :
    idealPerm d.len8 d.K d.ρ d.nn (R := d.R) d.kX_ne_kY d.len8_kX_kY (d.hSY8 hv) =
      idealPerm d.len11 d.K d.ρ d.nn (R := d.R) d.fX_ne_fY d.len11_fX_fY (d.hSY11 hv) :=
  Equiv.ext fun a => Fin.ext (idealC_of_foff (d.same8 hv).1.1 (d.same8 hv).1.2
    (d.same8 hv).2.1 (d.same8 hv).2.2 a)

/-- The ideal permutation of the twelve-field tiling is that of the eleven-field tiling. -/
theorem idealPerm_eq12 (hv : d.Valid) :
    idealPerm d.len12 d.K d.ρ d.nn (R := d.R) d.fX_ne_fY12 d.len12_fX_fY (d.hSY12 hv) =
      idealPerm d.len11 d.K d.ρ d.nn (R := d.R) d.fX_ne_fY d.len11_fX_fY (d.hSY11 hv) :=
  Equiv.ext fun a => Fin.ext (idealC_of_foff (d.foff12 _).1 (d.foff12 _).2 (d.foff12 _).1
    (d.foff12 _).2 a)

/-- The exceptional set of the earlier source. -/
theorem cbad_iff_badE (a : Fin (d.R * 2 ^ d.n)) :
    CBad d.len11 false CxD.fU CxD.fT d.fY d.K d.ρ d.G d.nn a ↔
      BadE d.len12 CxD.fT.castSucc d.fY.castSucc d.K d.ρ d.G d.nn a := by
  rw [← cbad_false_iff_badE d.len12 CxD.fU.castSucc a]
  exact cbad_of_foff (d.same12 _) (d.same12 _) (d.same12 _) false a

/-- The exceptional set of the later source. -/
theorem cbad_iff_badL (a : Fin (d.R * 2 ^ d.n)) :
    CBad d.len11 true CxD.fU CxD.fT d.fY d.K d.ρ d.G d.nn a ↔
      BadL d.len12 CxD.fU.castSucc CxD.fT.castSucc d.fY.castSucc d.K d.ρ d.G d.nn a := by
  rw [← cbad_true_iff_badL d.len12 a]
  exact cbad_of_foff (d.same12 _) (d.same12 _) (d.same12 _) true a

/-- The full XOR is the ideal permutation followed by the top fixup. -/
theorem fullXorPermC_eq (hv : d.Valid) :
    (idealPerm d.len11 d.K d.ρ d.nn (R := d.R) d.fX_ne_fY d.len11_fX_fY (d.hSY11 hv)).trans
        (topFixPermC d.len11 d.fX d.fY d.K d.ρ d.nn d.fX_ne_fY d.len11_fX_fY (d.hSY11 hv)) =
      fullXorPermC d.len11 d.fX d.fY d.K d.ρ d.nn d.fX_ne_fY d.len11_fX_fY (d.hSY11 hv) :=
  Equiv.ext fun a => Fin.ext (by
    rw [Equiv.trans_apply, topFixPermC_apply, idealPerm_apply, fullXorPermC_apply]
    exact (fullXorC_eq d.len11 (d.K_pos hv) d.fX_ne_fY d.len11_fX_fY a).symm)

end CxD

end IntegerMultBounds.MathlibTM2.Node
