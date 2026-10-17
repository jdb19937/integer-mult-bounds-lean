module

public import IntegerMultBounds.MathlibTM2.Fast.CompactSynLayerFitR
public import IntegerMultBounds.MathlibTM2.Fast.CompactSynLoopsR
public import IntegerMultBounds.MathlibTM2.Mult.SynthErrQ

/-!
# The rounded rounds as computed rounds

The rounded dispatch round `compactSynLQ` is within `η = etaQ p (1/16) = √2 (1 + 1/16) 2^{-p}`
of the exact butterflies `bflyL (selBits es h)` and no larger in modulus, on disk grid inputs.
On chunk rounds this is `topRS_norm` for the rounded top (`topRSW = topRS` by `topR_fits`): the
shrink `c = 2^{s'}` bounds the piece errors (`piecesErr ≤ 2^{E + D + K}`), and
`2c/2^s ≤ 1/16` since `s - s' ≥ 5`. On direct rounds it is the truncation `Q_p`.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Fast.Main

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
open IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.Networks
open IntegerMultBounds.MathlibTM2.Mult.Rounds IntegerMultBounds.MathlibTM2.Mult.SynthErr
open IntegerMultBounds.MathlibTM2.Cost IntegerMultBounds.NLogN IntegerMultBounds.Spec.SignedRingProduct
open CompactGadgetReservationCapacity

noncomputable section

/-! ### The rounded top on one row of records -/

section Generic

variable {n a l : ℕ}

/-- The rounded top on the records `Y`: within `√2 (1 + 2c/2^s)` of the butterflies on the
selected bits, and no larger in modulus. -/
theorem topRSW_synZ_bounds (ds : ComplexFramedExecution.Directions)
    (hd : ComplexPhaseBudget.Realizes ds) (w : ℕ) (low : List (Fin n)) (top : List (Fin (n + a)))
    {R₂ : ℕ} (hR₂ : 1 * 2 ^ a ≤ R₂) (Ps : List (Piece n R₂))
    (hinj : ∀ P ∈ Ps, Function.Injective P.e) (hcover : (Ps.flatMap Piece.bitsList).Perm low)
    (hsel : (low.map (Fin.castAdd a) ++ top).Nodup) (g s c : ℕ)
    (hs : s = (low.length + top.length + 1) / 2 + top.length + (Ps.map (Piece.expR ds)).sum + g)
    (hc : √2 * piecesErr ds (2 ^ l) Ps ≤ c) (Y : ℕ → Fin (2 ^ l) → GaussianInt)
    (hP : piecesRW w ds Ps (padRows R₂ (toRows a
        (k2s top ((2 ^ g : GaussianInt) • sZ (topSel a low top) (synZ (n + a) Y))))) =
      piecesR ds Ps (padRows R₂ (toRows a
        (k2s top ((2 ^ g : GaussianInt) • sZ (topSel a low top) (synZ (n + a) Y))))))
    {x : ℕ} (hx : x < 2 ^ (n + a)) (k : Fin (2 ^ l)) :
    ‖GaussianInt.toComplex (synRd (topRSW ds w a low top hR₂ Ps g s c (synZ (n + a) Y)) x k)‖ ≤
        ‖bflyL ((topSel a low top).map Fin.val) (fun x c => GaussianInt.toComplex (Y x c)) x k‖ ∧
      ‖GaussianInt.toComplex (synRd (topRSW ds w a low top hR₂ Ps g s c (synZ (n + a) Y)) x k) -
        bflyL ((topSel a low top).map Fin.val) (fun x c => GaussianInt.toComplex (Y x c)) x k‖ ≤
        √2 * (1 + 2 * c / 2 ^ s) := by
  have e1 := topRSW_eq_topRS ds w a low top hR₂ Ps g s c (synZ (n + a) Y) hP
  have hn := topRS_norm ds hd a low top hR₂ Ps hinj hcover hsel g s c hs hc (synZ (n + a) Y)
    ((0, k), addrBits (n + a) x)
  have hH : Hl _ (low.map (Fin.castAdd a) ++ top) (toC (synZ (n + a) Y))
      ((0, k), addrBits (n + a) x) =
      bflyL ((topSel a low top).map Fin.val) (fun x c => GaussianInt.toComplex (Y x c)) x k := by
    rw [Hl_synZ]
    simp only [ofBits_addrBits hx]
    rfl
  rw [hH] at hn
  simp only [synRd, e1]
  exact hn

/-- The piece errors are at most `2^{E + D + K + 1}` when each is at most `2^K`, there are at
most `D + 1` pieces and the piece shifts sum to `E`. -/
theorem sqrt_two_piecesErr_le (ds : ComplexFramedExecution.Directions) {R₂ : ℕ}
    (Ps : List (Piece n R₂)) (K E D : ℕ)
    (hK : ∀ P ∈ Ps, errL P.u ds P.R₀ (2 ^ l) n P.j ≤ 2 ^ K)
    (hE : (Ps.map (Piece.expR ds)).sum = E) (hlen : Ps.length ≤ D + 1) :
    √2 * piecesErr ds (2 ^ l) Ps ≤ ((2 ^ (E + D + K + 1) : ℕ) : ℝ) := by
  have h1 := piecesErr_le ds (2 ^ l) Ps
  have h2 : (Ps.map fun P => errL P.u ds P.R₀ (2 ^ l) n P.j).sum ≤ Ps.length • (2 : ℝ) ^ K := by
    have := List.sum_le_length_nsmul (Ps.map fun P => errL P.u ds P.R₀ (2 ^ l) n P.j) ((2 : ℝ) ^ K)
      (fun x hx => by obtain ⟨P, hP, rfl⟩ := List.mem_map.1 hx; exact hK P hP)
    simpa using this
  have h3 : (Ps.length : ℝ) ≤ 2 ^ D := by
    have : Ps.length ≤ 2 ^ D := hlen.trans (Nat.lt_two_pow_self).nat_succ_le
    exact_mod_cast this
  have hs2 : √2 ≤ 2 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have h0 := piecesErr_nonneg ds (2 ^ l) Ps
  rw [nsmul_eq_mul] at h2
  rw [hE] at h1
  push_cast
  calc √2 * piecesErr ds (2 ^ l) Ps ≤ 2 * (2 ^ E * (2 ^ D * 2 ^ K)) := by
        have h4 : piecesErr ds (2 ^ l) Ps ≤ 2 ^ E * (2 ^ D * 2 ^ K) := by
          refine h1.trans ?_
          gcongr
          exact h2.trans (by gcongr)
        have h5 : 0 ≤ (2 : ℝ) ^ E * (2 ^ D * 2 ^ K) := by positivity
        nlinarith [Real.sqrt_nonneg 2]
    _ = 2 ^ (E + D + K + 1) := by ring

/-- `2 c / 2^s ≤ 1/16` for `c = 2^{s'}` and `s' + 5 ≤ s`. -/
theorem two_pow_shrink_le {s s' : ℕ} (h : s' + 5 ≤ s) :
    2 * ((1 * 2 ^ s' : ℕ) : ℝ) / 2 ^ s ≤ 1 / 16 := by
  obtain ⟨k, rfl⟩ : ∃ k, s = s' + 5 + k := ⟨s - (s' + 5), by omega⟩
  push_cast
  rw [div_le_iff₀ (by positivity), pow_add, pow_add]
  have : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
  have : (0 : ℝ) < 2 ^ s' := by positivity
  nlinarith

end Generic


/-! ### The rounded chunk round -/

lemma guard_hg (N l D c : ℕ) : (N + l + 2) + D * (c + 1) + D + 6 ≤ guardG c N l D := by
  unfold guardG guardKc; ring_nf; omega

lemma guard_hw (N l D c G s p W : ℕ) (hW : p + 2 ≤ W) :
    (D + m + G) + c * D + s + p + (N + l + 2) + 5 ≤ W + s + D + guardKc c N l D + G + m + 4 := by
  unfold guardKc; ring_nf; omega

/-- **The rounded chunk round.** On every input of modulus at most `2^p`, each output record of
the rounded chunk round is within `√2 (1 + 1/16)` of the butterflies on the selected physical
bits and no larger in modulus. -/
theorem compactSynChunkR_bounds (ds : ComplexFramedExecution.Directions)
    (hd : ComplexPhaseBudget.Realizes ds) (M K : ℕ) (es : List ℕ) (ℓ W l p h : ℕ)
    (H : LayHyp es ℓ K) (hc : synChunk ℓ K h) (hW : p + 2 ≤ W) :
    let d := Mult.Sizes.d M
    let g := CompactReservationGrowth.guard M
    let D := es.length
    ∀ (_hKpos : 1≤K) (_hcap : CompactReservationFits d g K D) (_hD : D≤d)
      (Y : ℕ → Fin (2^l) → GaussianInt) (_hY : ∀ x c,‖GaussianInt.toComplex (Y x c)‖≤2^p)
      {x : ℕ} (_hx : x<2^es.sum) (k : Fin (2^l)),
    ‖GaussianInt.toComplex (compactSynChunkR ds M K es ℓ W l h Y x k)‖ ≤
        ‖bflyL ((selBits es h).map (twPosL (layPerm es ℓ K)))
          (fun x c => GaussianInt.toComplex (Y x c)) x k‖ ∧
      ‖GaussianInt.toComplex (compactSynChunkR ds M K es ℓ W l h Y x k) -
        bflyL ((selBits es h).map (twPosL (layPerm es ℓ K)))
          (fun x c => GaussianInt.toComplex (Y x c)) x k‖ ≤ √2 * (1 + 1 / 16) := by
  intro d g D hKpos hcap hD Y hY x hx k
  -- the geometry of the chunk
  have haddr := synChunk_fit H hc
  simp only [synOS,hc.1,ite_true,Nat.not_lt.mpr hc.2,ite_false] at haddr
  have hfit := (Nat.le_add_right _ _).trans haddr
  let o := K*((h-layB ℓ K)/K*D)
  let ρ := (h-layB ℓ K)%K
  let n := o+K*(D-CompactGlobalRowPadding.rowAxes NW m d)
  let a := es.sum-n
  have hsplit := compactCaller_selected_split hcap hfit
  have ha : CompactGlobalRowPadding.rowAxes NW m d*K≤a := by
    show _ ≤ es.sum-n
    rw [hsplit]; omega
  have hn : n≤es.sum := by
    have := compactReservation_axes hcap
    show o+K*(D-CompactGlobalRowPadding.rowAxes NW m d)≤es.sum
    exact (Nat.add_le_add_left (Nat.mul_le_mul_left _ (Nat.sub_le _ _)) _).trans hfit
  have hna : n+a=es.sum := Nat.add_sub_of_le hn
  let q := compactTopKernelCount d g K
  let aT := compactTopKernelOffset d g K D o
  let R₂ := compactTopRows d 1 a
  let E := backChunks d g K+
    synE (gateCount (program ds)) 0
      (compactReservationActive d g K D) (compactReservationActive d g K D)
  let gb := guardG (cGain ds) es.sum l D
  let s := (D+1)/2+q+(gb+E)
  let s' := gb+E-5
  let working := W+s+D+guardKc (cGain ds) es.sum l D+gateCount (program ds)+m+4
  let pcs := compactTopPcs d g K D o R₂
  have hρ : ρ<K := Nat.mod_lt _ (by omega)
  have hfitT := (compactTopKernel_geometry (o := o) hcap hρ ha).1
  have hpcs := compactTop_working_pcs_ok ds (oS := o) (R := 1) hKpos (by omega : 1≤1) hcap hD ha (w := W)
  let Ps := topPiecesR hρ pcs (fun pc hpc => (hpcs pc hpc).okR)
  let low := (topPieces hρ pcs hpcs).flatMap Piece.bitsList
  let top := topTop aT ρ K q (n+a) hfitT
  have hR₂b := compactTopRows_bounds (d := d) (by omega : 0<K) (by omega : 0<1) ha
  have e : compactSynChunkR ds M K es ℓ W l h Y =
      synRd (topRSW ds working a low top hR₂b.1 Ps gb s (1*2^s') (synZ (n+a) Y)) :=
    compactSynChunkR_of ds M K es ℓ W l h Y hKpos hcap hD ha
  rw [e]
  -- the pieces
  have hpf := compactTopPcs_facts (o := o) (R₂ := R₂) hcap
  have hPs : Ps = topPieces hρ pcs hpcs := topPiecesR_eq hρ pcs hpcs
  have hinj : ∀ P ∈ Ps, Function.Injective P.e := by
    rw [hPs]; exact compactTopPieces_injective ds hρ pcs hpcs
  have hcover : (Ps.flatMap Piece.bitsList).Perm low := by
    rw [hPs]
  have hvals := compactTopSelection_vals ds hcap hρ hpcs hfitT
  have hsel : (low.map (Fin.castAdd a) ++ top).Nodup := compactSelection_nodup (by omega) hvals
  have hj : ∀ P ∈ Ps, P.j ≤ D := by
    intro P hP
    obtain ⟨pc, hpc, hj, -⟩ := topPiecesR_mem _ _ _ P hP
    rw [hj]; exact (hpf.2 pc hpc).1
  have hlen : Ps.length ≤ D+1 := by
    show (topPiecesR hρ pcs _).length ≤ _
    rw [topPiecesR_length]; exact hpf.1
  have htop : top.length = q := by simp [top, topTop]
  have hs : s = (low.length+top.length+1)/2+top.length+(Ps.map (Piece.expR ds)).sum+gb := by
    have h1 := compactTop_shiftR ds hcap hρ hpcs hfitT
    rw [htop]
    show (D+1)/2+q+(gb+E) = _
    have : (D+1)/2+q+E = (low.length+q+1)/2+q+(Ps.map (Piece.expR ds)).sum := h1
    omega
  have hE : (Ps.map (Piece.expR ds)).sum = E := by
    show ((topPiecesR hρ pcs _).map (Piece.expR ds)).sum = _
    rw [topPiecesR_expR, compactTopPcs_expR]
  have hK : ∀ P ∈ Ps, errL P.u ds P.R₀ (2^l) n P.j ≤ 2^(guardKc (cGain ds) es.sum l D) := by
    intro P hP
    have hb := errL_le_K P.u ds P.R₀ (2^l) n P.j (l+es.sum+1+1) D (hj P hP) (by
      rw [← P.hR]
      have h2 : 2 * (R₂ * 2^l * 2^n) ≤ 2 * (2 * 2^a * 2^l * 2^n) := by
        have : R₂ ≤ 2 * 2^a := by have := hR₂b.2.2.1; omega
        gcongr
      refine h2.trans (le_of_eq ?_)
      rw [← hna]; ring)
    refine hb.trans (le_of_eq ?_)
    unfold guardKc; ring_nf
  have hcE := sqrt_two_piecesErr_le ds Ps _ E D hK hE hlen
  have hs'e : E+D+guardKc (cGain ds) es.sum l D+1 = s' := by
    show _ = guardG (cGain ds) es.sum l D+E-5
    unfold guardG; omega
  have hcc : √2 * piecesErr ds (2^l) Ps ≤ ((1*2^s' : ℕ) : ℝ) := by
    rw [← hs'e, Nat.one_mul]; exact hcE
  -- the fit of the tape pieces
  have hP := (topR_fits ds hd a l low top hR₂b.1 hR₂b.2.2.1 Ps hinj hcover hsel gb s working p D
    (D+m+gateCount (program ds)) hs (synZ (n+a) Y) (fun z => hY _ _) hj hlen
    (fun P hP i _ => by
      obtain ⟨pc, hpc, -, hu⟩ := topPiecesR_mem _ _ _ P hP
      have h1 := scaleR_le_add P.u ds i
      have h2 := (hpf.2 pc hpc).2
      omega)
    (by rw [hna]; exact guard_hg es.sum l D (cGain ds))
    (by rw [hna]; exact guard_hw es.sum l D (cGain ds) (gateCount (program ds)) s p W hW)).1
  have hx' : x<2^(n+a) := by rw [hna]; exact hx
  obtain ⟨b1, b2⟩ := topRSW_synZ_bounds ds hd working low top hR₂b.1 Ps hinj hcover hsel gb s
    (1*2^s') hs hcc Y hP hx' k
  -- the selected physical bits
  have hphys := compactSynSelection_physical H hc _ hvals
  have hnd : ((topSel a low top).map Fin.val).Nodup := hsel.map Fin.val_injective
  rw [bflyL_perm hphys hnd] at b1 b2
  have ht := two_pow_shrink_le (s := s) (s' := s') (by
    show gb+E-5+5 ≤ (D+1)/2+q+(gb+E)
    have : 5 ≤ gb := by unfold gb guardG; omega
    omega)
  refine ⟨b1, b2.trans ?_⟩
  gcongr


/-! ### Records -/

section Records

variable {r : ℕ} [NeZero r]

/-- `y^{-e}` reads every output coefficient off one input coefficient, up to sign. -/
theorem shiftInv_norm_src (e : ℕ) (i : Fin r) :
    ∃ j : Fin r, ∀ b : Fin r → ℂ, ‖shiftInv e b i‖ = ‖b j‖ := by
  refine ⟨shiftSrc r ((2 * r - e % (2 * r)) % (2 * r)) i, fun b => ?_⟩
  unfold shiftInv
  rw [shiftNegZ_apply, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]

/-- A computed record map within `η` of an exact one and dominated by it stays so after the
twiddle `y^{-E}`. -/
theorem mulYInv_bounds (e : ℕ → ℕ) {w v : Recs r} {η : ℝ} {n : ℕ}
    (h : ∀ c, ‖w n c - v n c‖ ≤ η ∧ ‖w n c‖ ≤ ‖v n c‖) (c : Fin r) :
    ‖mulYInv e w n c - mulYInv e v n c‖ ≤ η ∧ ‖mulYInv e w n c‖ ≤ ‖mulYInv e v n c‖ := by
  obtain ⟨j, hj⟩ := shiftInv_norm_src (e n) c
  have hs : mulYInv e w n c - mulYInv e v n c = shiftInv (e n) (w n - v n) c := by
    simp only [mulYInv, shiftInv_sub, Pi.sub_apply]
  refine ⟨?_, ?_⟩
  · rw [hs, hj]; exact (h j).1
  · simp only [mulYInv]; rw [hj, hj]; exact (h j).2

end Records


/-- The butterflies on the physical selected bits of numerators are `2^p` times the logical
butterflies. -/
theorem bflyL_num (es : List ℕ) (L : Equiv.Perm (Fin es.sum)) {l : ℕ} (p h : ℕ)
    {u : Recs (2^l)} {Y : ℕ → Fin (2^l) → GaussianInt} (hY : SynNum p L u Y)
    {x : ℕ} (hx : x<2^es.sum) (c : Fin (2^l)) :
    bflyL ((selBits es h).map (twPosL L)) (fun x c => GaussianInt.toComplex (Y x c)) x c =
      2^p * bflyL (selBits es h) u (synPi L x) c := by
  have hP : ∀ q ∈ (selBits es h).map (twPosL L), q < es.sum := by
    intro q hq
    obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hq
    exact twPosL_lt L k (selBits_lt es hk)
  have e1 : (fun x c => GaussianInt.toComplex (Y x c)) =
      fun x c => (2 : ℂ) ^ p * (GaussianInt.toComplex (Y x c) / 2 ^ p) := by
    funext x c; field_simp
  have heq : EqBelow es.sum (fun x c => GaussianInt.toComplex (Y x c) / 2 ^ p)
      (synPhys L u) := by
    intro x hx; funext c; exact hY x hx c
  have h2 := bflyL_eqBelow hP heq x hx
  rw [bflyL_phys L u _ (fun q hq => selBits_lt es hq)] at h2
  rw [e1, bflyL_smul]
  beta_reduce
  rw [h2]
  rfl

/-- **The rounded dispatch round on records.** On disk grid inputs every record of
`compactSynLQ` is within `etaQ p (1/16)` of the exact butterflies and no larger. -/
theorem compactSynLQ_bounds (ds : ComplexFramedExecution.Directions)
    (hd : ComplexPhaseBudget.Realizes ds) (M K : ℕ) (es : List ℕ) (ℓ W l p h : ℕ)
    (H : LayHyp es ℓ K) (hW : p + 2 ≤ W)
    (hcap : CompactReservationFits (Mult.Sizes.d M) (CompactReservationGrowth.guard M) K es.length)
    (hD : es.length ≤ Mult.Sizes.d M) {u : Recs (2^l)} (hu : SupLe es.sum u 1) (hug : GridR p u)
    {n : ℕ} (hn : n < 2^es.sum) (c : Fin (2^l)) :
    ‖compactSynLQ ds M K es ℓ W l p h u n c - bflyL (selBits es h) u n c‖ ≤ etaQ p (1/16) ∧
      ‖compactSynLQ ds M K es ℓ W l p h u n c‖ ≤ ‖bflyL (selBits es h) u n c‖ := by
  have hp : (0 : ℝ) < 2 ^ p := by positivity
  have h2p : ‖(2 : ℂ) ^ p‖ = 2 ^ p := by simp
  unfold compactSynLQ
  split_ifs with hc
  · set L := layPerm es ℓ K
    have hY := synNum_ynum (L := L) hug
    have hYm := synMask_norm hY hu
    have hYmN := synNum_mask hY
    set Ym := synMask (2^es.sum) (synYnum p L u)
    set x : ℕ := (layRec L ⟨n, hn⟩ : ℕ) with hx_def
    have hx : x < 2^es.sum := (layRec L ⟨n, hn⟩).isLt
    have hpix : synPi L x = n := by
      rw [hx_def, synPi_layRec L (layRec L ⟨n, hn⟩), Equiv.symm_apply_apply]
    obtain ⟨b1, b2⟩ := compactSynChunkR_bounds ds hd M K es ℓ W l p h H hc hW H.K_pos hcap hD
      Ym hYm hx c
    rw [bflyL_num es L p h hYmN hx c, hpix] at b1 b2
    have hdec : synDec p L (compactSynChunkR ds M K es ℓ W l h Ym) n c =
        GaussianInt.toComplex (compactSynChunkR ds M K es ℓ W l h Ym x c) / 2^p := by
      simp only [synDec, hn, dite_true, hx_def]
    rw [hdec]
    set z := GaussianInt.toComplex (compactSynChunkR ds M K es ℓ W l h Ym x c)
    set B := bflyL (selBits es h) u n c
    refine ⟨?_, ?_⟩
    · have e : z / 2^p - B = (z - 2^p * B) / 2^p := by field_simp
      rw [e, norm_div, h2p, etaQ, div_le_div_iff_of_pos_right hp]
      exact b2
    · rw [norm_div, h2p, div_le_iff₀ hp]
      rw [norm_mul, h2p] at b1
      linarith
  · refine ⟨(rdR_sub_lt p _ n c).le.trans ?_, norm_rhoC_le p _⟩
    rw [etaQ]
    gcongr
    norm_num


/-! ### The computed rounds -/

section Ops

variable (ds : ComplexFramedExecution.Directions) (hd : ComplexPhaseBudget.Realizes ds)
  (M K : ℕ) (es : List ℕ) (ℓ W l p : ℕ) (H : LayHyp es ℓ K) (hW : p + 2 ≤ W)
  (hcap : CompactReservationFits (Mult.Sizes.d M) (CompactReservationGrowth.guard M) K es.length)
  (hD : es.length ≤ Mult.Sizes.d M)

/-- The rounded forward rounds as computed rounds. -/
def compactSynFOp : RoundOp es.sum p (fwdRound (r := 2^l) es) (etaQ p (1/16)) where
  Q := compactSynFQ ds M K es ℓ W l p
  err h _ hu hug _ hn c :=
    (mulYInv_bounds _ (fun c => compactSynLQ_bounds ds hd M K es ℓ W l p h H hW hcap hD hu hug hn c)
      c).1
  dom h _ hu hug _ hn c :=
    (mulYInv_bounds _ (fun c => compactSynLQ_bounds ds hd M K es ℓ W l p h H hW hcap hD hu hug hn c)
      c).2
  grid h u _ _ := gridR_mulYInv _ (gridR_compactSynLQ ds M K es ℓ W l p h u)

/-- The rounded opposite rounds as computed rounds. -/
def compactSynOOp : RoundOp es.sum p (oppRound (r := 2^l) es) (etaQ p (1/16)) where
  Q := compactSynOQ ds M K es ℓ W l p
  err h _ hu hug _ hn c :=
    (compactSynLQ_bounds ds hd M K es ℓ W l p h H hW hcap hD (mulY_supLe _ hu) (gridR_mulY _ hug)
      hn c).1
  dom h _ hu hug _ hn c :=
    (compactSynLQ_bounds ds hd M K es ℓ W l p h H hW hcap hD (mulY_supLe _ hu) (gridR_mulY _ hug)
      hn c).2
  grid h _ _ _ := gridR_compactSynLQ ds M K es ℓ W l p h _

include hd H hW hcap hD in
/-- The rounded rounds keep the unit disk. -/
theorem compactSynInvR_of : CompactSynInvR ds M K es ℓ W l p := by
  intro h u hu hug
  exact ⟨(compactSynFOp ds hd M K es ℓ W l p H hW hcap hD).supLe hu hug (fwdRound_supLe es h hu),
    (compactSynOOp ds hd M K es ℓ W l p H hW hcap hD).supLe hu hug (oppRound_supLe es h hu)⟩

end Ops

end

end IntegerMultBounds.MathlibTM2.Fast.Main
