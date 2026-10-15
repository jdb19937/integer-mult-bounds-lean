module

public import IntegerMultBounds.MathlibTM2.Fast.CRTControlPass
public import IntegerMultBounds.MathlibTM2.Fast.CRTControlLoop

/-! # Concrete indexed iteration over every CRT fiber

External registers 0–7 are descriptor tape, descriptor saved stack, modulus,
multiplier, padding count, slot width, data source, output accumulator.
Registers 8–13 are exponent, count, loop saved stack, index, increment scratch,
and power-construction scratch. The body is a concrete Begin followed by
PassReset, rather than an assumed execution contract.
-/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node TableVM

variable {T Q A : ℕ} {U P : Type} {body : P → Pr P T Q A U}

/-- Semantic output of a fiber supplied as physical slots. -/
def crtControlAllOut (fs : List CrtControlField) (S μ : ℕ) (fwd : Bool)
    (slots : ℕ → List (List (Fin (A + 4)))) (F : ℕ) : List (Fin (A + 4)) :=
  (if crtControlValid fs F then (slots F |>.take S).rotate
    (crtControlShift fwd S μ (crtControlValue fs F)) ++ (slots F).drop S else slots F).flatten

/-- The residual address retained between completed fibers. -/
def crtControlBoundary (fs : List CrtControlField) (F : ℕ) : ℕ :=
  if F = 0 then 0 else crtControlRemainder fs (F - 1)

@[simp] theorem crtControlBoundary_zero (fs : List CrtControlField) :
    crtControlBoundary fs 0 = 0 := by simp [crtControlBoundary]

@[simp] theorem crtControlBoundary_succ (fs : List CrtControlField) (F : ℕ) :
    crtControlBoundary fs (F + 1) = crtControlRemainder fs F := by simp [crtControlBoundary]

/-- Source and accumulator invariants, together with the canonical arithmetic
bank at a boundary between fibers. -/
noncomputable def crtControlAllRegs (rg : TblR 10 → Fin T) (e : Fin 14 → Fin T)
    (W : ℕ) (wl nl : List (Fin (A + 4))) (fs : List CrtControlField)
    (S μ N : ℕ) (fwd : Bool) (slots : ℕ → List (List (Fin (A + 4))))
    (R : Regs T A) (F : ℕ) : Regs T A :=
  crtBankOverlay rg
    (Function.update (Function.update R (e 6)
      (((List.range N).drop F).flatMap fun i => (slots i).flatten)) (e 7)
      ((List.range F).flatMap (crtControlAllOut fs S μ fwd slots)).reverse)
    (tblRho W wl nl (crtControlState (crtControlBoundary fs F) 0 true []))

/-- The concrete indexed body loads its address and completes one entire fiber. -/
def crtControlAllBody (rg : TblR 10 → Fin T) (e : Fin 14 → Fin T)
    (fwd : Bool) : Pr P T Q A U :=
  .seq (crtControlBegin rg (e 11))
    (crtControlPassReset rg fwd (e 0) (e 1) (e 2) (e 3) (e 4) (e 5) (e 6) (e 7))

/-- Runtime setup, all physical fibers, and reversal of the accumulated output
back onto the data source. -/
def crtControlAllFibers (rg : TblR 10 → Fin T) (e : Fin 14 → Fin T)
    (fwd : Bool) : Pr P T Q A U :=
  .seq (crtControlIndexedFull (rg .wr) (e 8) (e 9) (e 10) (e 11) (e 12) (e 13) (e 12)
    (crtControlAllBody rg e fwd)) (crtMv (e 7) (e 6))

/-- Exact uniform body budget, including address loading and canonical reset. -/
def crtControlAllBodyCost (D W w S n k : ℕ) : ℕ :=
  (8 * W + 8 + 10 * tblC W w) +
  (D * ((48 * W + 56 + 13 * tblC W w) + 2) + 2 + (8 * D * W + 2) +
    (16 * W + 16) + (3 * tblC W w + W * (4 * S + 22) + 4 * S + n * (8 * k + 9) + 34) +
    10 * tblC W w)

private theorem remaining_cons (N F : ℕ) (hF : F < N)
    (slots : ℕ → List (List (Fin (A + 4)))) :
    ((List.range N).drop F).flatMap (fun i => (slots i).flatten) =
      (slots F).flatten ++ ((List.range N).drop (F + 1)).flatMap (fun i => (slots i).flatten) := by
  rw [List.drop_eq_getElem_cons (by simpa using hF), List.flatMap_cons]
  simp

private theorem produced_succ (out : ℕ → List (Fin (A + 4))) (F : ℕ) :
    ((List.range (F + 1)).flatMap out).reverse =
      (out F).reverse ++ ((List.range F).flatMap out).reverse := by
  simp [List.range_succ, List.flatMap_append, List.reverse_append]

private theorem remainder_le (fs : List CrtControlField) (F : ℕ) :
    crtControlRemainder fs F ≤ F := by
  induction fs generalizing F with
  | nil => exact le_rfl
  | cons f fs ih => exact (ih _).trans (Nat.mod_le _ _)

/-- The actual Begin/PassReset body satisfies the indexed loop interface.
Every source/accumulator transition is derived from the physical fiber proof. -/
theorem crtControlAllBody_runs {rg : TblR 10 → Fin T} (hrg : Function.Injective rg)
    (e : Fin 14 → Fin T) (he : Function.Injective e) (hrge : ∀ r j, rg r ≠ e j)
    {W w N : ℕ} (hW : 0 < W) (hN : N ≤ 2 ^ W)
    (wl nl : List (Fin (A + 4))) (hwl : wl.length = W) (hnl : nl.length = w) (hw : w ≤ W)
    (fs : List CrtControlField) (M S μ n k : ℕ) (fwd : Bool)
    (hfields : ∀ f ∈ fs, 0 < f.place ∧ f.place < 2 ^ W ∧ f.bound < 2 ^ W ∧
      f.weight < 2 ^ W ∧ f.weight ≤ M)
    (hbudget : ∀ F < N, F * M < 2 ^ W)
    (hS : 0 < S) (hSlt : S < 2 ^ W) (hμ : μ < 2 ^ W)
    (hprod : ∀ F < N, μ * crtControlValue fs F < 2 ^ W)
    (slots : ℕ → List (List (Fin (A + 4))))
    (hslots : ∀ F < N, (slots F).length = n ∧ ∀ x ∈ slots F, x.length = k)
    (R : Regs T A) (htape : R (e 0) = crtControlTape W fs) (hsave : R (e 1) = [])
    (hmod : R (e 2) = binSyms W S) (hmul : R (e 3) = binSyms W μ)
    (hpadding : n = S + (R (e 4)).length) (hslot : (R (e 5)).length = k) :
    CrtControlIndexedBody (body := body) (e 9) (e 10) (e 11) (e 12) W N
      (crtControlAllBodyCost fs.length W w S n k) (crtControlAllBody rg e fwd)
      (crtControlAllRegs rg e W wl nl fs S μ N fwd slots R) := by
  let Ψ := crtControlAllRegs rg e W wl nl fs S μ N fwd slots R
  intro F hF R' hindex htmp hdata
  have hFfit : F < 2 ^ W := hF.trans_le hN
  have hbound : crtControlBoundary fs F ≤ F := by
    by_cases hz : F = 0
    · simp [crtControlBoundary, hz]
    · exact (show crtControlBoundary fs F = crtControlRemainder fs (F - 1) by
        simp [crtControlBoundary, hz]) ▸ (remainder_le fs (F - 1)).trans (Nat.sub_le _ _)
  have hone : 1 < (2 : ℕ) ^ W := by
    have hp : (2 : ℕ) ^ 1 ≤ 2 ^ W := Nat.pow_le_pow_right (by decide) hW
    norm_num at hp; omega
  have hst : ∀ j, (crtControlState (crtControlBoundary fs F) 0 true
      ([] : List (Fin (A + 4)))).val j < 2 ^ W := by
    intro j; simp only [crtControlState]; split_ifs <;> omega
  have hRbank : ∀ r, R' (rg r) = tblRho W wl nl
      (crtControlState (crtControlBoundary fs F) 0 true []) r := by
    intro r
    rw [hdata (rg r) (hrge r 9) (hrge r 10) (hrge r 11) (hrge r 12)]
    exact crtBankOverlay_on hrg _ _ _
  have hE : ∀ j : Fin 14, j.val < 9 → R' (e j) =
      Function.update (Function.update R (e 6)
        (((List.range N).drop F).flatMap fun i => (slots i).flatten)) (e 7)
        ((List.range F).flatMap (crtControlAllOut fs S μ fwd slots)).reverse (e j) := by
    intro j hj
    rw [hdata (e j) (by intro h; have := he h; omega)
      (by intro h; have := he h; omega) (by intro h; have := he h; omega)
      (by intro h; have := he h; omega)]
    exact crtBankOverlay_off _ _ _ _ (fun r => hrge r j)
  have hbegin := crtControlBegin_runs (body := body) hrg (e 11) (fun r => hrge r 11)
    hW wl nl hwl hnl hw (crtControlState (crtControlBoundary fs F) 0 true []) hst
    F hFfit R' hRbank hindex
  let B := crtBankOverlay rg R' (tblRho W wl nl (crtControlState F 0 true []))
  have hBon : ∀ r, B (rg r) = tblRho W wl nl (crtControlState F 0 true []) r := by
    intro r; exact crtBankOverlay_on hrg _ _ _
  have hBoff : ∀ j, B (e j) = R' (e j) := fun j => crtBankOverlay_off _ _ _ _ (fun r => hrge r j)
  have hpass := crtControlPassReset_runs (body := body) hrg
    (e 0) (e 1) (e 2) (e 3) (e 4) (e 5) (e 6) (e 7)
    (by simp [List.nodup_cons, he.eq_iff])
    (by intro r j hj; simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
        rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact hrge _ _)
    hW wl nl [] hwl hnl hw fs F M S μ hfields hFfit (hbudget F hF) hS hSlt hμ
    (hprod F hF) fwd B hBon
    (by rw [hBoff, hE 0 (by decide)]; simpa [he.eq_iff] using htape)
    (by rw [hBoff, hE 1 (by decide)]; simpa [he.eq_iff] using hsave)
    (by rw [hBoff, hE 2 (by decide)]; simpa [he.eq_iff] using hmod)
    (by rw [hBoff, hE 3 (by decide)]; simpa [he.eq_iff] using hmul)
    (slots F)
    (by intro x hx; rw [hBoff, hE 5 (by decide)]; simpa [he.eq_iff, hslot] using (hslots F hF).2 x hx)
    (by rw [(hslots F hF).1, hBoff, hE 4 (by decide)]; simpa [he.eq_iff] using hpadding)
    (((List.range N).drop (F + 1)).flatMap fun i => (slots i).flatten)
    (by rw [hBoff, hE 6 (by decide)]; simpa [he.eq_iff] using remaining_cons N F hF slots)
  have hlen : (slots F).length = n := (hslots F hF).1
  have hk : (B (e 5)).length = k := by rw [hBoff, hE 5 (by decide)]; simp [he.eq_iff, hslot]
  rw [hlen, hk] at hpass
  apply crtRuns_congr (crtRuns_seq hbegin hpass)
  funext j
  by_cases hj : ∃ r, rg r = j
  · obtain ⟨r, rfl⟩ := hj
    simp only [Function.update_of_ne (hrge r 7), Function.update_of_ne (hrge r 6),
      crtBankOverlay_on hrg]
    have hnot : ¬(rg r = e 9 ∨ rg r = e 10 ∨ rg r = e 11 ∨ rg r = e 12) := by
      simp [hrge]
    simp only [hnot, ↓reduceIte, crtControlAllRegs, crtBankOverlay_on hrg,
      crtControlBoundary_succ]
  · have hj' : ∀ r, rg r ≠ j := by simpa using hj
    have hBj : B j = R' j := crtBankOverlay_off _ _ _ _ hj'
    by_cases h6 : j = e 6
    · subst j
      have hc : ¬(e 6 = e 9 ∨ e 6 = e 10 ∨ e 6 = e 11 ∨ e 6 = e 12) := by simp [he.eq_iff]
      simp [he.eq_iff, crtControlAllRegs, crtBankOverlay_off, hrge]
    · by_cases h7 : j = e 7
      · subst j
        have hc : ¬(e 7 = e 9 ∨ e 7 = e 10 ∨ e 7 = e 11 ∨ e 7 = e 12) := by simp [he.eq_iff]
        rw [Function.update_self]
        simp only [hc, ↓reduceIte, crtControlAllRegs,
          crtBankOverlay_off _ _ _ _ (fun r => hrge r 7), Function.update_self]
        rw [produced_succ, hBoff, hE 7 (by decide), Function.update_self]
        rfl
      · simp only [Function.update_of_ne h7, Function.update_of_ne h6, crtBankOverlay_off _ _ _ _ hj', hBj]
        split_ifs with hc
        · rfl
        · have hnc : j ≠ e 9 ∧ j ≠ e 10 ∧ j ≠ e 11 ∧ j ≠ e 12 := by tauto
          rw [hdata j hnc.1 hnc.2.1 hnc.2.2.1 hnc.2.2.2]
          simp only [crtControlAllRegs, crtBankOverlay_off _ _ _ _ hj',
            Function.update_of_ne h7, Function.update_of_ne h6]

/-- Rotation and invalid-fiber copying preserve the number of data symbols. -/
theorem crtControlAllOut_length (fs : List CrtControlField) (S μ F n k : ℕ) (fwd : Bool)
    (slots : ℕ → List (List (Fin (A + 4))))
    (hlen : (slots F).length = n) (hslots : ∀ x ∈ slots F, x.length = k) :
    (crtControlAllOut fs S μ fwd slots F).length = n * k := by
  unfold crtControlAllOut
  split
  · rw [crt_length_flatten_uniform k _ (by
      intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact hslots x (List.mem_of_mem_take (List.mem_rotate.mp hx))
      · exact hslots x (List.mem_of_mem_drop hx))]
    congr 1
    simp only [List.length_append, List.length_rotate, List.length_take, List.length_drop, hlen]
    omega
  · rw [crt_length_flatten_uniform k _ hslots, hlen]

/-- Exact full-pass cost including runtime count construction, binary index
increments, descriptor restoration on every fiber, and final output reversal. -/
def crtControlAllCost (D W w L S n k : ℕ) : ℕ :=
  2 ^ L * (crtControlAllBodyCost D W w S n k + 4 * W + 16) +
    6 * W + 9 * L + 17 + (2 * (2 ^ L * n * k) + 2)

/-- Every runtime-addressed fiber executes the concrete descriptor scanner and
physical shift. The final data source contains the entire output in order;
the output accumulator, index, loop count and all loop scratch are empty. -/
theorem crtControlAllFibers_runs {rg : TblR 10 → Fin T} (hrg : Function.Injective rg)
    (e : Fin 14 → Fin T) (he : Function.Injective e) (hrge : ∀ r j, rg r ≠ e j)
    {W w L : ℕ} (hW : 0 < W) (hL : L ≤ W)
    (wl nl : List (Fin (A + 4))) (hwl : wl.length = W) (hnl : nl.length = w) (hw : w ≤ W)
    (fs : List CrtControlField) (M S μ n k : ℕ) (fwd : Bool)
    (hfields : ∀ f ∈ fs, 0 < f.place ∧ f.place < 2 ^ W ∧ f.bound < 2 ^ W ∧
      f.weight < 2 ^ W ∧ f.weight ≤ M)
    (hbudget : ∀ F < 2 ^ L, F * M < 2 ^ W)
    (hS : 0 < S) (hSlt : S < 2 ^ W) (hμ : μ < 2 ^ W)
    (hprod : ∀ F < 2 ^ L, μ * crtControlValue fs F < 2 ^ W)
    (slots : ℕ → List (List (Fin (A + 4))))
    (hslots : ∀ F < 2 ^ L, (slots F).length = n ∧ ∀ x ∈ slots F, x.length = k)
    (R : Regs T A) (htape : R (e 0) = crtControlTape W fs) (hsave : R (e 1) = [])
    (hmod : R (e 2) = binSyms W S) (hmul : R (e 3) = binSyms W μ)
    (hpadding : n = S + (R (e 4)).length) (hslot : (R (e 5)).length = k)
    (hexponent : (R (e 8)).length = L)
    (hclean : ∀ j : Fin 14, 9 ≤ j.val → R (e j) = [])
    (hsource : R (e 6) = (List.range (2 ^ L)).flatMap (fun F => (slots F).flatten))
    (hacc : R (e 7) = []) :
    crtRuns body (crtControlAllFibers rg e fwd)
      (crtBankOverlay rg R (tblRho W wl nl (crtControlState 0 0 true [])))
      (Function.update (Function.update (crtBankOverlay rg R
        (tblRho W wl nl (crtControlState (crtControlBoundary fs (2 ^ L)) 0 true [])))
        (e 7) []) (e 6) ((List.range (2 ^ L)).flatMap (crtControlAllOut fs S μ fwd slots)))
      (crtControlAllCost fs.length W w L S n k) := by
  let Ψ := crtControlAllRegs rg e W wl nl fs S μ (2 ^ L) fwd slots R
  have hwidth : (Ψ 0 (rg .wr)).length = W := by
    simpa [Ψ, crtControlAllRegs, crtBankOverlay_on hrg, tblRho] using hwl
  have hexp : (Ψ 0 (e 8)).length = L := by
    simpa [Ψ, crtControlAllRegs, crtBankOverlay_off, hrge, he.eq_iff] using hexponent
  have hclean' : ∀ F, Ψ F (e 9) = [] ∧ Ψ F (e 10) = [] ∧ Ψ F (e 11) = [] ∧
      Ψ F (e 12) = [] ∧ Ψ F (e 13) = [] := by
    intro F
    simp [Ψ, crtControlAllRegs, crtBankOverlay_off, hrge, he.eq_iff, hclean]
  have hfixed : ∀ F, Ψ F (rg .wr) = Ψ 0 (rg .wr) ∧ Ψ F (e 8) = Ψ 0 (e 8) := by
    intro F
    simp [Ψ, crtControlAllRegs, crtBankOverlay_on hrg, crtBankOverlay_off, hrge, he.eq_iff, tblRho]
  have hp := crtControlAllBody_runs (body := body) hrg e he hrge hW
    (Nat.pow_le_pow_right (by decide) hL) wl nl hwl hnl hw fs M S μ n k fwd
    hfields hbudget hS hSlt hμ hprod slots hslots R htape hsave hmod hmul hpadding hslot
  have hloop := crtControlIndexedFull_runs (body := body)
    (width := rg .wr) (exponent := e 8) (count := e 9) (saved := e 10) (index := e 11)
    (tmp := e 12) (spare := e 13)
    (by simp [List.nodup_cons, hrge, he.eq_iff]) (e 12) hwidth hexp hclean' hfixed hp
  have hin : Ψ 0 = crtBankOverlay rg R (tblRho W wl nl (crtControlState 0 0 true [])) := by
    funext j
    by_cases hj : ∃ r, rg r = j
    · obtain ⟨r, rfl⟩ := hj
      simp [Ψ, crtControlAllRegs, crtBankOverlay_on hrg]
    · have hj' : ∀ r, rg r ≠ j := by simpa using hj
      simp only [Ψ, crtControlAllRegs, crtBankOverlay_off _ _ _ _ hj', List.drop_zero,
        List.range_zero, List.flatMap_nil, List.reverse_nil]
      by_cases h6 : j = e 6 <;> by_cases h7 : j = e 7 <;> simp_all [he.eq_iff]
  have hsrcN : Ψ (2 ^ L) (e 6) = [] := by
    have hdrop : (List.range (2 ^ L)).drop (2 ^ L) = [] := List.drop_eq_nil_of_le (by simp)
    simp [Ψ, crtControlAllRegs, crtBankOverlay_off, hrge, he.eq_iff, hdrop]
  have haccN : Ψ (2 ^ L) (e 7) =
      ((List.range (2 ^ L)).flatMap (crtControlAllOut fs S μ fwd slots)).reverse := by
    simp [Ψ, crtControlAllRegs, crtBankOverlay_off, hrge]
  have houtlen : ((List.range (2 ^ L)).flatMap (crtControlAllOut fs S μ fwd slots)).length =
      2 ^ L * n * k := by
    rw [List.flatMap_def, crt_length_flatten_uniform (n * k) _ (by
      intro x hx
      obtain ⟨F, hF, rfl⟩ := List.mem_map.mp hx
      have hF' := List.mem_range.mp hF
      exact crtControlAllOut_length fs S μ F n k fwd slots (hslots F hF').1 (hslots F hF').2)]
    simp [Nat.mul_assoc]
  have hmove := crtMv_runs (body := body) (show e 7 ≠ e 6 from fun h => by
    have := he h; contradiction) (Ψ (2 ^ L))
  rw [haccN, hsrcN, List.reverse_reverse, List.append_nil, List.length_reverse, houtlen] at hmove
  refine crtRuns_congr (crtRuns_seq (crtRuns_congr_left hloop hin.symm) hmove) ?_
  funext j
  by_cases h6 : j = e 6
  · subst j; simp
  · by_cases h7 : j = e 7
    · subst j; simp [he.eq_iff]
    · simp only [Function.update_of_ne h6, Function.update_of_ne h7]
      by_cases hj : ∃ r, rg r = j
      · obtain ⟨r, rfl⟩ := hj
        simp only [Ψ, crtControlAllRegs, crtBankOverlay_on hrg]
      · have hj' : ∀ r, rg r ≠ j := by simpa using hj
        simp only [Ψ, crtControlAllRegs, crtBankOverlay_off _ _ _ _ hj',
          Function.update_of_ne h6, Function.update_of_ne h7]

end IntegerMultBounds.MathlibTM2.Fast
