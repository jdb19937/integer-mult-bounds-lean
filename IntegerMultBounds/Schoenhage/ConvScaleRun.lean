module

public import IntegerMultBounds.Schoenhage.ConvScale

/-! The synthetic convolution's last step on the ring product's word tapes:
`log₂ M` in unary from the header (`runs_kOf`). -/

@[expose] public section

set_option maxRecDepth 10000

namespace IntegerMultBounds.Schoenhage

open Machine Strm Tp Schedule Spec.SignedRingProduct

/-- Half the zeros of the axis codes of the header in `zH`, in unary on `kI`. -/
noncomputable def kOf : Cmd 0 𝕌 :=
  .seq hdrInit <| .seq skipOne <| .seq skipOne <| .seq skipOne <| .seq skipOne <| .seq skipOne <|
  .seq (op0 Rules.zhalf false (ι tX) kI (by decide)) <| .seq (clear (ι tX)) <| .seq (clear (ι c1)) (rewind kI)

set_option maxHeartbeats 8000000 in
theorem runs_kOf {p d l K w : ℕ} {ts : List ℕ} (hp : 1 ≤ p) (hd : 1 ≤ d) (hK : 1 ≤ K) (hw : 1 ≤ w)
    (τ : Fin 𝕌 → WTape) (hc : Clean τ) (hH : τ zH = reg (transformHeader p d (2 ^ l) K w ts))
    (hk : τ kI = emp) :
    Runs kOf τ (· = Function.update τ kI (reg (ones ((ts.flatMap gamma).count false / 2))))
      (300 * (transformHeader p d (2 ^ l) K w ts).length + 2000) := by
  have hz : ∀ i : Fin 𝕋, τ (ι i) = emp := fun i => congrFun hc i
  set hdr := transformHeader p d (2 ^ l) K w ts
  set tsc := ts.flatMap gamma
  set R4 := gamma w ++ tsc
  set R3 := gamma K ++ R4
  set R2 := gamma (2 ^ l) ++ R3
  set R1 := gamma d ++ R2
  have eh : hdr = gamma p ++ R1 := by simp [hdr, transformHeader, tsc, R1, R2, R3, R4]
  set H := hdr.length
  have l1 : (gamma p).length + R1.length = H := by simp [H, eh]
  have l2 : (gamma d).length + R2.length = R1.length := by simp [R1]
  have l3 : (gamma (2 ^ l)).length + R3.length = R2.length := by simp [R2]
  have l4 : (gamma K).length + R4.length = R3.length := by simp [R3]
  have l5 : (gamma w).length + tsc.length = R4.length := by simp [R4]
  have s0 : Runs hdrInit τ (· = Function.update (Function.update τ (ι c1) (reg [true])) (ι tX) (reg hdr))
      (3 * H + 30) := by
    apply Runs.of_wp
    simp only [hdrInit, regDup, regIn, cpy, WP, wp_op0, wp_rewind, wp_emit]
    tsimp [hz, hH, emp, reg, Rules.output_copy]
    refine ⟨?_, ?_⟩
    · funext y
      simp only [Function.update_apply]
      split_ifs <;> (try subst_vars) <;> (try tsimp [hz, hH, reg, emp]); tsimp at *
    · simp [time_copy]; omega
  set τ₀ := Function.update (Function.update τ (ι c1) (reg [true])) (ι tX) (reg hdr)
  have s1 := runs_skipOne hp (rest := R1) τ₀ (by tsimp [τ₀]) (by tsimp [τ₀, eh])
    (by tsimp [τ₀, hz]) (by tsimp [τ₀, hz]) (by tsimp [τ₀, hz]) (by tsimp [τ₀, hz])
  set τ₁ := Function.update τ₀ (ι tX) (reg R1)
  have s2 := runs_skipOne hd (rest := R2) τ₁ (by tsimp [τ₁, τ₀]) (by tsimp [τ₁, R1])
    (by tsimp [τ₁, τ₀, hz]) (by tsimp [τ₁, τ₀, hz]) (by tsimp [τ₁, τ₀, hz]) (by tsimp [τ₁, τ₀, hz])
  set τ₂ := Function.update τ₁ (ι tX) (reg R2)
  have s3 := runs_skipOne (Nat.one_le_two_pow (n := l)) (rest := R3) τ₂ (by tsimp [τ₂, τ₁, τ₀])
    (by tsimp [τ₂, R2])
    (by tsimp [τ₂, τ₁, τ₀, hz]) (by tsimp [τ₂, τ₁, τ₀, hz]) (by tsimp [τ₂, τ₁, τ₀, hz]) (by tsimp [τ₂, τ₁, τ₀, hz])
  set τ₃ := Function.update τ₂ (ι tX) (reg R3)
  have s4 := runs_skipOne hK (rest := R4) τ₃ (by tsimp [τ₃, τ₂, τ₁, τ₀]) (by tsimp [τ₃, R3])
    (by tsimp [τ₃, τ₂, τ₁, τ₀, hz]) (by tsimp [τ₃, τ₂, τ₁, τ₀, hz]) (by tsimp [τ₃, τ₂, τ₁, τ₀, hz])
    (by tsimp [τ₃, τ₂, τ₁, τ₀, hz])
  set τ₄ := Function.update τ₃ (ι tX) (reg R4)
  have s5 := runs_skipOne hw (rest := tsc) τ₄ (by tsimp [τ₄, τ₃, τ₂, τ₁, τ₀]) (by tsimp [τ₄, R4])
    (by tsimp [τ₄, τ₃, τ₂, τ₁, τ₀, hz]) (by tsimp [τ₄, τ₃, τ₂, τ₁, τ₀, hz]) (by tsimp [τ₄, τ₃, τ₂, τ₁, τ₀, hz])
    (by tsimp [τ₄, τ₃, τ₂, τ₁, τ₀, hz])
  set τ₅ := Function.update τ₄ (ι tX) (reg tsc)
  have s6 : Runs (a := 0) (.seq (op0 Rules.zhalf false (ι tX) kI (by decide)) <| .seq (clear (ι tX)) <|
      .seq (clear (ι c1)) (rewind kI)) τ₅
      (· = Function.update τ kI (reg (ones (tsc.count false / 2)))) (5 * tsc.length + 60) := by
    apply Runs.of_wp
    simp only [WP, wp_op0, wp_rewind, wp_clear]
    tsimp [τ₅, τ₄, τ₃, τ₂, τ₁, τ₀, hk, emp, reg, Rules.output_zhalf]
    have t1 := time_le Rules.zhalf tsc (fun j => j.elim0) 0 (fun j => j.elim0)
    refine ⟨?_, ?_⟩
    · funext y
      simp only [Function.update_apply]
      split_ifs <;> (try subst_vars) <;> (try tsimp [hz, hk, reg, emp])
    · have hb : Rules.zhalf.B = 1 := rfl
      rw [hb] at t1
      have hc : tsc.count false ≤ tsc.length := List.count_le_length
      simp [WTape.words, clen] at t1 ⊢; omega
  refine (Runs.then s0 (Runs.then s1 (Runs.then s2 (Runs.then s3 (Runs.then s4 (Runs.then s5 s6)))))).mono
    (fun τ' h => h) ?_
  simp only [List.length_append]
  omega

/-! ### Widening every component word -/

/-- Append the next piece of `xA` and `k` zeros to `zO`'s word. -/
noncomputable def scaleBody : Cmd 0 𝕌 :=
  .seq (op0 Rules.copy true xA zO (by decide)) <| .seq (op0 (Rules.fill false) true kI zO (by decide)) (rewind kI)

noncomputable def scaleLoop : Cmd 0 𝕌 := .loop xA scaleBody

theorem time_fill (c : Bool) (w : List Bool) (ws : Fin 0 → List Bool) :
    time (Rules.fill c) w ws ≤ w.length + 6 := by
  have := time_le (Rules.fill c) w ws 0 (fun j => j.elim0)
  have hb : (Rules.fill c).B = 1 := rfl
  omega

theorem runs_scaleLoop {k : ℕ} : ∀ (ps L : List (List Bool)) (acc : List Bool) (τ : Fin 𝕌 → WTape),
    τ xA = ⟨L, ps⟩ → τ zO = ⟨[acc], []⟩ → τ kI = reg (ones k) →
    Runs scaleLoop τ (· = Function.update (Function.update τ xA ⟨ps.reverse ++ L, []⟩) zO
        ⟨[acc ++ ps.flatMap (· ++ List.replicate k false)], []⟩)
      (ps.flatten.length + ps.length * (3 * k + 40))
  | [], L, acc, τ, hA, hO, hK => by
    refine (Runs.loop_done (by simp [hA]) rfl).mono (fun τ' h' => ?_) (by simp)
    subst h'
    funext y
    simp only [Function.update_apply]
    split_ifs <;> (try subst_vars) <;> simp_all
  | q :: ps, L, acc, τ, hA, hO, hK => by
    have s1 : Runs (a := 0) scaleBody τ (· = Function.update (Function.update τ xA ⟨q :: L, ps⟩) zO
        ⟨[acc ++ (q ++ List.replicate k false)], []⟩) (q.length + 3 * k + 37) := by
      apply Runs.of_wp
      simp only [scaleBody, WP, wp_op0, wp_rewind]
      tsimp [hA, hO, hK, emp, reg, Rules.output_copy, Rules.output_fill, WTape.put, WTape.next, WTape.cur]
      have t1 := time_fill false (ones k) (fun j => j.elim0)
      refine ⟨?_, ?_⟩
      · funext y
        simp only [Function.update_apply]
        split_ifs <;> (try subst_vars) <;> (try tsimp [hA, hO, hK, reg]) <;> tsimp at *
      · simp [time_copy] at t1 ⊢; omega
    set τ₁ := Function.update (Function.update τ xA ⟨q :: L, ps⟩) zO ⟨[acc ++ (q ++ List.replicate k false)], []⟩
    have ih := runs_scaleLoop (k := k) ps (q :: L) (acc ++ (q ++ List.replicate k false)) τ₁ (by tsimp [τ₁])
      (by tsimp [τ₁]) (by tsimp [τ₁, hK])
    refine (Runs.loop_step (by simp [hA]) (s1.mono (fun τ' h' => by rw [h']; exact ih) le_rfl)).mono
      (fun τ' h' => ?_) ?_
    · rw [h']; funext y
      simp only [τ₁, Function.update_apply]
      split_ifs <;> (try subst_vars) <;> simp_all
    · simp only [List.flatten_cons, List.length_append, List.length_cons]; ring_nf; omega

/-- Cut the array of `zF` into `w`-bit words and write them, each widened by `k` zeros, to `zO`. -/
noncomputable def scaleArr : Cmd 0 𝕌 :=
  .seq (chunkw zF iW xA (by decide) (by decide) (by decide)) <| .seq (rewind xA) <| .seq (emit [[]] zO) <|
  .seq scaleLoop <| .seq (clear xA) <| .seq (rewind zO) (rewind zF)

set_option maxHeartbeats 4000000 in
theorem runs_scaleArr {x : List Bool} {w k : ℕ} (hw : 1 ≤ w) (τ : Fin 𝕌 → WTape) (hF : τ zF = reg x)
    (hW : τ iW = reg (ones w)) (hK : τ kI = reg (ones k)) (hA : τ xA = emp) (hO : τ zO = emp) :
    Runs scaleArr τ (· = Function.update τ zO (reg ((cut w x).flatMap (· ++ List.replicate k false))))
      (10 * x.length + (cut w x).length * (4 * k + 60) + 40) := by
  have s1 := runs_chunkw (a := 0) (show zF ≠ iW by decide) (show zF ≠ xA by decide) (show iW ≠ xA by decide) τ
    (L := []) (R := []) (x := x) (w := w) (by simpa [reg] using hF) hW hw (by simp [hA, emp])
  set τ₁ := Function.update (Function.update τ zF ⟨[x], []⟩) xA ⟨(cut w x).reverse ++ (τ xA).left, []⟩
  have s2 := runs_rewind (a := 0) xA τ₁
  set τ₂ := Function.update τ₁ xA ⟨[], (τ₁ xA).left.reverse ++ (τ₁ xA).right⟩
  have s3 := runs_emit (a := 0) [[]] zO τ₂ (by tsimp [τ₂, τ₁, hO, emp])
  set τ₃ := Function.update τ₂ zO ⟨[[]].reverse ++ (τ₂ zO).left, []⟩
  have s4 := runs_scaleLoop (k := k) (cut w x) [] [] τ₃ (by tsimp [τ₃, τ₂, τ₁, hA, emp])
    (by tsimp [τ₃, τ₂, τ₁, hO, emp]) (by tsimp [τ₃, τ₂, τ₁, hK])
  set τ₄ := Function.update (Function.update τ₃ xA ⟨(cut w x).reverse ++ [], []⟩) zO
    ⟨[[] ++ (cut w x).flatMap (· ++ List.replicate k false)], []⟩
  have s5 := runs_clear (a := 0) xA τ₄
  have s6 := runs_rewind (a := 0) zO (Function.update τ₄ xA ⟨[], []⟩)
  have s7 := runs_rewind (a := 0) zF (Function.update (Function.update τ₄ xA ⟨[], []⟩) zO
    ⟨[], ((Function.update τ₄ xA ⟨[], []⟩) zO).left.reverse ++ ((Function.update τ₄ xA ⟨[], []⟩) zO).right⟩)
  refine (Runs.then s1 (Runs.then s2 (Runs.then s3 (Runs.then s4 (Runs.then s5 (Runs.then s6 s7)))))).mono
    (fun τ' h => ?_) ?_
  · rw [h]; funext y
    simp only [τ₄, τ₃, τ₂, τ₁, Function.update_apply]
    split_ifs <;> (try subst_vars) <;> (try tsimp [hA, hO, hF, emp, reg]) <;> tsimp at *
  · have hsum : ((cut w x).map List.length).sum = x.length := by
      rw [← List.length_flatten, cut_flatten]
    have hcl : clen (cut w x) = x.length + (cut w x).length := by
      simp only [clen, List.sum_map_add, List.map_const', List.sum_replicate, smul_eq_mul, mul_one, hsum]
    tsimp [τ₄, τ₃, τ₂, τ₁, hA, hO, hF, emp, reg, clen_cons, clen_nil, cut_flatten, clen_reverse, WTape.words,
      hcl, hsum]
    nlinarith

/-! ### The width code -/

/-- `ones (w + k)` on `qR`. -/
noncomputable def gammaA : Cmd 0 𝕌 :=
  .seq (op0 Rules.copy false iW (ι qR) (by decide)) <| .seq (rewind iW) <|
  .seq (op0 Rules.copy true kI (ι qR) (by decide)) <| .seq (rewind kI) (rewind (ι qR))

noncomputable def gammaE : Cmd 0 𝕌 := .seq (clear (ι qR)) <| .seq (clear (ι qT)) (rewind (ι qB))

noncomputable def gammaG : Cmd 0 𝕌 :=
  .seq (clear (ι qB)) <| .seq (rewind (ι tD)) <|
  .seq (op0 Rules.tailFill false (ι tD) zG (by decide)) <| .seq (rewind (ι tD)) <|
  .seq (op0 Rules.copy true (ι tD) zG (by decide)) <| .seq (clear (ι tD)) (rewind zG)

/-- `Γ(w + k)` on `zG` from `iW = ones w` and `kI = ones k`. -/
noncomputable def gammaOut : Cmd 0 𝕌 :=
  .seq gammaA <| .seq (ticksFrom (ι qR) (by decide)) <| .seq (emit [[]] (ι qB)) <| .seq (up lsbLoop) <|
  .seq gammaE <| .seq (revw (ι qB) (ι tD) (by decide)) gammaG

theorem length_lsb (n : ℕ) : (lsb n).length = Nat.size n := by
  rw [← List.length_reverse, lsb_reverse, length_msbBits]

set_option maxHeartbeats 8000000 in
theorem runs_gammaOut {w k : ℕ} (τ : Fin 𝕌 → WTape) (hc : Clean τ) (hW : τ iW = reg (ones w))
    (hK : τ kI = reg (ones k)) (hG : τ zG = emp) :
    Runs gammaOut τ (· = Function.update τ zG (reg (gamma (w + k)))) (200 * (w + k) + 400) := by
  have hz : ∀ i : Fin 𝕋, τ (ι i) = emp := fun i => congrFun hc i
  set n := w + k
  have hsz := size_le_self n
  have sA : Runs gammaA τ
      (· = Function.update τ (ι qR) (reg (ones n))) (6 * n + 40) := by
    apply Runs.of_wp
    simp only [gammaA, WP, wp_op0, wp_rewind]
    tsimp [hz, hW, hK, emp, reg, Rules.output_copy, WTape.put, WTape.next, WTape.cur]
    refine ⟨?_, ?_⟩
    · funext y
      simp only [Function.update_apply]
      split_ifs <;> (try subst_vars) <;> (try tsimp [hz, hW, hK, reg, emp, ones, n])
    · simp [time_copy, n]; omega
  set τA := Function.update τ (ι qR) (reg (ones n))
  have sB := runs_ticksFrom (show ι qR ≠ ι qT by decide) τA (b := n) (by tsimp [τA]) (by tsimp [τA, hz])
  set τB := Function.update τA (ι qT) ⟨[], List.replicate n []⟩
  have sC := runs_emit (a := 0) [[]] (ι qB) τB (by tsimp [τB, τA, hz, emp])
  set τC := Function.update τB (ι qB) ⟨[[]].reverse ++ (τB (ι qB)).left, []⟩
  have hacc := lsbAcc_eq n n [] hsz
  have sD : Runs (up lsbLoop) τC (· = Function.update (Function.update (Function.update τC
      (ι qR) (reg (ones 0))) (ι qB) ⟨[lsb n], []⟩) (ι qT) ⟨List.replicate n [] ++ [], []⟩)
      (20 * n + 80 * Nat.size n + 20 * n) := by
    have h := runs_lsbLoop n n [] [] (τC ∘ ι) [] (by tsimp [τC, τB, τA]) (by tsimp [τC, τB, τA, hz, emp])
      (by tsimp [τC, τB, τA, hz]) (by tsimp [τC, τB, τA, hz]) (by tsimp [τC, τB, τA])
    rw [hacc] at h
    simp only [List.nil_append] at h
    exact runs_up' h (by rw [ext_update, ext_update, ext_update, ext_self])
  set τD := Function.update (Function.update (Function.update τC
      (ι qR) (reg (ones 0))) (ι qB) ⟨[lsb n], []⟩) (ι qT) ⟨List.replicate n [] ++ [], []⟩
  have sE : Runs gammaE τD
      (· = Function.update (Function.update τ (ι qB) (reg (lsb n))) (ι qT) emp) (4 * n + 20) := by
    apply Runs.of_wp
    simp only [gammaE, WP, wp_rewind, wp_clear]
    tsimp [τD, τC, τB, τA, hz, emp, reg]
    refine ⟨?_, ?_⟩
    · funext y
      simp only [Function.update_apply]
      split_ifs <;> (try subst_vars) <;> (try tsimp [hz, reg, emp]); tsimp at *
    · simp [clen, WTape.words, length_lsb, ones]; omega
  set τE := Function.update (Function.update τ (ι qB) (reg (lsb n))) (ι qT) emp
  have sF := runs_revw (a := 0) (show ι qB ≠ ι tD by decide) τE (L := []) (R := []) (w := lsb n)
    (by tsimp [τE, reg]) (by tsimp [τE, hz, emp])
  set τF := Function.update (Function.update τE (ι qB) ⟨[lsb n], []⟩) (ι tD) ⟨(lsb n).reverse :: (τE (ι tD)).left, []⟩
  have sG : Runs gammaG τF
      (· = Function.update τ zG (reg (gamma n))) (20 * Nat.size n + 60) := by
    apply Runs.of_wp
    simp only [gammaG, WP, wp_op0, wp_rewind, wp_clear]
    tsimp [τF, τE, hz, hG, emp, reg, Rules.output_copy, Rules.output_tailFill, WTape.put, WTape.next,
      WTape.cur]
    have t1 := time_le Rules.tailFill (lsb n).reverse (fun j => j.elim0) 0 (fun j => j.elim0)
    refine ⟨?_, ?_⟩
    · funext y
      simp only [Function.update_apply]
      split_ifs <;> (try subst_vars) <;> (try tsimp [hz, hG, reg, emp, gamma_eq_lsb])
    · have hb : Rules.tailFill.B = 1 := rfl
      rw [hb] at t1
      simp [time_copy, clen, WTape.words, length_lsb] at t1 ⊢; omega
  refine (Runs.then sA (Runs.then sB (Runs.then sC (Runs.then sD (Runs.then sE (Runs.then sF sG)))))).mono
    (fun τ' h => h) ?_
  have hc1 : clen [[]] = 1 := rfl
  simp only [length_lsb]
  omega

/-! ### The whole step -/

theorem ι_ne_high {x : Fin 𝕌} (hx : 64 ≤ x.val) (i : Fin 𝕋) : ι i ≠ x := fun h => by
  have h1 := congrArg Fin.val h
  rw [ι_val] at h1
  have := i.isLt
  change i.val < 64 at this
  omega

theorem clean_update_outside_workspace {τ : Fin 𝕌 → WTape} (hc : Clean τ) {x : Fin 𝕌} (hx : 64 ≤ x.val) (v : WTape) :
    Clean (Function.update τ x v) := by
  funext i
  simp only [Function.comp_apply, Function.update_of_ne (ι_ne_high hx i)]
  exact congrFun hc i

/-- Decode the header, then write the array of `zF` times `M` to `zO` and `Γ(w + log₂ M)` to `zG`. -/
noncomputable def convScale : Cmd 0 𝕌 :=
  .seq decodeHeader <| .seq kOf <| .seq scaleArr <| .seq gammaOut <| .seq (clear iP) <|
  .seq (clear iL) <| .seq (clear iW) (clear kI)

/-- A bound on the step. -/
def convScaleCost (p r w H X N k : ℕ) : ℕ :=
  headerCost p r w H + 300 * H + 10 * X + N * (4 * k + 60) + 200 * (w + k) + 2 * (p + r + w + k) + 3000

set_option maxHeartbeats 8000000 in
theorem runs_convScale {p d l K w : ℕ} {ts : List ℕ} (hp : 1 ≤ p) (hd : 1 ≤ d) (hK : 1 ≤ K) (hw : 1 ≤ w)
    (hts : ∀ t ∈ ts, ∃ e, t = 2 ^ e) {x : List Bool} (τ : Fin 𝕌 → WTape) (hc : Clean τ)
    (hH : τ zH = reg (transformHeader p d (2 ^ l) K w ts)) (hF : τ zF = reg x) (hG : τ zG = emp)
    (hO : τ zO = emp) (hP : τ iP = emp) (hL : τ iL = emp) (hW : τ iW = emp) (hk : τ kI = emp)
    (hA : τ xA = emp) :
    Runs convScale τ (· = Function.update (Function.update τ zO
        (reg ((cut w x).flatMap (· ++ List.replicate (Nat.log 2 ts.prod) false))))
        zG (reg (gamma (w + Nat.log 2 ts.prod))))
      (convScaleCost p (2 ^ l) w (transformHeader p d (2 ^ l) K w ts).length x.length (cut w x).length
        (Nat.log 2 ts.prod)) := by
  have hz : ∀ i : Fin 𝕋, τ (ι i) = emp := fun i => congrFun hc i
  set k := Nat.log 2 ts.prod
  have hkz := (axes_zeros hts).1
  have s1 := runs_decodeHeader hp hd hK hw τ hc hH hP hL hW
  set τ₁ := Function.update (Function.update (Function.update τ iP (reg (ones p))) iL (reg (ones l))) iW
    (reg (ones w))
  have hc₁ : Clean τ₁ :=
    clean_update_outside_workspace (clean_update_outside_workspace (clean_update_outside_workspace hc (by decide) _) (by decide) _) (by decide) _
  have s2 := runs_kOf (l := l) (ts := ts) hp hd hK hw τ₁ hc₁ (by tsimp [τ₁, hH]) (by tsimp [τ₁, hk])
  rw [hkz] at s2
  set τ₂ := Function.update τ₁ kI (reg (ones k))
  have s3 := runs_scaleArr (x := x) (k := k) hw τ₂ (by tsimp [τ₂, τ₁, hF]) (by tsimp [τ₂, τ₁]) (by tsimp [τ₂])
    (by tsimp [τ₂, τ₁, hA]) (by tsimp [τ₂, τ₁, hO])
  set τ₃ := Function.update τ₂ zO (reg ((cut w x).flatMap (· ++ List.replicate k false)))
  have hc₃ : Clean τ₃ := clean_update_outside_workspace (clean_update_outside_workspace hc₁ (by decide) _) (by decide) _
  have s4 := runs_gammaOut (w := w) (k := k) τ₃ hc₃ (by tsimp [τ₃, τ₂, τ₁]) (by tsimp [τ₃, τ₂])
    (by tsimp [τ₃, τ₂, τ₁, hG])
  set τ₄ := Function.update τ₃ zG (reg (gamma (w + k)))
  have s5 : Runs (a := 0) (.seq (clear iP) <| .seq (clear iL) <| .seq (clear iW) (clear kI)) τ₄
      (· = Function.update (Function.update τ zO (reg ((cut w x).flatMap (· ++ List.replicate k false))))
        zG (reg (gamma (w + k)))) (2 * (p + 2 ^ l + w + k) + 20) := by
    apply Runs.of_wp
    simp only [WP, wp_clear]
    tsimp [τ₄, τ₃, τ₂, τ₁]
    refine ⟨?_, ?_⟩
    · funext y
      simp only [Function.update_apply]
      split_ifs <;> (try subst_vars) <;> (try tsimp [hP, hL, hW, hk, emp]) <;> (try tsimp at *)
    · have hl : l ≤ 2 ^ l := Nat.lt_two_pow_self.le
      simp [clen, WTape.words, reg]; omega
  refine (Runs.then s1 (Runs.then s2 (Runs.then s3 (Runs.then s4 s5)))).mono (fun τ' h => h) ?_
  unfold convScaleCost
  omega

end IntegerMultBounds.Schoenhage
