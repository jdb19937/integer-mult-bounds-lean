module

public import IntegerMultBounds.Schoenhage.PrefixRoundTape
public import IntegerMultBounds.Schoenhage.TwistRound
public import IntegerMultBounds.Schoenhage.DifOppositeRounds

/-! §6 task 5: the exact butterflies of a prefix slot and one truncation, on the
ring product's word tapes (`runs_prefixHad`): from the record array on `zF`
to the array of `truncRec D` of the exact butterflies on the bits
`s, …, s + D - 1`, written on `zO`. -/

@[expose] public section

set_option maxRecDepth 10000

namespace IntegerMultBounds.Schoenhage

open Machine Strm Tp Schedule Rules Spec.SignedRingProduct


noncomputable def phA : Cmd 0 𝕌 := .seq (chunkw zF kw xA (by decide) (by decide) (by decide)) (rewind xA)

noncomputable def phB : Cmd 0 𝕌 :=
  .seq (clear xA) <| .seq (rewind xB) <| .seq (rewind zF) (ticksFrom kS (by decide))

noncomputable def phC : Cmd 0 𝕌 := .seq (clear (ι qT)) (clear xP)

noncomputable def phD : Cmd 0 𝕌 := .seq (rewind (ι tD)) (clear xB)

noncomputable def phE : Cmd 0 𝕌 := .seq (clear (ι tD)) <| .seq (rewind xE) (emit [[]] zO)

noncomputable def phF : Cmd 0 𝕌 := .seq (clear xE) <| .seq (rewind zO) <| .seq (clear kH) (clear kC)

/-- The exact butterflies of a prefix slot, then one truncation. -/
noncomputable def prefixHad : Cmd 0 𝕌 :=
  .seq phA <| .seq offLoop <| .seq phB <| .seq passesLoop <| .seq phC <| .seq zextLoop <| .seq phD <|
  .seq constK <| .seq (digitLoop xE own_xE (by decide)) <| .seq phE <| .seq prJoinLoop phF

/-- A bound on the prefix round for `N` words of width `w` and `D` passes. -/
def prefixCost (w D N : ℕ) : ℕ :=
  D * (N * (40 * (w + D) + 400) + 200) + N * (100 * (w + D) + 400) + 100 * (w + D) + 500

set_option maxHeartbeats 32000000 in
theorem runs_prefixHad {r w D s c : ℕ} (hr : 1 ≤ r) (hw : 2 ≤ w) (hc : 1 ≤ c) (fs : List (Rec r))
    (hlen : fs.length = 2 ^ (s + D) * c) (hb : Bounded (2 ^ (w - 1) - 1) fs) (τ : Fin 𝕌 → WTape)
    (hcl : Clean τ) (hF : τ zF = reg (array w fs)) (hW : τ kw = reg (ones w)) (hS : τ kS = reg (ones D))
    (hP : τ xP = reg (ones (2 * r * 2 ^ s))) (hA : τ xA = emp) (hB : τ xB = emp) (hC : τ xC = emp)
    (hQ : τ xQ = emp) (hE : τ xE = emp) (hrF : τ rF = emp) (hrG : τ rG = emp) (hrO : τ rO = emp)
    (hkW : τ kW = emp) (hkH : τ kH = emp) (hkC : τ kC = emp) (hO : τ zO = emp) :
    Runs prefixHad τ (· = Function.update (Function.update τ zO
      (reg (array w ((bflysRecs ((List.range D).map (s + ·)) fs).map (truncRec D))))) xP emp)
      (prefixCost w D (2 * r * fs.length)) := by
  have hz : ∀ i : Fin 𝕋, τ (ι i) = emp := fun i => congrFun hcl i
  have hw1 : 1 ≤ w := by omega
  set x := array w fs
  set N := 2 * r * fs.length
  set ws := cut w x
  have hxl : x.length = N * w := by simp [x, length_array, N]; ring
  have hwsl : ws.length = N := by
    rw [length_cut hw1 _ (by rw [hxl]; exact Dvd.intro_left _ rfl), hxl, Nat.mul_div_cancel _ (by omega)]
  have hwsw : ∀ y ∈ ws, y.length = w := cut_lengths hw1 x (by rw [hxl]; exact Dvd.intro_left _ rfl)
  have hbnd : ∀ f ∈ fs, ∀ j, -2 ^ (w - 1) ≤ f.1 j ∧ f.1 j < 2 ^ (w - 1) ∧ -2 ^ (w - 1) ≤ f.2 j ∧
      f.2 j < 2 ^ (w - 1) := by
    intro f hf j
    obtain ⟨b1, b2⟩ := comp_bound_of hb hf j
    rw [abs_le] at b1 b2
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  have hoffs : ws.map (fun y => flipLast y.reverse) = arrOff w fs := cut_array_off hw1 fs hbnd
  -- 1. cut into words
  have s1 : Runs phA τ (· = Function.update (Function.update τ zF ⟨[x], []⟩) xA ⟨[], ws⟩) (6 * N * (w + 1) + 10) := by
    have c1 := runs_chunkw (a := 0) (show zF ≠ kw by decide) (show zF ≠ xA by decide) (show kw ≠ xA by decide) τ
      (L := []) (R := []) (x := x) (w := w) (by simpa [reg] using hF) hW hw1 (by simp [hA, emp])
    have c2 := runs_rewind (a := 0) xA (Function.update (Function.update τ zF ⟨[x], []⟩) xA
      ⟨(cut w x).reverse ++ (τ xA).left, []⟩)
    refine (Runs.then c1 c2).mono (fun σ h => ?_) ?_
    · rw [h]; funext y; simp only [Function.update_apply]
      split_ifs <;> (try subst_vars) <;> tsimp [hA, emp] <;> rfl
    · have h1 : clen (cut w x) = N * (w + 1) := by rw [← hwsl]; exact clen_uniform ws w hwsw
      tsimp [hA, emp, clen_reverse, h1, hxl]
      nlinarith
  set σ₁ := Function.update (Function.update τ zF ⟨[x], []⟩) xA ⟨[], ws⟩
  -- 2. offset words
  have s2 := runs_offLoop ws σ₁ [] [] (by tsimp [σ₁]) (by tsimp [σ₁, hB, emp]) (by tsimp [σ₁, hz])
    (fun y hy => by have := hwsw y hy; intro e; rw [e] at this; simp at this; omega)
  rw [hoffs] at s2
  set offs := arrOff w fs
  have hoffl : offs.length = N := length_arrOff w fs
  have hoffw : ∀ y ∈ offs, y.length = w := by
    intro y hy; rw [← hoffs] at hy; obtain ⟨z, hz', rfl⟩ := List.mem_map.mp hy
    rw [length_flipLast (by have := hwsw z hz'; intro e; rw [List.reverse_eq_nil_iff] at e; rw [e] at this; simp at this; omega)]
    simpa using hwsw z hz'
  set σ₂ := Function.update (Function.update σ₁ xA ⟨ws.reverse ++ [], []⟩) xB ⟨offs.reverse ++ [], []⟩
  -- 3. rewind and ticks
  have s3 : Runs phB σ₂ (· = Function.update (Function.update τ xB ⟨[], offs⟩) (ι qT) ⟨[], List.replicate D []⟩)
      (3 * N * (w + 1) + x.length + 3 * D + 40) := by
    apply Runs.of_wp
    simp only [phB, ticksFrom, WP, wp_clear, wp_rewind, wp_op0]
    tsimp [σ₂, σ₁, hS, hz, emp, reg, Rules.output_ticks, WTape.put, WTape.next, WTape.cur]
    have t1 := time_le Rules.ticks (ones D) (fun j => j.elim0) 0 (fun j => j.elim0)
    refine ⟨?_, ?_⟩
    · funext y; simp only [Function.update_apply]
      split_ifs <;> (try subst_vars) <;> tsimp [hS, hz, hA, hF, emp, reg] <;>
        simp_all (config := {decide := true})
    · have h1 : clen ws = N * (w + 1) := by rw [← hwsl]; exact clen_uniform ws w hwsw
      have h2 : clen offs = N * (w + 1) := by rw [← hoffl]; exact clen_uniform offs w hoffw
      have hb0 : Rules.ticks.B = 0 := rfl
      rw [hb0] at t1
      tsimp [WTape.words, clen_reverse, h1, h2, clen_replicate_nil] at t1 ⊢
      nlinarith
  set σ₃ := Function.update (Function.update τ xB ⟨[], offs⟩) (ι qT) ⟨[], List.replicate D []⟩
  -- 4. the passes
  have hdiv : 2 ^ (s + D) ∣ fs.length := by rw [hlen]; exact Dvd.intro c rfl
  have hoffN : offs.length = 2 * r * 2 ^ s * 2 ^ D * c := by
    rw [hoffl]; simp only [N, hlen, pow_add]; ring
  have s4 := runs_passesLoop D (2 * r * 2 ^ s) w c σ₃ offs []
    (by have := Nat.one_le_two_pow (n := s); nlinarith) hc (by tsimp [σ₃])
    (by tsimp [σ₃, hP]) (by tsimp [σ₃, hC]) (by tsimp [σ₃, hQ]) (by tsimp [σ₃]) (by tsimp [σ₃, hz])
    (by tsimp [σ₃, hz]) (by tsimp [σ₃, hrF]) (by tsimp [σ₃, hrG]) (by tsimp [σ₃, hrO]) (by tsimp [σ₃, hkW])
    hoffN hoffw
  set G := bflysRecs ((List.range D).map (s + ·)) fs
  have hpass : passes (2 * r * 2 ^ s) D offs = arrOff (w + D) G := (arrOff_bflysRecs D s w fs hw1 hdiv hb).symm
  rw [hpass] at s4
  set σ₄ := Function.update (Function.update (Function.update σ₃ xB ⟨[], arrOff (w + D) G⟩) xP
    (reg (ones (2 ^ D * (2 * r * 2 ^ s))))) (ι qT) ⟨List.replicate D [] ++ [], []⟩
  have hGl : G.length = fs.length := length_bflysRecs _ _
  set Wd := w + D
  set L := arrOff Wd G
  have hLl : L.length = N := by simp only [L, length_arrOff, hGl, N]
  have hLw : ∀ y ∈ L, y.length = Wd := by
    intro y hy
    obtain ⟨f, -, hf⟩ := List.mem_flatMap.mp hy
    obtain ⟨j, -, hj⟩ := List.mem_flatMap.mp hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl <;> simp
  have hNle : 2 ^ D * (2 * r * 2 ^ s) ≤ N := by
    have e : N = 2 * r * 2 ^ s * 2 ^ D * c := by rw [← hoffl, hoffN]
    rw [e]; nlinarith [Nat.one_le_two_pow (n := D), Nat.one_le_two_pow (n := s)]
  -- 5. drop the ticks and the ruler
  have s5 : Runs phC σ₄ (· = Function.update (Function.update τ xB ⟨[], L⟩) xP emp)
      (2 * D + 2 * N + 10) := by
    apply Runs.of_wp
    simp only [phC, WP, wp_clear]
    tsimp [σ₄, σ₃]
    refine ⟨?_, ?_⟩
    · funext y; simp only [Function.update_apply]
      split_ifs <;> (try subst_vars) <;> tsimp [hz, emp] <;> first | rfl | simp_all (config := {decide := true})
    · simp [WTape.words, reg, clen]; omega
  set σ₅ := Function.update (Function.update τ xB ⟨[], L⟩) xP emp
  -- 6. zero-extend into digits
  have s6 := runs_zextLoop L σ₅ [] [] (by tsimp [σ₅]) (by tsimp [σ₅, hz]; rfl)
  have hdig := zext_digits L hLw
  rw [hdig] at s6
  set es := L.map bval
  set σ₆ := Function.update (Function.update σ₅ xB ⟨L.reverse ++ [], []⟩) (ι tD)
    ⟨(es.map (bits (Wd + 1))).reverse ++ [], []⟩
  have s7 : Runs phD σ₆ (· = Function.update (Function.update τ (ι tD) ⟨[], es.map (bits (Wd + 1))⟩) xP emp)
      (4 * N * (Wd + 2) + 10) := by
    apply Runs.of_wp
    simp only [phD, WP, wp_clear, wp_rewind]
    tsimp [σ₆, σ₅]
    refine ⟨?_, ?_⟩
    · funext y; simp only [Function.update_apply]
      split_ifs <;> (try subst_vars) <;> tsimp [hz, hB, emp] <;> simp_all (config := {decide := true})
    · have h1 : clen L = N * (Wd + 1) := by rw [← hLl]; exact clen_uniform L Wd hLw
      have h2 : clen (es.map (bits (Wd + 1))) = N * (Wd + 2) := by
        rw [clen_uniform _ (Wd + 1) (by intro y hy; simp at hy; obtain ⟨_, _, rfl⟩ := hy; simp)]
        simp [es, hLl]
      simp [WTape.words, clen_reverse, h1, h2]; nlinarith
  set σ₇ := Function.update (Function.update τ (ι tD) ⟨[], es.map (bits (Wd + 1))⟩) xP emp
  -- 8. the digit constants
  have s8 := runs_constK (w := w) (D := D) hw1 σ₇ (by tsimp [σ₇, hW]) (by tsimp [σ₇, hS]) (by tsimp [σ₇, hz])
    (by tsimp [σ₇, hkH]) (by tsimp [σ₇, hkC])
  set σ₈ := Function.update (Function.update σ₇ kH (reg (bits (w + D + 1) (2 ^ (w + D - 1)))))
    kC (reg (bits (w + D + 1) (2 ^ D - 1)))
  -- 9. the digits
  have s9 := runs_digitLoop own_xE (show kw ≠ xE by decide) (Wd := Wd) (s := D) (w := w) es σ₈ [] []
    (by tsimp [σ₈, σ₇]) (by tsimp [σ₈, Wd]) (by tsimp [σ₈, Wd]) (by tsimp [σ₈, σ₇, hS]) (by tsimp [σ₈, σ₇, hW])
    (by tsimp [σ₈, σ₇, hz]) (by tsimp [σ₈, σ₇, hz]) (by tsimp [σ₈, σ₇, hz]) (by tsimp [σ₈, σ₇, hE]; rfl)
  set outs := es.map (outWord Wd D w)
  set σ₉ := Function.update (Function.update σ₈ (ι tD) ⟨(es.map (bits (Wd + 1))).reverse ++ [], []⟩) xE
    ⟨outs.reverse ++ [], []⟩
  have hesl : es.length = N := by simp [es, hLl]
  have houtw : ∀ y ∈ outs, y.length = w := by
    intro y hy; simp only [outs, List.mem_map] at hy; obtain ⟨e, -, rfl⟩ := hy; simp [outWord]
  have hcout : clen outs = N * (w + 1) := by rw [clen_uniform outs w houtw]; simp [outs, hesl]
  have hcL : clen L = N * (Wd + 1) := by rw [← hLl]; exact clen_uniform L Wd hLw
  have hcws : clen ws = N * (w + 1) := by rw [← hwsl]; exact clen_uniform ws w hwsw
  have s10 : Runs phE σ₉ (· = Function.update (Function.update (Function.update σ₈ (ι tD) emp) xE ⟨[], outs⟩)
      zO ⟨[[]], []⟩) (2 * N * (Wd + 2) + N * (w + 1) + 10) := by
    apply Runs.of_wp
    simp only [phE, WP, wp_clear, wp_rewind, wp_emit]
    tsimp [σ₉, σ₈, σ₇, hO, emp]
    refine ⟨?_, ?_⟩
    · funext y; simp only [Function.update_apply]
      split_ifs <;> (try subst_vars) <;> tsimp [hz, emp] <;> first | rfl | simp_all (config := {decide := true})
    · have h1 : clen outs = N * (w + 1) := by
        rw [clen_uniform outs w houtw]; simp [outs, hesl]
      have h2 : clen (es.map (bits (Wd + 1))) = N * (Wd + 2) := by
        rw [clen_uniform _ (Wd + 1) (by intro y hy; simp at hy; obtain ⟨_, _, rfl⟩ := hy; simp)]
        simp [hesl]
      tsimp [WTape.words, clen_reverse, h1, h2, clen_cons, clen_nil]; nlinarith
  set σ₁₀ := Function.update (Function.update (Function.update σ₈ (ι tD) emp) xE ⟨[], outs⟩) zO ⟨[[]], []⟩
  -- 11. join
  have s11 := runs_prJoinLoop outs σ₁₀ [] [] (by tsimp [σ₁₀]) (by tsimp [σ₁₀]) (by tsimp [σ₁₀, σ₈, σ₇, hz])
  set out := (outs.map List.reverse).flatten
  have hboundG : Bounded (2 ^ (Wd - 1) - 1) G := by
    have := bounded_bflysRecs ((List.range D).map (s + ·)) fs hb
    refine this.mono ?_
    simp only [List.length_map, List.length_range, Wd]
    have e : (2 : ℤ) ^ (w + D - 1) = 2 ^ D * 2 ^ (w - 1) := by rw [← pow_add]; congr 1; omega
    rw [e]
    have : (1 : ℤ) ≤ 2 ^ D := one_le_pow₀ (by norm_num)
    nlinarith
  have hout : out = array w (G.map (truncRec D)) := by
    rw [← join_outWords hw1 (by omega) (by omega) G hboundG]
    simp only [out, outs, es, List.map_map]; rfl
  set σ₁₁ := Function.update (Function.update σ₁₀ xE ⟨outs.reverse ++ [], []⟩) zO ⟨[[] ++ out], []⟩
  have s12 : Runs phF σ₁₁ (· = Function.update (Function.update τ zO (reg (array w (G.map (truncRec D))))) xP emp)
      (2 * N * (w + 1) + N * w + 4 * (Wd + 2) + 20) := by
    apply Runs.of_wp
    simp only [phF, WP, wp_clear, wp_rewind]
    tsimp [σ₁₁, σ₁₀, σ₈, σ₇]
    refine ⟨?_, ?_⟩
    · funext y; simp only [Function.update_apply]
      split_ifs <;> (try subst_vars) <;> tsimp [hz, emp, hkH, hkC, hE, hout, reg] <;>
        first | rfl | simp_all (config := {decide := true})
    · have hol : out.length = N * w := by
        simp only [out, List.length_flatten, List.map_map]
        have e : outs.map (List.length ∘ List.reverse) = outs.map (fun _ => w) :=
          List.map_congr_left (fun y hy => by simp [houtw y hy])
        rw [e, List.map_const', List.sum_replicate, smul_eq_mul]
        simp [outs, hesl]
      tsimp [WTape.words, clen_reverse, clen_cons, clen_nil, reg, hcout, hol]
      simp only [Wd]; nlinarith
  refine (Runs.then s1 (Runs.then s2 (Runs.then s3 (Runs.then s4 (Runs.then s5 (Runs.then s6 (Runs.then s7
    (Runs.then s8 (Runs.then s9 (Runs.then s10 (Runs.then s11 s12))))))))))).mono (fun σ h => h) ?_
  have hol' : outs.length = N := by simp [outs, hesl]
  rw [hwsl, hcws, hoffl, hLl, hcL, hesl, hol', hcout, hxl]
  unfold prefixCost
  simp only [Wd]
  nlinarith

/-! ### The paper's prefix round -/

theorem bounded_of_disk {r p w : ℕ} (hpw : p + 2 ≤ w) {fs : List (Rec r)} (hd : ∀ f ∈ fs, DiskGrid p f.1 f.2) :
    Bounded (2 ^ (w - 1) - 1) fs := by
  intro y c
  have hle : (2 : ℤ) ^ p ≤ 2 ^ (w - 1) - 1 := by
    have : (2 : ℤ) ^ (w - 1) = 2 ^ (w - 1 - p) * 2 ^ p := by rw [← pow_add]; congr 1; omega
    rw [this]
    have h1 : (2 : ℤ) ≤ 2 ^ (w - 1 - p) := by
      calc (2 : ℤ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (w - 1 - p) := pow_le_pow_right₀ (by norm_num) (by omega)
    have h2 : (1 : ℤ) ≤ 2 ^ p := one_le_pow₀ (by norm_num)
    nlinarith
  by_cases hy : y < fs.length
  · rw [List.getD_eq_getElem _ _ hy]
    have hf := hd _ (List.getElem_mem hy)
    unfold comp
    split_ifs with h1 h2
    · exact (hf.abs_le _).1.trans hle
    · exact (hf.abs_le _).2.trans hle
    · simp; linarith [one_le_pow₀ (M₀ := ℤ) (a := 2) (n := p) (by norm_num)]
  · rw [List.getD_eq_default _ _ (by omega), comp_zero, abs_zero]
    linarith [one_le_pow₀ (M₀ := ℤ) (a := 2) (n := p) (by norm_num)]

/-- In the paper's layout, the prefix round's machine meets its preconditions, and twisting its output by
the round's exponents is the computed round. -/
theorem prefix_had_spec {r : ℕ} [NeZero r] {ts : List ℕ} {ℓ K : ℕ} (hL : LayoutOK r ts ℓ K) {h : ℕ}
    (hh : h < (ℓ - 1) % K) {p w : ℕ} (hpw : p + 2 ≤ w) (fs : List (Rec r)) (hlen : fs.length = ts.prod)
    (hd : ∀ f ∈ fs, DiskGrid p f.1 f.2) :
    Bounded (2 ^ (w - 1) - 1) fs ∧
      (∃ c, 1 ≤ c ∧ fs.length = 2 ^ (prefixBase ts.length ℓ K h + ts.length) * c) ∧
      twist (slotExp (paperPerm hL) r ts (slotAxes ts h) h)
        (arrayVec p ((bflysRecs ((List.range ts.length).map (prefixBase ts.length ℓ K h + ·)) fs).map
          (truncRec ts.length))) = roundArr p (slotRound (paperPerm hL) ts h (arrayVec p fs)) := by
  refine ⟨bounded_of_disk hpw hd, ?_, (prefix_round_eq hL hh p fs hlen).symm⟩
  obtain ⟨-, hM⟩ := axes_zeros (ts := ts) (fun t ht => by obtain ⟨a, ha, -⟩ := hL.1 t ht; exact ⟨a, ha⟩)
  set D := ts.length
  have hlog : Nat.log 2 ts.prod = D * ((ℓ - 1) / K) * K + D * ((ℓ - 1) % K) + (longs ts ℓ).length :=
    log_prod_layout hL
  have hle : prefixBase D ℓ K h + D ≤ Nat.log 2 ts.prod := by
    have hb1 : (h + 1) * D ≤ ((ℓ - 1) % K) * D := Nat.mul_le_mul_right _ (by omega)
    have e1 : (h + 1) * D = h * D + D := by ring
    have e2 : D * ((ℓ - 1) % K) = ((ℓ - 1) % K) * D := Nat.mul_comm _ _
    simp only [prefixBase]
    omega
  refine ⟨2 ^ (Nat.log 2 ts.prod - (prefixBase D ℓ K h + D)), Nat.one_le_two_pow, ?_⟩
  rw [hlen, ← pow_add]
  conv_lhs => rw [hM]
  congr 1
  omega

/-- The exact butterflies of prefix slot `h` on any array of the right length, rounded once. -/
theorem prefix_bflys_eq {r : ℕ} [NeZero r] {ts : List ℕ} {ℓ K : ℕ} (hL : LayoutOK r ts ℓ K) {h : ℕ}
    (hh : h < (ℓ - 1) % K) (p : ℕ) (gs : List (Rec r)) (hlen : gs.length = ts.prod) :
    roundArr p (bflys (slotBits (paperPerm hL) ts (slotAxes ts h) h) (arrayVec p gs)) =
      arrayVec p ((bflysRecs ((List.range ts.length).map (prefixBase ts.length ℓ K h + ·)) gs).map
        (truncRec ts.length)) := by
  have := prefix_round_eq hL hh p gs hlen
  unfold slotRound at this
  rw [roundArr_twist] at this
  have hinj : Function.Injective (twist (r := r) (slotExp (paperPerm hL) r ts (slotAxes ts h) h)) := by
    intro a b e
    rw [← untwist_twist (slotExp (paperPerm hL) r ts (slotAxes ts h) h) a, e, untwist_twist]
  exact hinj this

/-- The opposite round of prefix slot `h`: untwist the records, then the same butterflies and truncation. -/
theorem prefix_opp_round_eq {r : ℕ} [NeZero r] {ts : List ℕ} {ℓ K : ℕ} (hL : LayoutOK r ts ℓ K) {h : ℕ}
    (hh : h < (ℓ - 1) % K) (p : ℕ) (fs : List (Rec r)) (hlen : fs.length = ts.prod) :
    roundArr p (oppSlotRound (paperPerm hL) ts h (arrayVec p fs)) =
      arrayVec p ((bflysRecs ((List.range ts.length).map (prefixBase ts.length ℓ K h + ·))
        (TwistRound.untwistRecs (slotExp (paperPerm hL) r ts (slotAxes ts h) h) fs)).map (truncRec ts.length)) := by
  unfold oppSlotRound
  rw [← TwistRound.arrayVec_untwist]
  exact prefix_bflys_eq hL hh p _ (by simp [TwistRound.untwistRecs, hlen])

end IntegerMultBounds.Schoenhage
