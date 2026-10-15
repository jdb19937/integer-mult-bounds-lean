module

public import IntegerMultBounds.MathlibTM2.Node.CompactTopProcRegs

/-! Actual descent, whole-row padding, unpadding and ascent for arbitrary
basis banks. Persistent basis-rest predicates are retained across all stages. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds IntegerMultBounds.Networks IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Layer
open IntegerMultBounds.MathlibTM2.Node hiding LReg
noncomputable section
variable {BReg : Type} [Fintype BReg] {A Q : ℕ} {U P : Type}
variable {bc : BReg → List (Fin (A+4)) → Prop}
variable (body : P → Pr P (nT BReg) Q A U)

local macro "compactTopRowsFupd" : tactic => `(tactic| (simp only [Function.update_apply, reg_inj,
  reduceCtorEq, ↓reduceIte, eq_self_iff_true, LReg.sc.injEq, LReg.ph.injEq, LReg.lf.injEq,
  IntegerMultBounds.MathlibTM2.Node.LReg.k.injEq, Fin.reduceEq, Fin.isValue]))

/-- The registers for the pieces: `a` symbols of `n` on `st`, `rowctr` on `cs`, `rowctr` rebuilt
with `2^n r w` symbols, the address fields `binSyms n 0`. -/
noncomputable def compactTopDownR (Rg : Fin (nT BReg) → List (Fin (A + 4))) (a n r w : ℕ) :
    Fin (nT BReg) → List (Fin (A + 4)) :=
  Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update Rg (reg .n) ((Rg (reg .n)).drop a)) (reg .st) ((Rg (reg .n)).take a).reverse)
    (reg (.ph .af)) (binSyms n 0)) (reg (.lf (.k .cf))) (binSyms n 0)) (reg .cs)
    (Rg (reg .rowctr)).reverse) (reg .rowctr)
    ((List.replicate (r * w) tick).flatMap (List.replicate (2 ^ n)))

/-- `compactTopDownR` keeps every register outside `n`, `st`, `ph .af`, `lf (.k .cf)`, `cs`, `rowctr`. -/
lemma compactTopDownR_of_ne {Rg : Fin (nT BReg) → List (Fin (A + 4))} {a n r w : ℕ} {x : LReg BReg}
    (h1 : x ≠ .n) (h2 : x ≠ .st) (h3 : x ≠ .ph .af) (h4 : x ≠ .lf (.k .cf)) (h5 : x ≠ .cs)
    (h6 : x ≠ .rowctr) : compactTopDownR Rg a n r w (reg x) = Rg (reg x) := by
  simp [compactTopDownR, h1, h2, h3, h4, h5, h6]

lemma compactTopDownR_par {Rg : Fin (nT BReg) → List (Fin (A + 4))} {a n r w : ℕ} {x : LReg BReg}
    (hx : x ∈ [LReg.lev, .u, .a₀, .L, .rows, .w, .rw, .K, .ρ]) :
    compactTopDownR Rg a n r w (reg x) = Rg (reg x) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact compactTopDownR_of_ne (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)

lemma compactTopDownR_regs {Rg : Fin (nT BReg) → List (Fin (A + 4))} {n a r w K ρ : ℕ}
    (hT : CompactTopRegs bc Rg (n + a) r w K ρ) : CompactTopRegs bc (compactTopDownR Rg a n r w) n r w K ρ where
  rest := fun x => by
    by_cases h1 : x = .n
    · subst h1; trivial
    by_cases h2 : x = .st
    · subst h2; trivial
    by_cases h3 : x = .ph .af
    · subst h3; simp [compactTopDownR, restSpec, phRest]
    by_cases h4 : x = .lf (.k .cf)
    · subst h4; simp [compactTopDownR, restSpec, lfRest]
    by_cases h5 : x = .cs
    · subst h5; trivial
    by_cases h6 : x = .rowctr
    · subst h6
      simp [compactTopDownR, restSpec]
      ring
    rw [compactTopDownR_of_ne h1 h2 h3 h4 h5 h6]
    exact (compactTopRestSpec_bits h3 h4 h6).1 (hT.rest x)
  hlev := by rw [compactTopDownR_par (by simp)]; exact hT.hlev
  hu := by rw [compactTopDownR_par (by simp)]; exact hT.hu
  ha₀ := by rw [compactTopDownR_par (by simp)]; exact hT.ha₀
  hL := by rw [compactTopDownR_par (by simp)]; exact hT.hL
  hrows := by rw [compactTopDownR_par (by simp)]; exact hT.hrows
  hn := by simp [compactTopDownR, hT.hn]
  hw := by rw [compactTopDownR_par (by simp)]; exact hT.hw
  hrw := by rw [compactTopDownR_par (by simp)]; exact hT.hrw
  hK := by rw [compactTopDownR_par (by simp)]; exact hT.hK
  hρ := by rw [compactTopDownR_par (by simp)]; exact hT.hρ

/-- From the rest state for `n + a` address bits to the one for `n` (`a` from field `2`). -/
noncomputable def compactTopDownS : Pr P (nT BReg) Q A U :=
  .seq (compactTopRd (reg (.sc 0)) 2)
  (.seq (Shift.counted (reg (.sc 0)) (reg (.sc 3)) (Shift.copyStep (reg (.sc 0)) (reg (.sc 3))
      (reg .n) (reg .st)))
  (.seq (usub (reg (.sc 0)) (reg (.ph .af)) (reg (.sc 3)))
  (.seq (usub (reg (.sc 0)) (reg (.lf (.k .cf))) (reg (.sc 3)))
  (.seq (moveR (reg .rowctr) (reg .cs) id)
  (.seq (ucopy (reg .rw) (reg .rowctr) (reg (.sc 3)))
  (.seq (upow2 (reg .n) (reg .rowctr) (reg (.sc 4)) (reg (.sc 5)))
    (uclear (reg (.sc 0)))))))))

/-- The step bound of `compactTopDownS`. -/
def compactTopDownCost (cfg : List ℕ) (n a r w : ℕ) : ℕ :=
  topGetCost cfg + (4 * a + 4) + (4 * a + 4) + (4 * a + 4) + (2 * (2 ^ (n + a) * r * w) + 2) +
    (4 * (r * w) + 4) + (4 * (2 ^ n * (r * w)) + 9 * n + 4) + (2 * a + 2)

theorem compactTopDownS_exec {cfg pfs : List ℕ} {n a r w K ρ : ℕ} (h2 : cfg[2]? = some a)
    (v : HS (nT BReg) Q A U) (S : Stacks (nT BReg) A) (hT : CompactTopRegs bc S.R (n + a) r w K ρ)
    (hI : CompactTopIn (BReg := BReg) S.R cfg pfs) :
    ∃ (v' : HS (nT BReg) Q A U) (c : ℕ), v'.user = v.user ∧ c ≤ compactTopDownCost cfg n a r w ∧
      Exec body compactTopDownS (mk v S) c (mk v' { S with R := compactTopDownR S.R a n r w }) := by
  have hl2 : 2 < cfg.length := (List.getElem?_eq_some_iff.1 h2).1
  have hc2 : cfg[2] = a := (List.getElem?_eq_some_iff.1 h2).2
  have hsc : ∀ i, S.R (reg (.sc i)) = [] := fun i => hT.rest (.sc i)
  have hlc : S.R (reg .lenctr) = [] := hT.rest .lenctr
  set ln := S.R (reg .n) with hln
  set lr := S.R (reg .rowctr) with hlr
  have hlnl : ln.length = n + a := hT.hn
  have hlrl : lr.length = 2 ^ (n + a) * r * w := hT.rest .rowctr
  have haf : S.R (reg (.ph .af)) = List.replicate (n + a) (bitSymbol false) := by
    rw [← binSyms_zero_right]; exact hT.rest (.ph .af)
  have hcf : S.R (reg (.lf (.k .cf))) = List.replicate (n + a) (bitSymbol false) := by
    rw [← binSyms_zero_right]; exact hT.rest (.lf (.k .cf))
  obtain ⟨v₁, c₁, hu₁, hc₁, e₁⟩ := compactTopRd_exec body (x := .sc 0) (by simp) (by simp) 2 hl2 v S
    hlc hI.cf
  rw [hc2, hsc 0, List.append_nil] at e₁
  set R₁ := Function.update S.R (reg (.sc 0)) (List.replicate a tick) with hR₁
  obtain ⟨v₂, hv₂, e₂⟩ := topCopyC_exec body (c := reg (.sc 0)) (t := reg (.sc 3))
    (src := reg .n) (dst := reg .st) (nodup_map_reg (l := [.sc 0, .sc 3, .n, .st]) (by simp))
    (ln.take a) (ln.drop a) v₁ { S with R := R₁ } (by simp [hR₁, hlnl])
    (by simp [hR₁, hln]) (by simp [hR₁, hsc])
  rw [show (ln.take a).length = a by simp [hlnl]] at e₂
  set R₂ := Function.update (Function.update R₁ (reg .n) (ln.drop a)) (reg .st)
    ((ln.take a).reverse ++ R₁ (reg .st)) with hR₂
  obtain ⟨v₃, hu₃, e₃⟩ := usub_exec body (a := reg (.sc 0)) (b := reg (.ph .af)) (t := reg (.sc 3))
    (reg_ne (by simp)) (reg_ne (by simp)) (reg_ne (by simp)) v₂ { S with R := R₂ }
    (by simp [hR₂, hR₁, hsc])
  dsimp only at e₃
  rw [show (R₂ (reg (.sc 0))).length = a by simp [hR₂, hR₁],
    show R₂ (reg (.ph .af)) = List.replicate (n + a) (bitSymbol false) by simp [hR₂, hR₁, haf],
    List.drop_replicate, Nat.add_sub_cancel, ← binSyms_zero_right] at e₃
  set R₃ := Function.update R₂ (reg (.ph .af)) (binSyms n 0) with hR₃
  obtain ⟨v₄, hu₄, e₄⟩ := usub_exec body (a := reg (.sc 0)) (b := reg (.lf (.k .cf)))
    (t := reg (.sc 3)) (reg_ne (by simp)) (reg_ne (by simp)) (reg_ne (by simp)) v₃
    { S with R := R₃ } (by simp [hR₃, hR₂, hR₁, hsc])
  dsimp only at e₄
  rw [show (R₃ (reg (.sc 0))).length = a by simp [hR₃, hR₂, hR₁],
    show R₃ (reg (.lf (.k .cf))) = List.replicate (n + a) (bitSymbol false) by
      simp [hR₃, hR₂, hR₁, hcf],
    List.drop_replicate, Nat.add_sub_cancel, ← binSyms_zero_right] at e₄
  set R₄ := Function.update R₃ (reg (.lf (.k .cf))) (binSyms n 0) with hR₄
  obtain ⟨v₅, hu₅, e₅⟩ := moveR_exec body (reg .rowctr) (reg .cs) (reg_ne (by simp)) id v₄
    { S with R := R₄ }
  dsimp only at e₅
  have hR₄r : R₄ (reg .rowctr) = lr := by simp [hR₄, hR₃, hR₂, hR₁, hlr]
  rw [hR₄r] at e₅
  set R₅ := movedR R₄ (reg .rowctr) (reg .cs) id lr with hR₅
  obtain ⟨v₆, hu₆, e₆⟩ := ucopy_exec body (a := reg .rw) (b := reg .rowctr) (t := reg (.sc 3))
    (reg_ne (by simp)) (reg_ne (by simp)) (reg_ne (by simp)) v₅ { S with R := R₅ }
    (by simp [hR₅, movedR, hR₄, hR₃, hR₂, hR₁, hsc])
  dsimp only at e₆
  rw [show (R₅ (reg .rw)).length = r * w by simp [hR₅, movedR, hR₄, hR₃, hR₂, hR₁]; exact hT.hrw,
    show R₅ (reg .rowctr) = [] by simp [hR₅, movedR], List.append_nil] at e₆
  set R₆ := Function.update R₅ (reg .rowctr) (List.replicate (r * w) tick) with hR₆
  obtain ⟨v₇, m₇, hu₇, hm₇, e₇⟩ := upow2_exec body (a := reg .n) (b := reg .rowctr)
    (t₁ := reg (.sc 4)) (t₂ := reg (.sc 5)) (nodup_map_reg (l := [.n, .rowctr, .sc 4, .sc 5])
      (by simp)) v₆ { S with R := R₆ } (by simp [hR₆, hR₅, movedR, hR₄, hR₃, hR₂, hR₁, hsc])
    (by simp [hR₆, hR₅, movedR, hR₄, hR₃, hR₂, hR₁, hsc])
  dsimp only at e₇ hm₇
  have hn₆ : (R₆ (reg .n)).length = n := by
    simp [hR₆, hR₅, movedR, hR₄, hR₃, hR₂, hlnl]
  have hr₆ : R₆ (reg .rowctr) = List.replicate (r * w) tick := by simp [hR₆]
  rw [hn₆, hr₆] at e₇ hm₇
  set R₇ := Function.update R₆ (reg .rowctr)
    ((List.replicate (r * w) tick).flatMap (List.replicate (2 ^ n))) with hR₇
  obtain ⟨v₈, hu₈, e₈⟩ := uclear_exec body (reg (.sc 0)) v₇ { S with R := R₇ }
  refine ⟨v₈, _, by rw [hu₈, hu₇, hu₆, hu₅, hu₄, hu₃, hv₂.user, hu₁], ?_,
    Exec.cast (Exec.seq e₁ (Exec.seq e₂ (Exec.seq e₃ (Exec.seq e₄ (Exec.seq e₅ (Exec.seq e₆
      (Exec.seq e₇ e₈))))))) rfl ?_⟩
  · have h0 : (R₇ (reg (.sc 0))).length = a := by
      simp [hR₇, hR₆, hR₅, movedR, hR₄, hR₃, hR₂, hR₁]
    rw [h0]
    simp only [List.length_replicate] at hm₇
    unfold compactTopDownCost
    rw [hlrl]
    nlinarith [hc₁, hm₇]
  · congr 2
    funext k
    by_cases h0 : k = reg (.sc 0)
    · subst h0; simp [compactTopDownR, hsc]
    rw [Function.update_of_ne h0]
    by_cases h1 : k = reg .rowctr
    · subst h1; simp [hR₇, compactTopDownR]
    by_cases h2 : k = reg .cs
    · subst h2
      simp [hR₇, hR₆, hR₅, movedR, compactTopDownR, hI.y, hR₄, hR₃, hR₂, hR₁, hlr]
    by_cases h3 : k = reg (.lf (.k .cf))
    · subst h3; simp [hR₇, hR₆, hR₅, movedR, hR₄, compactTopDownR]
    by_cases h4 : k = reg (.ph .af)
    · subst h4; simp [hR₇, hR₆, hR₅, movedR, hR₄, hR₃, compactTopDownR]
    by_cases h5 : k = reg .st
    · subst h5; simp [hR₇, hR₆, hR₅, movedR, hR₄, hR₃, hR₂, compactTopDownR, hI.x, hR₁, hln]
    by_cases h6 : k = reg .n
    · subst h6; simp [hR₇, hR₆, hR₅, movedR, hR₄, hR₃, hR₂, compactTopDownR, hln]
    simp [hR₇, hR₆, hR₅, movedR, hR₄, hR₃, hR₂, hR₁, compactTopDownR,
      h0, h1, h2, h3, h4, h5, h6]

/-- Back to the rest state for `n + a` address bits. -/
noncomputable def compactTopUpS : Pr P (nT BReg) Q A U :=
  .seq (compactTopRd (reg (.sc 0)) 2)
  (.seq (uclear (reg .rowctr))
  (.seq (moveR (reg .cs) (reg .rowctr) id)
  (.seq (zeroBits (reg (.sc 0)) (reg (.ph .af)) (reg (.sc 3)))
  (.seq (zeroBits (reg (.sc 0)) (reg (.lf (.k .cf))) (reg (.sc 3)))
  (.seq (moveR (reg .st) (reg .n) id) (uclear (reg (.sc 0))))))))

/-- The step bound of `compactTopUpS`. -/
def compactTopUpCost (cfg : List ℕ) (n a r w : ℕ) : ℕ :=
  topGetCost cfg + (2 * (2 ^ n * (r * w)) + 2) + (2 * (2 ^ (n + a) * r * w) + 2) + (4 * a + 4) +
    (4 * a + 4) + (2 * a + 2) + (2 * a + 2)

theorem compactTopUpS_exec {cfg pfs : List ℕ} {n a r w K ρ : ℕ} (h2 : cfg[2]? = some a)
    (v : HS (nT BReg) Q A U) (S : Stacks (nT BReg) A) (hT : CompactTopRegs bc S.R (n + a) r w K ρ)
    (hI : CompactTopIn (BReg := BReg) S.R cfg pfs) (X : List (Fin (A + 4))) :
    ∃ (v' : HS (nT BReg) Q A U) (c : ℕ), v'.user = v.user ∧ c ≤ compactTopUpCost cfg n a r w ∧
      Exec body compactTopUpS (mk v { S with R := Function.update (compactTopDownR S.R a n r w) (reg .io) X }) c
        (mk v' { S with R := Function.update S.R (reg .io) X }) := by
  have hl2 : 2 < cfg.length := (List.getElem?_eq_some_iff.1 h2).1
  have hc2 : cfg[2] = a := (List.getElem?_eq_some_iff.1 h2).2
  have hsc : ∀ i, S.R (reg (.sc i)) = [] := fun i => hT.rest (.sc i)
  have hlc : S.R (reg .lenctr) = [] := hT.rest .lenctr
  set ln := S.R (reg .n) with hln
  set lr := S.R (reg .rowctr) with hlr
  have hlnl : ln.length = n + a := hT.hn
  have hlrl : lr.length = 2 ^ (n + a) * r * w := hT.rest .rowctr
  have haf : S.R (reg (.ph .af)) = List.replicate (n + a) (bitSymbol false) := by
    rw [← binSyms_zero_right]; exact hT.rest (.ph .af)
  have hcf : S.R (reg (.lf (.k .cf))) = List.replicate (n + a) (bitSymbol false) := by
    rw [← binSyms_zero_right]; exact hT.rest (.lf (.k .cf))
  set Rd := Function.update (compactTopDownR S.R a n r w) (reg .io) X with hRd
  obtain ⟨v₁, c₁, hu₁, hc₁, e₁⟩ := compactTopRd_exec body (x := .sc 0) (by simp) (by simp) 2 hl2 v
    { S with R := Rd } (by simp [hRd, compactTopDownR, hlc]) (by simpa [hRd, compactTopDownR] using hI.cf)
  dsimp only at e₁
  rw [hc2, show Rd (reg (.sc 0)) = [] by simp [hRd, compactTopDownR, hsc], List.append_nil] at e₁
  set R₁ := Function.update Rd (reg (.sc 0)) (List.replicate a tick) with hR₁
  obtain ⟨v₂, hu₂, e₂⟩ := uclear_exec body (reg .rowctr) v₁ { S with R := R₁ }
  dsimp only at e₂
  set R₂ := Function.update R₁ (reg .rowctr) [] with hR₂
  obtain ⟨v₃, hu₃, e₃⟩ := moveR_exec body (reg .cs) (reg .rowctr) (reg_ne (by simp)) id v₂
    { S with R := R₂ }
  dsimp only at e₃
  have hR₂c : R₂ (reg .cs) = lr.reverse := by simp [hR₂, hR₁, hRd, compactTopDownR, hlr]
  rw [hR₂c] at e₃
  set R₃ := movedR R₂ (reg .cs) (reg .rowctr) id lr.reverse with hR₃
  obtain ⟨v₄, hu₄, e₄⟩ := zeroBits_exec body (len := reg (.sc 0)) (z := reg (.ph .af))
    (t := reg (.sc 3)) (reg_ne (by simp)) (reg_ne (by simp)) (reg_ne (by simp)) v₃
    { S with R := R₃ } (by simp [hR₃, movedR, hR₂, hR₁, hRd, compactTopDownR, hsc])
  dsimp only at e₄
  have hR₃0 : (R₃ (reg (.sc 0))).length = a := by simp [hR₃, movedR, hR₂, hR₁]
  rw [hR₃0, show R₃ (reg (.ph .af)) = binSyms n 0 by
    simp [hR₃, movedR, hR₂, hR₁, hRd, compactTopDownR]] at e₄
  set R₄ := Function.update R₃ (reg (.ph .af)) (binSyms a 0 ++ binSyms n 0) with hR₄
  obtain ⟨v₅, hu₅, e₅⟩ := zeroBits_exec body (len := reg (.sc 0)) (z := reg (.lf (.k .cf)))
    (t := reg (.sc 3)) (reg_ne (by simp)) (reg_ne (by simp)) (reg_ne (by simp)) v₄
    { S with R := R₄ } (by simp [hR₄, hR₃, movedR, hR₂, hR₁, hRd, compactTopDownR, hsc])
  dsimp only at e₅
  rw [show (R₄ (reg (.sc 0))).length = a by simp [hR₄, hR₃, movedR, hR₂, hR₁],
    show R₄ (reg (.lf (.k .cf))) = binSyms n 0 by
      simp [hR₄, hR₃, movedR, hR₂, hR₁, hRd, compactTopDownR]] at e₅
  set R₅ := Function.update R₄ (reg (.lf (.k .cf))) (binSyms a 0 ++ binSyms n 0) with hR₅
  obtain ⟨v₆, hu₆, e₆⟩ := moveR_exec body (reg .st) (reg .n) (reg_ne (by simp)) id v₅
    { S with R := R₅ }
  dsimp only at e₆
  have hR₅s : R₅ (reg .st) = (ln.take a).reverse := by
    simp [hR₅, hR₄, hR₃, movedR, hR₂, hR₁, hRd, compactTopDownR, hln]
  rw [hR₅s] at e₆
  set R₆ := movedR R₅ (reg .st) (reg .n) id (ln.take a).reverse with hR₆
  obtain ⟨v₇, hu₇, e₇⟩ := uclear_exec body (reg (.sc 0)) v₆ { S with R := R₆ }
  refine ⟨v₇, _, by rw [hu₇, hu₆, hu₅, hu₄, hu₃, hu₂, hu₁], ?_,
    Exec.cast (Exec.seq e₁ (Exec.seq e₂ (Exec.seq e₃ (Exec.seq e₄ (Exec.seq e₅ (Exec.seq e₆
      e₇)))))) rfl ?_⟩
  · have h1 : (R₁ (reg .rowctr)).length = 2 ^ n * (r * w) := by
      simp [hR₁, hRd, compactTopDownR]; ring
    have h6 : (R₆ (reg (.sc 0))).length = a := by simp [hR₆, movedR, hR₅, hR₄, hR₃, hR₂, hR₁]
    rw [h1, h6]
    simp only [List.length_reverse, List.length_take, hlnl, hlrl]
    unfold compactTopUpCost
    have : min a (n + a) = a := by omega
    rw [this]
    omega
  · congr 2
    funext k
    by_cases h0 : k = reg (.sc 0)
    · subst h0; simp [hsc]
    rw [Function.update_of_ne h0]
    by_cases h1 : k = reg .n
    · subst h1
      simp [hR₆, movedR, hR₅, hR₄, hR₃, hR₂, hR₁, hRd, compactTopDownR, hln]
    by_cases h2 : k = reg .st
    · subst h2; simp [hR₆, movedR, hI.x]
    by_cases h3 : k = reg (.lf (.k .cf))
    · subst h3
      simp [hR₆, movedR, hR₅, hcf, binSyms_zero_right, List.replicate_append_replicate,
        Nat.add_comm]
    by_cases h4 : k = reg (.ph .af)
    · subst h4
      simp [hR₆, movedR, hR₅, hR₄, haf, binSyms_zero_right, List.replicate_append_replicate,
        Nat.add_comm]
    by_cases h5 : k = reg .rowctr
    · subst h5; simp [hR₆, movedR, hR₅, hR₄, hR₃, hR₂, hlr]
    by_cases h6 : k = reg .cs
    · subst h6; simp [hR₆, movedR, hR₅, hR₄, hR₃, hI.y]
    by_cases h7 : k = reg .io
    · subst h7; simp [hR₆, movedR, hR₅, hR₄, hR₃, hR₂, hR₁, hRd]
    simp only [hR₆, movedR, hR₅, hR₄, hR₃, hR₂, hR₁, hRd, Function.update_apply, h0, h1, h2, h3,
      h4, h5, h6, h7, ↓reduceIte]
    obtain ⟨x, rfl⟩ := (regEquiv BReg).surjective k
    exact compactTopDownR_of_ne (fun h => h1 (by rw [h]; rfl)) (fun h => h2 (by rw [h]; rfl))
      (fun h => h4 (by rw [h]; rfl)) (fun h => h3 (by rw [h]; rfl)) (fun h => h6 (by rw [h]; rfl))
      (fun h => h5 (by rw [h]; rfl))

/-! ### Padding and unpadding rows -/

/-- Pad to `R₂` rows (field `4`) from `R 2^a` rows (fields `3`, `2`): `io` moved onto `racc`,
`(R₂ - R 2^a) · |rowctr|` zero pairs pushed onto `io`, `racc` moved back. -/
noncomputable def compactTopPadS : Pr P (nT BReg) Q A U :=
  .seq (compactTopRd (reg (.sc 0)) 2)
  (.seq (compactTopRd (reg (.sc 1)) 3)
  (.seq (upow2 (reg (.sc 0)) (reg (.sc 1)) (reg (.sc 4)) (reg (.sc 5)))
  (.seq (compactTopRd (reg (.sc 2)) 4)
  (.seq (usub (reg (.sc 1)) (reg (.sc 2)) (reg (.sc 3)))
  (.seq (moveR (reg .io) (reg .racc) id)
  (.seq (scanP (reg (.sc 2)) (reg (.sc 3))
      (umulSym 1 (pairSym A false false) (reg .rowctr) (reg .io) (reg (.sc 4))))
  (.seq (moveR (reg .racc) (reg .io) id)
  (.seq (uclear (reg (.sc 0))) (.seq (uclear (reg (.sc 1))) (uclear (reg (.sc 2))))))))))))

/-- The step bound of `compactTopPadS` with `V` symbols on `io` and rows of `L` symbols. -/
def compactTopPadCost (cfg : List ℕ) (a R R₂ L V : ℕ) : ℕ :=
  3 * topGetCost cfg + (4 * (2 ^ a * R) + 9 * a + 4) + (4 * (2 ^ a * R) + 4) + (2 * V + 2) +
    ((R₂ - 2 ^ a * R) * (4 * L + 7) + 2 * (R₂ - 2 ^ a * R) + 4) + (2 * V + 2) + (2 * a + 2) +
    (2 * (2 ^ a * R) + 2) + (2 * (R₂ - 2 ^ a * R) + 2)

theorem compactTopPadS_exec {cfg : List ℕ} {n a R R₂ r w K ρ : ℕ} (h2 : cfg[2]? = some a)
    (h3 : cfg[3]? = some R) (h4 : cfg[4]? = some R₂) (v : HS (nT BReg) Q A U)
    (S : Stacks (nT BReg) A) (hT : CompactTopRegs bc S.R n r w K ρ)
    (hcf : ∃ rest, S.R (reg .park) = topRec cfg ++ rest) :
    ∃ (v' : HS (nT BReg) Q A U) (c : ℕ), v'.user = v.user ∧
      c ≤ compactTopPadCost cfg a R R₂ (2 ^ n * r * w) (S.R (reg .io)).length ∧
      Exec body compactTopPadS (mk v S) c
        (mk v' { S with
          R := Function.update S.R (reg .io) (S.R (reg .io) ++
            List.replicate ((R₂ - 2 ^ a * R) * (2 ^ n * r * w)) (pairSym A false false)) }) := by
  have hl2 : 2 < cfg.length := (List.getElem?_eq_some_iff.1 h2).1
  have hl3 : 3 < cfg.length := (List.getElem?_eq_some_iff.1 h3).1
  have hl4 : 4 < cfg.length := (List.getElem?_eq_some_iff.1 h4).1
  have hc2 : cfg[2] = a := (List.getElem?_eq_some_iff.1 h2).2
  have hc3 : cfg[3] = R := (List.getElem?_eq_some_iff.1 h3).2
  have hc4 : cfg[4] = R₂ := (List.getElem?_eq_some_iff.1 h4).2
  have hsc : ∀ i, S.R (reg (.sc i)) = [] := fun i => hT.rest (.sc i)
  have hlc : S.R (reg .lenctr) = [] := hT.rest .lenctr
  have hracc : S.R (reg .racc) = [] := hT.rest .racc
  have hrow : (S.R (reg .rowctr)).length = 2 ^ n * r * w := hT.rest .rowctr
  set Xs := S.R (reg .io) with hXs
  set L := 2 ^ n * r * w with hL
  obtain ⟨v₁, c₁, hu₁, hc₁, e₁⟩ := compactTopRd_exec body (x := .sc 0) (by simp) (by simp) 2 hl2 v S
    hlc hcf
  rw [hc2, hsc 0, List.append_nil] at e₁
  set R₁ := Function.update S.R (reg (.sc 0)) (List.replicate a tick) with hR₁
  obtain ⟨v₂, c₂, hu₂, hc₂, e₂⟩ := compactTopRd_exec body (x := .sc 1) (by simp) (by simp) 3 hl3 v₁
    { S with R := R₁ } (by simp [hR₁, hlc]) (by simpa [hR₁] using hcf)
  dsimp only at e₂
  rw [hc3, show R₁ (reg (.sc 1)) = [] by simp [hR₁, hsc], List.append_nil] at e₂
  set R₂' := Function.update R₁ (reg (.sc 1)) (List.replicate R tick) with hR₂'
  obtain ⟨v₃, m₃, hu₃, hm₃, e₃⟩ := upow2_exec body (a := reg (.sc 0)) (b := reg (.sc 1))
    (t₁ := reg (.sc 4)) (t₂ := reg (.sc 5)) (nodup_map_reg (l := [.sc 0, .sc 1, .sc 4, .sc 5])
      (by simp)) v₂ { S with R := R₂' } (by simp [hR₂', hR₁, hsc]) (by simp [hR₂', hR₁, hsc])
  dsimp only at e₃ hm₃
  rw [show R₂' (reg (.sc 0)) = List.replicate a tick by simp [hR₂', hR₁],
    show R₂' (reg (.sc 1)) = List.replicate R tick by simp [hR₂'], List.length_replicate] at e₃ hm₃
  set R₃ := Function.update R₂' (reg (.sc 1))
    ((List.replicate R tick).flatMap (List.replicate (2 ^ a))) with hR₃
  have h3l : (R₃ (reg (.sc 1))).length = 2 ^ a * R := by
    simp [hR₃]; ring
  obtain ⟨v₄, c₄, hu₄, hc₄, e₄⟩ := compactTopRd_exec body (x := .sc 2) (by simp) (by simp) 4 hl4 v₃
    { S with R := R₃ } (by simp [hR₃, hR₂', hR₁, hlc]) (by simpa [hR₃, hR₂', hR₁] using hcf)
  dsimp only at e₄
  rw [hc4, show R₃ (reg (.sc 2)) = [] by simp [hR₃, hR₂', hR₁, hsc], List.append_nil] at e₄
  set R₄ := Function.update R₃ (reg (.sc 2)) (List.replicate R₂ tick) with hR₄
  obtain ⟨v₅, hu₅, e₅⟩ := usub_exec body (a := reg (.sc 1)) (b := reg (.sc 2)) (t := reg (.sc 3))
    (reg_ne (by simp)) (reg_ne (by simp)) (reg_ne (by simp)) v₄ { S with R := R₄ }
    (by simp [hR₄, hR₃, hR₂', hR₁, hsc])
  dsimp only at e₅
  rw [show (R₄ (reg (.sc 1))).length = 2 ^ a * R by simp [hR₄, h3l],
    show R₄ (reg (.sc 2)) = List.replicate R₂ tick by simp [hR₄], List.drop_replicate] at e₅
  set M := R₂ - 2 ^ a * R with hM
  set R₅ := Function.update R₄ (reg (.sc 2)) (List.replicate M tick) with hR₅
  obtain ⟨v₆, hu₆, e₆⟩ := moveR_exec body (reg .io) (reg .racc) (reg_ne (by simp)) id v₅
    { S with R := R₅ }
  dsimp only at e₆
  rw [show R₅ (reg .io) = Xs by simp [hR₅, hR₄, hR₃, hR₂', hR₁, hXs]] at e₆
  set R₆ := movedR R₅ (reg .io) (reg .racc) id Xs with hR₆
  have hR₆row : (R₆ (reg .rowctr)).length = L := by
    simp [hR₆, movedR, hR₅, hR₄, hR₃, hR₂', hR₁, hrow, hL]
  -- the zero rows
  let Ψ : ℕ → Regs (nT BReg) A := fun j =>
    Function.update R₆ (reg .io) (List.replicate (j * L) (pairSym A false false))
  have hp : IterSpec body (umulSym 1 (pairSym A false false) (reg .rowctr) (reg .io) (reg (.sc 4)))
      (reg (.sc 2)) (reg (.sc 3)) Ψ (fun _ => 4 * L + 4) M := by
    intro j _ v' S' hS'
    have hb : S'.R (reg .io) = List.replicate (j * L) (pairSym A false false) := by
      rw [hS' _ (reg_ne (by simp)) (reg_ne (by simp))]; simp [Ψ]
    have hrw : (S'.R (reg .rowctr)).length = L := by
      rw [hS' _ (reg_ne (by simp)) (reg_ne (by simp))]; simp [Ψ, hR₆row]
    obtain ⟨v'', hu'', he''⟩ := umulSym_exec body 1 (pairSym A false false)
      (a := reg .rowctr) (b := reg .io) (t := reg (.sc 4)) (reg_ne (by simp)) (reg_ne (by simp))
      (reg_ne (by simp)) v' S'
      (by rw [hS' _ (reg_ne (by simp)) (reg_ne (by simp))]
          simp [Ψ, hR₆, movedR, hR₅, hR₄, hR₃, hR₂', hR₁, hsc])
    refine ⟨v'', _, _, hu'', le_of_eq (by rw [hrw]), he'', by simp, by simp, ?_⟩
    intro k hka hkt
    by_cases hk : k = reg .io
    · subst hk; simp [Ψ, hb, hrw, List.replicate_append_replicate]; ring_nf
    · simp [Ψ, Function.update_of_ne hk, hS' k hka hkt]
  obtain ⟨v₇, R₇, m₇, hu₇, hm₇, e₇, h7a, h7t, h7o⟩ := scanP_exec body (reg_ne (by simp)) hp 0 v₆
    { S with R := R₆ } (by simp [hR₆, movedR, hR₅]) (fun k hka hkt => by
      by_cases hk : k = reg .io
      · subst hk; simp [Ψ, hR₆, movedR]
      · simp [Ψ, Function.update_of_ne hk])
  dsimp only at h7a h7t hm₇
  have h3e : R₆ (reg (.sc 3)) = [] := by simp [hR₆, movedR, hR₅, hR₄, hR₃, hR₂', hR₁, hsc]
  have h2e : R₆ (reg (.sc 2)) = List.replicate M tick := by simp [hR₆, movedR, hR₅]
  rw [h3e, h2e] at hm₇ h7a
  simp only [List.length_replicate, Finset.sum_const, Finset.card_range,
    smul_eq_mul, List.length_nil, List.reverse_nil, List.nil_append] at hm₇ h7a
  -- `racc` back onto `io`
  obtain ⟨v₈, hu₈, e₈⟩ := moveR_exec body (reg .racc) (reg .io) (reg_ne (by simp)) id v₇
    { S with R := R₇ }
  dsimp only at e₈
  have h7r : R₇ (reg .racc) = Xs.reverse := by
    rw [h7o _ (reg_ne (by simp)) (reg_ne (by simp))]
    simp [Ψ, hR₆, movedR, hR₅, hR₄, hR₃, hR₂', hR₁, hracc]
  have h7i : R₇ (reg .io) = List.replicate (M * L) (pairSym A false false) := by
    rw [h7o _ (reg_ne (by simp)) (reg_ne (by simp))]
    simp [Ψ, h2e]
  rw [h7r] at e₈
  set R₈ := movedR R₇ (reg .racc) (reg .io) id Xs.reverse with hR₈
  obtain ⟨v₉, hu₉, e₉⟩ := uclear_exec body (reg (.sc 0)) v₈ { S with R := R₈ }
  obtain ⟨v₁₀, hu₁₀, e₁₀⟩ := uclear_exec body (reg (.sc 1)) v₉
    { S with R := Function.update R₈ (reg (.sc 0)) [] }
  obtain ⟨v₁₁, hu₁₁, e₁₁⟩ := uclear_exec body (reg (.sc 2)) v₁₀
    { S with R := Function.update (Function.update R₈ (reg (.sc 0)) []) (reg (.sc 1)) [] }
  have hR₇o : ∀ k, k ≠ reg (.sc 2) → k ≠ reg (.sc 3) → k ≠ reg .io → R₇ k = R₆ k := by
    intro k h1 h2 h3
    rw [h7o k h1 h2]; simp [Ψ, Function.update_of_ne h3]
  refine ⟨v₁₁, _, by rw [hu₁₁, hu₁₀, hu₉, hu₈, hu₇, hu₆, hu₅, hu₄, hu₃, hu₂, hu₁], ?_,
    Exec.cast (Exec.seq e₁ (Exec.seq e₂ (Exec.seq e₃ (Exec.seq e₄ (Exec.seq e₅ (Exec.seq e₆
      (Exec.seq e₇ (Exec.seq e₈ (Exec.seq e₉ (Exec.seq e₁₀ e₁₁)))))))))) rfl ?_⟩
  · have hs0 : (R₈ (reg (.sc 0))).length = a := by
      simp only [hR₈, movedR]; compactTopRowsFupd
      rw [hR₇o _ (reg_ne (by simp)) (reg_ne (by simp)) (reg_ne (by simp))]
      simp [hR₆, movedR, hR₅, hR₄, hR₃, hR₂', hR₁]
    have hs1 : (R₈ (reg (.sc 1))).length = 2 ^ a * R := by
      simp only [hR₈, movedR]; compactTopRowsFupd
      rw [hR₇o _ (reg_ne (by simp)) (reg_ne (by simp)) (reg_ne (by simp))]
      simp [hR₆, movedR, hR₅, hR₄, h3l]
    have hs2 : (R₈ (reg (.sc 2))).length = M := by
      simp only [hR₈, movedR]; compactTopRowsFupd; rw [h7a]; simp
    have hrl : (R₇ (reg .racc)).length = Xs.length := by rw [h7r]; simp
    dsimp only
    simp only [Function.update_apply]
    compactTopRowsFupd
    try rw [hs0]
    try rw [hs1]
    try rw [hs2]
    simp only [List.length_reverse]
    simp only [List.length_replicate] at hm₃
    unfold compactTopPadCost
    rw [← hM]
    linarith [hc₁, hc₂, hc₄, hm₃, hm₇]
  · congr 2
    funext k
    by_cases h0 : k = reg (.sc 0)
    · subst h0; simp [hsc]
    by_cases h1 : k = reg (.sc 1)
    · subst h1; simp [hsc]
    by_cases h2 : k = reg (.sc 2)
    · subst h2; simp [hsc]
    simp only [Function.update_apply, h0, h1, h2, ↓reduceIte, hR₈, movedR]
    by_cases h3 : k = reg .io
    · subst h3
      simp [h7i, List.map_id]
    by_cases h4 : k = reg .racc
    · subst h4; simp [h3, hracc]
    simp only [h3, h4, ↓reduceIte]
    by_cases h5 : k = reg (.sc 3)
    · subst h5; rw [h7t, hsc]
    rw [hR₇o k h2 h5 h3]
    simp [hR₆, movedR, hR₅, hR₄, hR₃, hR₂', hR₁, h0, h1, h2, h3, h4]

/-- Keep the first `R 2^a` rows (fields `3`, `2`): one counted copy of a row from `io` onto
`racc` per row, then `io` cleared and `racc` moved back. -/
noncomputable def compactTopUnpadS : Pr P (nT BReg) Q A U :=
  .seq (compactTopRd (reg (.sc 0)) 2)
  (.seq (compactTopRd (reg (.sc 1)) 3)
  (.seq (upow2 (reg (.sc 0)) (reg (.sc 1)) (reg (.sc 4)) (reg (.sc 5)))
  (.seq (scanP (reg (.sc 1)) (reg (.sc 3)) (Shift.counted (reg .rowctr) (reg .rowtmp)
      (Shift.copyStep (reg .rowctr) (reg .rowtmp) (reg .io) (reg .racc))))
  (.seq (uclear (reg .io))
  (.seq (moveR (reg .racc) (reg .io) id)
  (.seq (uclear (reg (.sc 0))) (uclear (reg (.sc 1)))))))))

/-- The step bound of `compactTopUnpadS` with `V` symbols on `io` and rows of `L` symbols. -/
def compactTopUnpadCost (cfg : List ℕ) (a R L V : ℕ) : ℕ :=
  2 * topGetCost cfg + (4 * (2 ^ a * R) + 9 * a + 4) +
    (2 ^ a * R * (4 * L + 7) + 2 * (2 ^ a * R) + 4) + (2 * V + 2) + (2 * V + 2) + (2 * a + 2) +
    (2 * (2 ^ a * R) + 2)

theorem compactTopUnpadS_exec {cfg : List ℕ} {n a R r w K ρ : ℕ} (h2 : cfg[2]? = some a)
    (h3 : cfg[3]? = some R) (v : HS (nT BReg) Q A U) (S : Stacks (nT BReg) A)
    (hT : CompactTopRegs bc S.R n r w K ρ) (hcf : ∃ rest, S.R (reg .park) = topRec cfg ++ rest)
    (hlen : 2 ^ a * R * (2 ^ n * r * w) ≤ (S.R (reg .io)).length) :
    ∃ (v' : HS (nT BReg) Q A U) (c : ℕ), v'.user = v.user ∧
      c ≤ compactTopUnpadCost cfg a R (2 ^ n * r * w) (S.R (reg .io)).length ∧
      Exec body compactTopUnpadS (mk v S) c
        (mk v' { S with
          R := Function.update S.R (reg .io)
            ((S.R (reg .io)).take (2 ^ a * R * (2 ^ n * r * w))) }) := by
  have hl2 : 2 < cfg.length := (List.getElem?_eq_some_iff.1 h2).1
  have hl3 : 3 < cfg.length := (List.getElem?_eq_some_iff.1 h3).1
  have hc2 : cfg[2] = a := (List.getElem?_eq_some_iff.1 h2).2
  have hc3 : cfg[3] = R := (List.getElem?_eq_some_iff.1 h3).2
  have hsc : ∀ i, S.R (reg (.sc i)) = [] := fun i => hT.rest (.sc i)
  have hlc : S.R (reg .lenctr) = [] := hT.rest .lenctr
  have hracc : S.R (reg .racc) = [] := hT.rest .racc
  have hrt : S.R (reg .rowtmp) = [] := hT.rest .rowtmp
  have hrow : (S.R (reg .rowctr)).length = 2 ^ n * r * w := hT.rest .rowctr
  set Xs := S.R (reg .io) with hXs
  set L := 2 ^ n * r * w with hL
  set N₁ := 2 ^ a * R with hN₁
  obtain ⟨v₁, c₁, hu₁, hc₁, e₁⟩ := compactTopRd_exec body (x := .sc 0) (by simp) (by simp) 2 hl2 v S
    hlc hcf
  rw [hc2, hsc 0, List.append_nil] at e₁
  set R₁ := Function.update S.R (reg (.sc 0)) (List.replicate a tick) with hR₁
  obtain ⟨v₂, c₂, hu₂, hc₂, e₂⟩ := compactTopRd_exec body (x := .sc 1) (by simp) (by simp) 3 hl3 v₁
    { S with R := R₁ } (by simp [hR₁, hlc]) (by simpa [hR₁] using hcf)
  dsimp only at e₂
  rw [hc3, show R₁ (reg (.sc 1)) = [] by simp [hR₁, hsc], List.append_nil] at e₂
  set R₂' := Function.update R₁ (reg (.sc 1)) (List.replicate R tick) with hR₂'
  obtain ⟨v₃, m₃, hu₃, hm₃, e₃⟩ := upow2_exec body (a := reg (.sc 0)) (b := reg (.sc 1))
    (t₁ := reg (.sc 4)) (t₂ := reg (.sc 5)) (nodup_map_reg (l := [.sc 0, .sc 1, .sc 4, .sc 5])
      (by simp)) v₂ { S with R := R₂' } (by simp [hR₂', hR₁, hsc]) (by simp [hR₂', hR₁, hsc])
  dsimp only at e₃ hm₃
  rw [show R₂' (reg (.sc 0)) = List.replicate a tick by simp [hR₂', hR₁],
    show R₂' (reg (.sc 1)) = List.replicate R tick by simp [hR₂'], List.length_replicate] at e₃ hm₃
  set R₃ := Function.update R₂' (reg (.sc 1))
    ((List.replicate R tick).flatMap (List.replicate (2 ^ a))) with hR₃
  have h3l : (R₃ (reg (.sc 1))).length = N₁ := by
    simp [hR₃, hN₁]; ring
  -- the rows kept
  let Ψ : ℕ → Regs (nT BReg) A := fun j =>
    Function.update (Function.update R₃ (reg .io) (Xs.drop (j * L))) (reg .racc)
      (Xs.take (j * L)).reverse
  have hp : IterSpec body (Shift.counted (reg .rowctr) (reg .rowtmp)
      (Shift.copyStep (reg .rowctr) (reg .rowtmp) (reg .io) (reg .racc)))
      (reg (.sc 1)) (reg (.sc 3)) Ψ (fun _ => 4 * L + 4) N₁ := by
    intro j hj v' S' hS'
    have hjL : (j + 1) * L ≤ Xs.length := le_trans (Nat.mul_le_mul_right _ hj) hlen
    have hjL' : j * L + L ≤ Xs.length := by rw [← Nat.succ_mul]; exact hjL
    have hio' : S'.R (reg .io) = (Xs.drop (j * L)).take L ++ Xs.drop (j * L + L) := by
      rw [hS' _ (reg_ne (by simp)) (reg_ne (by simp))]
      simp [Ψ, Nat.add_comm]
    obtain ⟨v'', hv'', he''⟩ := topCopyC_exec body (c := reg .rowctr) (t := reg .rowtmp)
      (src := reg .io) (dst := reg .racc)
      (nodup_map_reg (l := [.rowctr, .rowtmp, .io, .racc]) (by simp))
      ((Xs.drop (j * L)).take L) (Xs.drop (j * L + L)) v' S'
      (by rw [hS' _ (reg_ne (by simp)) (reg_ne (by simp))]
          simp [Ψ, hR₃, hR₂', hR₁, hrow]
          omega) hio'
      (by rw [hS' _ (reg_ne (by simp)) (reg_ne (by simp))]; simp [Ψ, hR₃, hR₂', hR₁, hrt])
    have hyl : ((Xs.drop (j * L)).take L).length = L := by simp; omega
    rw [hyl] at he''
    refine ⟨v'', _, _, hv''.user, le_refl _, he'', by simp, by simp, ?_⟩
    intro k hka hkt
    by_cases hk1 : k = reg .io
    · subst hk1; simp [Ψ, Nat.succ_mul]
    by_cases hk2 : k = reg .racc
    · subst hk2
      rw [Function.update_self, hS' _ hka hkt]
      simp [Ψ, Nat.succ_mul, List.take_add]
    simp [Ψ, Function.update_of_ne hk1, Function.update_of_ne hk2, hS' k hka hkt]
  obtain ⟨v₄, R₄, m₄, hu₄, hm₄, e₄, h4a, h4t, h4o⟩ := scanP_exec body (reg_ne (by simp)) hp 0 v₃
    { S with R := R₃ } (by simp [h3l]) (fun k hka hkt => by
      by_cases hk1 : k = reg .io
      · subst hk1; simp [Ψ, hR₃, hR₂', hR₁, hXs]
      by_cases hk2 : k = reg .racc
      · subst hk2; simp [Ψ, hR₃, hR₂', hR₁, hracc]
      simp [Ψ, Function.update_of_ne hk1, Function.update_of_ne hk2])
  dsimp only at h4a h4t hm₄
  have h3e : R₃ (reg (.sc 3)) = [] := by simp [hR₃, hR₂', hR₁, hsc]
  rw [h3e, h3l] at hm₄
  rw [h3e] at h4a
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul, List.length_nil,
    List.reverse_nil, List.nil_append] at hm₄ h4a
  have h4i : R₄ (reg .io) = Xs.drop (N₁ * L) := by
    rw [h4o _ (reg_ne (by simp)) (reg_ne (by simp)), h3l]; simp [Ψ]
  have h4r : R₄ (reg .racc) = (Xs.take (N₁ * L)).reverse := by
    rw [h4o _ (reg_ne (by simp)) (reg_ne (by simp)), h3l]; simp [Ψ]
  obtain ⟨v₅, hu₅, e₅⟩ := uclear_exec body (reg .io) v₄ { S with R := R₄ }
  dsimp only at e₅
  rw [h4i] at e₅
  obtain ⟨v₆, hu₆, e₆⟩ := moveR_exec body (reg .racc) (reg .io) (reg_ne (by simp)) id v₅
    { S with R := Function.update R₄ (reg .io) [] }
  dsimp only at e₆
  rw [show Function.update R₄ (reg .io) [] (reg .racc) = (Xs.take (N₁ * L)).reverse by
    rw [Function.update_of_ne (reg_ne (by simp)), h4r]] at e₆
  set R₆ := movedR (Function.update R₄ (reg .io) []) (reg .racc) (reg .io) id
    (Xs.take (N₁ * L)).reverse with hR₆
  obtain ⟨v₇, hu₇, e₇⟩ := uclear_exec body (reg (.sc 0)) v₆ { S with R := R₆ }
  obtain ⟨v₈, hu₈, e₈⟩ := uclear_exec body (reg (.sc 1)) v₇
    { S with R := Function.update R₆ (reg (.sc 0)) [] }
  have hR₄o : ∀ k, k ≠ reg (.sc 1) → k ≠ reg (.sc 3) → k ≠ reg .io → k ≠ reg .racc →
      R₄ k = R₃ k := by
    intro k h1 h2 h3 h4
    rw [h4o k h1 h2]; simp [Ψ, Function.update_of_ne h3, Function.update_of_ne h4]
  refine ⟨v₈, _, by rw [hu₈, hu₇, hu₆, hu₅, hu₄, hu₃, hu₂, hu₁], ?_,
    Exec.cast (Exec.seq e₁ (Exec.seq e₂ (Exec.seq e₃ (Exec.seq e₄ (Exec.seq e₅ (Exec.seq e₆
      (Exec.seq e₇ e₈))))))) rfl ?_⟩
  · have hs0 : (R₆ (reg (.sc 0))).length = a := by
      simp only [hR₆, movedR]; compactTopRowsFupd
      rw [hR₄o _ (reg_ne (by simp)) (reg_ne (by simp)) (reg_ne (by simp)) (reg_ne (by simp))]
      simp [hR₃, hR₂', hR₁]
    have hs1 : (Function.update R₆ (reg (.sc 0)) [] (reg (.sc 1))).length = N₁ := by
      simp only [hR₆, movedR]; compactTopRowsFupd; rw [h4a, h3l]
    rw [hs0, hs1]
    simp only [List.length_reverse, List.length_take, List.length_drop]
    simp only [List.length_replicate] at hm₃
    have hmin : min (N₁ * L) Xs.length = N₁ * L := by
      apply min_eq_left; rw [hN₁]; nlinarith [hlen]
    rw [hmin]
    unfold compactTopUnpadCost
    rw [← hN₁]
    have : Xs.length - N₁ * L ≤ Xs.length := Nat.sub_le _ _
    nlinarith [hc₁, hc₂, hm₃, hm₄]
  · congr 2
    funext k
    by_cases h0 : k = reg (.sc 0)
    · subst h0; simp [hsc]
    by_cases h1 : k = reg (.sc 1)
    · subst h1; simp [hsc]
    simp only [Function.update_apply, h0, h1, ↓reduceIte, hR₆, movedR]
    by_cases h3 : k = reg .io
    · subst h3; simp
    by_cases h4 : k = reg .racc
    · subst h4; simp [h3, hracc]
    simp only [h3, h4, ↓reduceIte]
    by_cases h5 : k = reg (.sc 3)
    · subst h5; rw [h4t, hsc]
    rw [hR₄o k h1 h5 h3 h4]
    simp [hR₃, hR₂', hR₁, h0, h1]


/-! ### The pieces -/

lemma CompactTopRegs.update_store {Rg : Fin (nT BReg) → List (Fin (A + 4))} {N r w K ρ : ℕ}
    (h : CompactTopRegs bc Rg N r w K ρ) {x : LReg BReg}
    (hx : x = .io ∨ x = .ph .arr ∨ x = .lf (.k .arr)) (l : List (Fin (A + 4))) :
    CompactTopRegs bc (Function.update Rg (reg x) l) N r w K ρ := by
  have hne : ∀ y : LReg BReg, y ∈ parRegs (BReg := BReg) → reg y ≠ reg x := by
    intro y hy
    apply reg_ne
    simp only [parRegs, List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hx with rfl | rfl | rfl <;>
      rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  exact {
    rest := fun y => by
      by_cases hy : y = x
      · subst hy
        rcases hx with rfl | rfl | rfl <;> trivial
      · rw [Function.update_of_ne (reg_ne hy)]; exact h.rest y
    hlev := by rw [Function.update_of_ne (hne .lev (by simp [parRegs]))]; exact h.hlev
    hu := by rw [Function.update_of_ne (hne .u (by simp [parRegs]))]; exact h.hu
    ha₀ := by rw [Function.update_of_ne (hne .a₀ (by simp [parRegs]))]; exact h.ha₀
    hL := by rw [Function.update_of_ne (hne .L (by simp [parRegs]))]; exact h.hL
    hrows := by rw [Function.update_of_ne (hne .rows (by simp [parRegs]))]; exact h.hrows
    hn := by rw [Function.update_of_ne (hne .n (by simp [parRegs]))]; exact h.hn
    hw := by rw [Function.update_of_ne (hne .w (by simp [parRegs]))]; exact h.hw
    hrw := by rw [Function.update_of_ne (hne .rw (by simp [parRegs]))]; exact h.hrw
    hK := by rw [Function.update_of_ne (hne .K (by simp [parRegs]))]; exact h.hK
    hρ := by rw [Function.update_of_ne (hne .ρ (by simp [parRegs]))]; exact h.hρ }

end
end IntegerMultBounds.MathlibTM2.LayerMachine
