module

public import IntegerMultBounds.MathlibTM2.Node.CompactTopProcRows
public import IntegerMultBounds.MathlibTM2.Node.CompactTopProcCall

/-! Actual recursive piece dispatch and padded top block for arbitrary basis
banks. Each piece uses the established per-layer CallSpec induction boundary;
all record processing, loops, row transforms and framing execute here. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds IntegerMultBounds.Networks IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Layer
open IntegerMultBounds.MathlibTM2.Node hiding LReg
noncomputable section
variable {BReg : Type} [Fintype BReg] {A Q : ℕ} {U P : Type}

local macro "compactTopPiecesFupd" : tactic => `(tactic| (simp only [Function.update_apply, reg_inj,
  reduceCtorEq, ↓reduceIte, eq_self_iff_true, LReg.sc.injEq, LReg.ph.injEq, LReg.lf.injEq,
  IntegerMultBounds.MathlibTM2.Node.LReg.k.injEq, Fin.reduceEq, Fin.isValue]))

/-- One piece: its fields `j`, `u`, `a₀`, `L` from `ph .arr` onto `lev`, `u`, `a₀`, `L` (the
fields kept on `lf (.k .arr)`), `rows := R₂` (field `4`), the call, and `flag` for the next
piece. -/
noncomputable def compactTopPcBody (cp : Pr P (nT BReg) Q A U) : Pr P (nT BReg) Q A U :=
  .seq (topField (reg (.ph .arr)) (reg (.lf (.k .arr))) (reg .lev) true)
  (.seq (topField (reg (.ph .arr)) (reg (.lf (.k .arr))) (reg .u) true)
  (.seq (topField (reg (.ph .arr)) (reg (.lf (.k .arr))) (reg .a₀) true)
  (.seq (topField (reg (.ph .arr)) (reg (.lf (.k .arr))) (reg .L) true)
  (.seq (compactTopRd (reg .rows) 4)
  (.seq (compactTopCallClr cp) (.act (peekR (reg (.ph .arr)))))))))

/-- The step bound of one piece. -/
def compactTopPcCost (cfg : List ℕ) (K : ℕ) (pc : TopPc) (cc : ℕ) : ℕ :=
  (2*pc.j+3)+(2*pc.u+3)+(2*pc.a₀+3)+(2*(K*bits pc.u pc.j)+3)+
    topGetCost cfg+(cc+(2*pc.j+2*pc.u+2*pc.a₀+2*(K*bits pc.u pc.j)+
      2*rowsAt pc.R₀ pc.j+10))+1

def compactTopPcsCost (cfg : List ℕ) (K : ℕ) (cc : TopPc → ℕ) : List TopPc → ℕ
  | [] => 1
  | pc :: pcs => compactTopPcCost cfg K pc (cc pc)+1+compactTopPcsCost cfg K cc pcs

theorem compactTopPcBody_exec (body : P → Pr P (nT BReg) Q A U)
    (cp : Pr P (nT BReg) Q A U) (bc : BReg → List (Fin (A+4)) → Prop)
    (ds : ComplexFramedExecution.Directions) (cc : TopPc → ℕ)
    {cfg : List ℕ} {n r w K ρ R₂ : ℕ} (h4 : cfg[4]? = some R₂) (hρ : ρ < K) (pc : TopPc) (hok : pc.Ok ds K n w R₂)
    (hcall : ∀ hfit : ∀ i<bits pc.u pc.j,pc.a₀+ρ+K*i<n,
      CallSpec body cp bc ds pc.R₀ pc.j pc.u K ρ pc.a₀ (K*bits pc.u pc.j) n r w hfit (cc pc)) (restPL : List (Fin (A + 4)))
    (Y : ZArr (Fin R₂ × Fin r) n) (v : HS (nT BReg) Q A U)
    (S : Stacks (nT BReg) A) (hL : ∀ y, S.L y = []) (hT : CompactTopRegs bc S.R n r w K ρ)
    (hcf : ∃ rest, S.R (reg .park) = topRec cfg ++ rest)
    (hPL : S.R (reg (.ph .arr)) = topRec (topPcFields K pc) ++ restPL)
    (hio : S.R (reg .io) = encZ A w Y) :
    ∃ (v' : HS (nT BReg) Q A U) (c : ℕ), v'.user = v.user ∧
      v'.flag = restPL.head?.isSome ∧ c ≤ compactTopPcCost cfg K pc (cc pc) ∧
      Exec body (compactTopPcBody cp) (mk v S) c
        (mk v' { S with
          R := Function.update (Function.update (Function.update S.R (reg .io)
            (encZ A w (pieceZ (pc.piece hρ hok).u ds (pc.piece hρ hok).R₀
              (pc.piece hρ hok).j (pc.piece hρ hok).hR (pc.piece hρ hok).e Y))) (reg (.ph .arr))
              restPL) (reg (.lf (.k .arr)))
            ((topRec (topPcFields K pc)).reverse ++ S.R (reg (.lf (.k .arr)))) }) := by
  have hl4 : 4 < cfg.length := (List.getElem?_eq_some_iff.1 h4).1
  have hc4 : cfg[4] = R₂ := (List.getElem?_eq_some_iff.1 h4).2
  have hlc : S.R (reg .lenctr) = [] := hT.rest .lenctr
  set PL : Fin (nT BReg) := reg (.ph .arr) with hPLd
  set PB : Fin (nT BReg) := reg (.lf (.k .arr)) with hPBd
  set Lv := K * bits pc.u pc.j with hLv
  have hd : ∀ x : LReg BReg, x ∈ [LReg.lev, .u, .a₀, .L] →
      PL ≠ reg x ∧ PB ≠ reg x := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> exact ⟨reg_ne (by simp), reg_ne (by simp)⟩
  have hPB : PL ≠ PB := reg_ne (by simp)
  -- the four fields
  have hPL₀ : S.R PL =
      List.replicate pc.j tick ++ topSep :: (topRec [pc.u, pc.a₀, Lv] ++ restPL) := by
    rw [hPL]; simp [topPcFields, topRec_cons, hLv]
  obtain ⟨v₁, hu₁, e₁⟩ := topField_exec body hPB (hd .lev (by simp)).1 (hd .lev (by simp)).2 true
    pc.j _ v S hPL₀
  simp only [ite_true, hT.hlev, List.append_nil] at e₁
  set F₁ := Function.update (Function.update (Function.update S.R PL
    (topRec [pc.u, pc.a₀, Lv] ++ restPL)) PB (topSep :: List.replicate pc.j tick ++ S.R PB))
    (reg .lev) (List.replicate pc.j tick) with hF₁
  obtain ⟨v₂, hu₂, e₂⟩ := topField_exec body hPB (hd .u (by simp)).1 (hd .u (by simp)).2 true
    pc.u (topRec [pc.a₀, Lv] ++ restPL) v₁ { S with R := F₁ }
    (by simp [hF₁, (hd .lev (by simp)).1, topRec_cons, hPB])
  simp only [ite_true] at e₂
  try dsimp only at e₂
  set F₂ := Function.update (Function.update (Function.update F₁ PL
    (topRec [pc.a₀, Lv] ++ restPL)) PB (topSep :: List.replicate pc.u tick ++ F₁ PB))
    (reg .u) (List.replicate pc.u tick ++ F₁ (reg .u)) with hF₂
  obtain ⟨v₃, hu₃, e₃⟩ := topField_exec body hPB (hd .a₀ (by simp)).1 (hd .a₀ (by simp)).2 true
    pc.a₀ (topRec [Lv] ++ restPL) v₂ { S with R := F₂ }
    (by simp [hF₂, (hd .u (by simp)).1, topRec_cons, hPB])
  simp only [ite_true] at e₃
  try dsimp only at e₃
  set F₃ := Function.update (Function.update (Function.update F₂ PL
    (topRec [Lv] ++ restPL)) PB (topSep :: List.replicate pc.a₀ tick ++ F₂ PB))
    (reg .a₀) (List.replicate pc.a₀ tick ++ F₂ (reg .a₀)) with hF₃
  obtain ⟨v₄, hu₄, e₄⟩ := topField_exec body hPB (hd .L (by simp)).1 (hd .L (by simp)).2 true
    Lv restPL v₃ { S with R := F₃ }
    (by simp [hF₃, (hd .a₀ (by simp)).1, topRec_cons, hPB])
  simp only [ite_true] at e₄
  try dsimp only at e₄
  set F₄ := Function.update (Function.update (Function.update F₃ PL restPL) PB
    (topSep :: List.replicate Lv tick ++ F₃ PB))
    (reg .L) (List.replicate Lv tick ++ F₃ (reg .L)) with hF₄
  have hF₄o : ∀ x : LReg BReg, x ≠ .lev → x ≠ .u → x ≠ .a₀ → x ≠ .L → x ≠ .ph .arr →
      x ≠ .lf (.k .arr) → F₄ (reg x) = S.R (reg x) := by
    intro x h1 h2 h3 h4 h5 h6
    simp [hF₄, hF₃, hF₂, hF₁, hPLd, hPBd, h1, h2, h3, h4, h5, h6]
  -- `rows := F₂`
  obtain ⟨v₅, c₅, hu₅, hc₅, e₅⟩ := compactTopRd_exec body (x := .rows) (by simp) (by simp) 4 hl4 v₄
    { S with R := F₄ }
    ((hF₄o .lenctr (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)).trans hlc)
    (by obtain ⟨rest, h⟩ := hcf
        exact ⟨rest, (hF₄o .park (by simp) (by simp) (by simp) (by simp) (by simp)
          (by simp)).trans h⟩)
  try dsimp only at e₅
  rw [hc4, hF₄o _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp), hT.hrows,
    List.append_nil] at e₅
  set F₅ := Function.update F₄ (reg .rows) (List.replicate R₂ tick) with hF₅
  -- the call
  set Z : ZArr (Fin (rowsAt pc.R₀ pc.j) × Fin r) n :=
    fun q => Y ((Fin.cast hok.hR.symm q.1.1, q.1.2), q.2) with hZ
  have hF₅o : ∀ x : LReg BReg, x ≠ .lev → x ≠ .u → x ≠ .a₀ → x ≠ .L → x ≠ .rows →
      x ≠ .ph .arr → x ≠ .lf (.k .arr) → F₅ (reg x) = S.R (reg x) := by
    intro x h1 h2 h3 h4 h5 h6 h7
    rw [hF₅, Function.update_of_ne (reg_ne h5), hF₄o x h1 h2 h3 h4 h6 h7]
  have hpar : ParState F₅ pc.j pc.u K ρ pc.a₀ (K * bits pc.u pc.j) (rowsAt pc.R₀ pc.j) n w
      (r * w) := by
    have hh : ∀ x : LReg BReg, x ∈ [LReg.K, .ρ, .n, .w, .rw] → F₅ (reg x) = S.R (reg x) := by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;>
        exact hF₅o _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
    refine compactTopParState ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · simp [hF₅, hF₄, hF₃, hF₂, hF₁, hPLd, hPBd]
    · simp [hF₅, hF₄, hF₃, hF₂, hPLd, hPBd, hF₁, hT.hu]
    · rw [hh _ (by simp)]; exact hT.hK
    · rw [hh _ (by simp)]; exact hT.hρ
    · simp [hF₅, hF₄, hF₃, hPLd, hPBd, hF₂, hF₁, hT.ha₀]
    · simp [hF₅, hF₄, hPLd, hPBd, hF₃, hF₂, hF₁, hT.hL, hLv]
    · simp [hF₅, ← hok.hR]
    · rw [hh _ (by simp)]; exact hT.hn
    · rw [hh _ (by simp)]; exact hT.hw
    · rw [hh _ (by simp)]; exact hT.hrw
  have hrest₅ : Rest bc n r w F₅ := by
    intro x
    by_cases hx : x ∈ parRegs (BReg := BReg)
    · exact compactTopRestSpec_par hx _
    by_cases h6 : x = .ph .arr
    · subst h6; trivial
    by_cases h7 : x = .lf (.k .arr)
    · subst h7; trivial
    rw [hF₅o x (fun h => hx (by simp [h, parRegs])) (fun h => hx (by simp [h, parRegs]))
      (fun h => hx (by simp [h, parRegs])) (fun h => hx (by simp [h, parRegs]))
      (fun h => hx (by simp [h, parRegs])) h6 h7]
    exact hT.rest x
  obtain ⟨v₆, c₆, hu₆, hc₆, e₆⟩ := compactTopCallClr_exec body cp bc ds
    (topFit hρ hok.hfit) (hcall _) Z v₅ { S with R := F₅ } hL hpar hrest₅
    ((hF₅o .io (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)).trans
      (hio.trans (topEnc_cast hok.hR.symm Y).symm))
  set X := encZ A w (pieceZ (pc.piece hρ hok).u ds (pc.piece hρ hok).R₀
    (pc.piece hρ hok).j (pc.piece hρ hok).hR (pc.piece hρ hok).e Y) with hX
  have hX' : encZ A w (layerZ pc.u ds pc.R₀ pc.j
      (actMap pc.a₀ ρ K (bits pc.u pc.j) n (topFit hρ hok.hfit)) Z) = X := by
    rw [hX]; exact (topEnc_cast hok.hR _).symm
  rw [hX'] at e₆
  set F₆ := Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update F₅ (reg .io) X) (reg .lev) []) (reg .u) []) (reg .a₀) []) (reg .L) [])
    (reg .rows) [] with hF₆
  have e₇ := Exec.act (body := body) (peekR PL : Act _ _ _ _) (mk v₆ { S with R := F₆ })
  rw [peekR_run] at e₇
  have hF₆PL : F₆ PL = restPL := by simp [hF₆, hF₅, hF₄, hPLd, hPBd]
  refine ⟨{ v₆ with flag := (F₆ PL).head?.isSome }, _, by rw [hu₆, hu₅, hu₄, hu₃, hu₂, hu₁],
    by rw [hF₆PL], ?_, Exec.seq e₁ (Exec.seq e₂ (Exec.seq e₃ (Exec.seq e₄ (Exec.seq e₅
      (Exec.seq e₆ (Exec.cast e₇ rfl ?_))))))⟩
  · have e1 : (F₁ (reg .u)).length = 0 := by simp [hF₁, hPLd, hPBd, hT.hu]
    have e2 : (F₂ (reg .a₀)).length = 0 := by simp [hF₂, hF₁, hPLd, hPBd, hT.ha₀]
    have e3 : (F₃ (reg .L)).length = 0 := by simp [hF₃, hF₂, hF₁, hPLd, hPBd, hT.hL]
    unfold compactTopPcCost
    rw [← hLv]
    rw [← hLv] at hc₆
    omega
  · congr 2
    funext k
    by_cases h1 : k = PB
    · subst h1
      simp [hF₆, hF₅, hF₄, hF₃, hF₂, hF₁, hPLd, hPBd, topPcFields, topRec, hLv]
    by_cases h2 : k = PL
    · subst h2; simp [hF₆, hF₅, hF₄, hPLd, hPBd]
    by_cases h3 : k = reg .io
    · subst h3; simp [hF₆, hPLd, hPBd]
    by_cases h4 : k = reg .lev
    · subst h4; simp [hF₆, hPLd, hPBd, hT.hlev]
    by_cases h5 : k = reg .u
    · subst h5; simp [hF₆, hPLd, hPBd, hT.hu]
    by_cases h6 : k = reg .a₀
    · subst h6; simp [hF₆, hPLd, hPBd, hT.ha₀]
    by_cases h7 : k = reg .L
    · subst h7; simp [hF₆, hPLd, hPBd, hT.hL]
    by_cases h8 : k = reg .rows
    · subst h8; simp [hF₆, hPLd, hPBd, hT.hrows]
    simp only [hF₆, Function.update_apply, h1, h2, h3, h4, h5, h6, h7, h8, ↓reduceIte]
    obtain ⟨x, rfl⟩ := (regEquiv BReg).surjective k
    exact hF₅o x (fun h => h4 (by rw [h]; rfl)) (fun h => h5 (by rw [h]; rfl))
      (fun h => h6 (by rw [h]; rfl)) (fun h => h7 (by rw [h]; rfl)) (fun h => h8 (by rw [h]; rfl))
      (fun h => h2 (by rw [h]; rfl)) (fun h => h1 (by rw [h]; rfl))

theorem compactTopPcLoop_loop (body : P → Pr P (nT BReg) Q A U)
    (cp : Pr P (nT BReg) Q A U) (bc : BReg → List (Fin (A+4)) → Prop)
    (ds : ComplexFramedExecution.Directions) (cc : TopPc → ℕ)
    {cfg : List ℕ} {n r w K ρ R₂ : ℕ} (h4 : cfg[4]? = some R₂) (hρ : ρ < K) :
    ∀ (pcs : List TopPc) (hpcs : ∀ pc ∈ pcs, pc.Ok ds K n w R₂)
      (_hcalls : ∀ pc∈pcs, ∀ hfit : ∀ i<bits pc.u pc.j,pc.a₀+ρ+K*i<n,
      CallSpec body cp bc ds pc.R₀ pc.j pc.u K ρ pc.a₀ (K*bits pc.u pc.j) n r w hfit (cc pc)) (Y : ZArr (Fin R₂ × Fin r) n)
      (v : HS (nT BReg) Q A U) (S : Stacks (nT BReg) A),
      (∀ y, S.L y = []) → CompactTopRegs bc S.R n r w K ρ →
      (∃ rest, S.R (reg .park) = topRec cfg ++ rest) →
      S.R (reg (.ph .arr)) = topRec (topPcRec K pcs) →
      v.flag = (S.R (reg (.ph .arr))).head?.isSome →
      S.R (reg .io) = encZ A w Y →
      ∃ (v' : HS (nT BReg) Q A U) (c : ℕ), v'.user = v.user ∧
        c ≤ compactTopPcsCost cfg K cc pcs ∧
        Exec body (.loop (·.flag) (compactTopPcBody cp)) (mk v S) c
          (mk v' { S with
            R := Function.update (Function.update (Function.update S.R (reg .io)
              (encZ A w (piecesZ ds (topPieces hρ pcs hpcs) Y))) (reg (.ph .arr)) [])
              (reg (.lf (.k .arr)))
              ((topRec (topPcRec K pcs)).reverse ++ S.R (reg (.lf (.k .arr)))) })
  | [], hpcs, hcalls, Y, v, S, hL, hT, hcf, hPL, hf, hio => by
      refine ⟨v, 1, rfl, le_refl _, ?_⟩
      have hS : ({ S with
          R := Function.update (Function.update (Function.update S.R (reg .io)
            (encZ A w (piecesZ ds (topPieces hρ [] hpcs) Y))) (reg (.ph .arr)) [])
            (reg (.lf (.k .arr)))
            ((topRec (topPcRec K [])).reverse ++ S.R (reg (.lf (.k .arr)))) } :
            Stacks (nT BReg) A) = S := by
        cases S with
        | mk inp out L R =>
          simp only at hio hPL ⊢
          congr 1
          funext k
          simp only [Function.update_apply]
          split_ifs with h1 h2 h3
          · subst h1; simp [topPcRec]
          · subst h2; rw [hPL]; simp [topPcRec]
          · subst h3; rw [hio]; rfl
          · rfl
      rw [hS]
      exact .loop_false (by show v.flag = false; rw [hf, hPL]; simp [topPcRec])
  | pc :: pcs, hpcs, hcalls, Y, v, S, hL, hT, hcf, hPL, hf, hio => by
      have hok := hpcs pc List.mem_cons_self
      have hPL' : S.R (reg (.ph .arr)) = topRec (topPcFields K pc) ++ topRec (topPcRec K pcs) := by
        rw [hPL, topPcRec, List.flatMap_cons, topRec_append]; rfl
      obtain ⟨v₁, c₁, hu₁, hf₁, hc₁, e₁⟩ := compactTopPcBody_exec body cp bc ds cc h4 hρ pc
        hok (hcalls pc List.mem_cons_self) (topRec (topPcRec K pcs)) Y v S hL hT hcf hPL' hio
      set P := pc.piece hρ hok
      set Y' := pieceZ P.u ds P.R₀ P.j P.hR P.e Y with hY'
      set S₁ : Stacks (nT BReg) A := { S with
        R := Function.update (Function.update (Function.update S.R (reg .io)
          (encZ A w Y')) (reg (.ph .arr)) (topRec (topPcRec K pcs)))
          (reg (.lf (.k .arr)))
          ((topRec (topPcFields K pc)).reverse ++ S.R (reg (.lf (.k .arr)))) } with hS₁
      have hT₁ : CompactTopRegs bc S₁.R n r w K ρ :=
        ((hT.update_store (Or.inl rfl) _).update_store (Or.inr (Or.inl rfl)) _).update_store
          (Or.inr (Or.inr rfl)) _
      obtain ⟨v₂, c₂, hu₂, hc₂, e₂⟩ := compactTopPcLoop_loop body cp bc ds cc h4 hρ pcs
        (fun q hq => hpcs q (List.mem_cons_of_mem _ hq))
        (fun q hq => hcalls q (List.mem_cons_of_mem _ hq)) Y' v₁ S₁ hL hT₁
        (by simpa [hS₁] using hcf) (by simp [hS₁]) (by rw [hf₁]; simp [hS₁])
        (by simp [hS₁])
      have hne : (S.R (reg (.ph .arr))).head?.isSome = true := by
        rw [hPL']; simp [topPcFields, topRec]
      refine ⟨v₂, c₁ + c₂ + 1, hu₂.trans hu₁, by simp only [compactTopPcsCost]; omega,
        Exec.cast (Exec.loop_true (by show v.flag = true; rw [hf]; exact hne) e₁ e₂) rfl ?_⟩
      congr 2
      funext k
      simp only [hS₁, Function.update_apply]
      split_ifs <;> simp_all [topPcRec, topRec_append, List.reverse_append, piecesZ, topPieces]
      rfl

/-- The pieces: run the piece record of `ph .arr` through `(compactTopPcBody cp)`, keeping the consumed
fields on the empty `lf (.k .arr)`, and move them back. -/
noncomputable def compactTopPcLoop (cp : Pr P (nT BReg) Q A U) : Pr P (nT BReg) Q A U :=
  .seq (.act (peekR (reg (.ph .arr))))
    (.seq (.loop (·.flag) (compactTopPcBody cp)) (moveR (reg (.lf (.k .arr))) (reg (.ph .arr)) id))

theorem compactTopPcLoop_exec (body : P → Pr P (nT BReg) Q A U)
    (cp : Pr P (nT BReg) Q A U) (bc : BReg → List (Fin (A+4)) → Prop)
    (ds : ComplexFramedExecution.Directions) (cc : TopPc → ℕ)
    {cfg : List ℕ} {n r w K ρ R₂ : ℕ} (h4 : cfg[4]? = some R₂) (hρ : ρ < K) (pcs : List TopPc) (hpcs : ∀ pc ∈ pcs, pc.Ok ds K n w R₂)
    (hcalls : ∀ pc∈pcs, ∀ hfit : ∀ i<bits pc.u pc.j,pc.a₀+ρ+K*i<n,
      CallSpec body cp bc ds pc.R₀ pc.j pc.u K ρ pc.a₀ (K*bits pc.u pc.j) n r w hfit (cc pc))
    (Y : ZArr (Fin R₂ × Fin r) n) (v : HS (nT BReg) Q A U)
    (S : Stacks (nT BReg) A) (hL : ∀ y, S.L y = []) (hT : CompactTopRegs bc S.R n r w K ρ)
    (hcf : ∃ rest, S.R (reg .park) = topRec cfg ++ rest)
    (hPL : S.R (reg (.ph .arr)) = topRec (topPcRec K pcs)) (hPB : S.R (reg (.lf (.k .arr))) = [])
    (hio : S.R (reg .io) = encZ A w Y) :
    ∃ (v' : HS (nT BReg) Q A U) (c : ℕ), v'.user = v.user ∧
      c ≤ compactTopPcsCost cfg K cc pcs + 1 + (2 * topRecLen (topPcRec K pcs) + 2) ∧
      Exec body (compactTopPcLoop cp) (mk v S) c
        (mk v' { S with
          R := Function.update S.R (reg .io)
            (encZ A w (piecesZ ds (topPieces hρ pcs hpcs) Y)) }) := by
  have e₀ := Exec.act (body := body) (peekR (reg (.ph .arr)) : Act _ _ _ _) (mk v S)
  rw [peekR_run] at e₀
  obtain ⟨v₁, c₁, hu₁, hc₁, e₁⟩ := compactTopPcLoop_loop body cp bc ds cc h4 hρ pcs hpcs hcalls Y
    { v with flag := (S.R (reg (.ph .arr))).head?.isSome } S hL hT hcf hPL rfl hio
  set R₁ := Function.update (Function.update (Function.update S.R (reg .io)
    (encZ A w (piecesZ ds (topPieces hρ pcs hpcs) Y))) (reg (.ph .arr)) [])
    (reg (.lf (.k .arr))) ((topRec (topPcRec K pcs)).reverse ++ S.R (reg (.lf (.k .arr))))
    with hR₁
  obtain ⟨v₂, hu₂, e₂⟩ := moveR_exec body (reg (.lf (.k .arr))) (reg (.ph .arr))
    (reg_ne (by simp)) id v₁ { S with R := R₁ }
  refine ⟨v₂, _, by rw [hu₂, hu₁], ?_, Exec.cast (Exec.seq e₀ (Exec.seq e₁ e₂)) rfl ?_⟩
  · dsimp only
    simp only [hR₁, Function.update_self, hPB, List.append_nil, List.length_reverse,
      length_topRec']
    omega
  · congr 2
    funext k
    simp only [movedR, hR₁, Function.update_apply]
    split_ifs <;> simp_all

/-- The pieces on the array with the top bits as rows: the rest state for `n` address bits,
padding, the pieces, unpadding, and the rest state for `n + a` address bits again. -/
noncomputable def compactTopBlockS (cp : Pr P (nT BReg) Q A U) : Pr P (nT BReg) Q A U :=
  .seq compactTopDownS (.seq compactTopPadS (.seq (compactTopPcLoop cp) (.seq compactTopUnpadS compactTopUpS)))

/-- The step bound of `(compactTopBlockS cp)`. -/
def compactTopBlockCost (cfg : List ℕ)
    (K n a r w R R₂ : ℕ) (cc : TopPc → ℕ) (pcs : List TopPc) : ℕ :=
  compactTopDownCost cfg n a r w + compactTopPadCost cfg a R R₂ (2 ^ n * r * w) (R * 2 ^ a * 2 ^ n * r * w) +
    (compactTopPcsCost cfg K cc pcs + 1 + (2 * topRecLen (topPcRec K pcs) + 2)) +
    compactTopUnpadCost cfg a R (2 ^ n * r * w) (R₂ * 2 ^ n * r * w) + compactTopUpCost cfg n a r w

theorem compactTopBlockS_exec (body : P → Pr P (nT BReg) Q A U)
    (cp : Pr P (nT BReg) Q A U) (bc : BReg → List (Fin (A+4)) → Prop)
    (ds : ComplexFramedExecution.Directions) (cc : TopPc → ℕ)
    {cfg : List ℕ} {n a R R₂ r w K ρ : ℕ} (h2 : cfg[2]? = some a) (h3 : cfg[3]? = some R)
    (h4 : cfg[4]? = some R₂) (hρ : ρ < K) (hR₂ : R * 2 ^ a ≤ R₂)
    (pcs : List TopPc) (hpcs : ∀ pc ∈ pcs, pc.Ok ds K n w R₂)
    (hcalls : ∀ pc∈pcs, ∀ hfit : ∀ i<bits pc.u pc.j,pc.a₀+ρ+K*i<n,
      CallSpec body cp bc ds pc.R₀ pc.j pc.u K ρ pc.a₀ (K*bits pc.u pc.j) n r w hfit (cc pc))
    (Y : ZArr (Fin (R * 2 ^ a) × Fin r) n) (v : HS (nT BReg) Q A U)
    (S : Stacks (nT BReg) A) (hL : ∀ y, S.L y = [])
    (hT : CompactTopRegs bc S.R (n + a) r w K ρ) (hI : CompactTopIn (BReg := BReg) S.R cfg (topPcRec K pcs))
    (hio : S.R (reg .io) = encZ A w Y) :
    ∃ (v' : HS (nT BReg) Q A U) (c : ℕ), v'.user = v.user ∧
      c ≤ compactTopBlockCost cfg K n a r w R R₂ cc pcs ∧
      Exec body (compactTopBlockS cp) (mk v S) c
        (mk v' { S with
          R := Function.update S.R (reg .io) (encZ A w
            (unpadRows hR₂ (piecesZ ds (topPieces hρ pcs hpcs) (padRows R₂ Y)))) }) := by
  -- down
  obtain ⟨v₁, c₁, hu₁, hc₁, e₁⟩ := compactTopDownS_exec body h2 v S hT hI
  set Rd := compactTopDownR S.R a n r w with hRd
  have hTd : CompactTopRegs bc Rd n r w K ρ := compactTopDownR_regs hT
  have hcfd : ∃ rest, Rd (reg .park) = topRec cfg ++ rest := by
    rw [hRd, compactTopDownR_of_ne (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)]
    exact hI.cf
  have hiod : Rd (reg .io) = encZ A w Y := by
    rw [hRd, compactTopDownR_of_ne (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)]
    exact hio
  -- pad
  obtain ⟨v₂, c₂, hu₂, hc₂, e₂⟩ := compactTopPadS_exec body h2 h3 h4 v₁ { S with R := Rd } hTd hcfd
  dsimp only at e₂ hc₂
  have hpad : Rd (reg .io) ++ List.replicate ((R₂ - 2 ^ a * R) * (2 ^ n * r * w))
      (pairSym A false false) = encZ A w (padRows R₂ Y) := by
    rw [hiod, topEnc_padRows hR₂]
    congr 2
    rw [Nat.mul_comm (2 ^ a) R]; ring
  rw [hpad] at e₂
  -- the pieces
  obtain ⟨v₃, c₃, hu₃, hc₃, e₃⟩ := compactTopPcLoop_exec body cp bc ds cc h4 hρ pcs hpcs hcalls
    (padRows R₂ Y) v₂ { S with R := Function.update Rd (reg .io) (encZ A w
      (padRows R₂ Y)) } hL (hTd.update_io _)
    (by simpa [Function.update_of_ne (reg_ne (show LReg.park ≠ .io by simp))] using hcfd)
    (by dsimp only; rw [Function.update_of_ne (reg_ne (by simp)), hRd,
      compactTopDownR_of_ne (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)]; exact hI.pl)
    (by dsimp only; rw [Function.update_of_ne (reg_ne (by simp)), hRd,
      compactTopDownR_of_ne (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)]; exact hI.pb)
    (by simp)
  rw [Function.update_idem] at e₃
  set G := piecesZ ds (topPieces hρ pcs hpcs) (padRows R₂ Y) with hG
  -- unpad
  have hGl : (encZ A w G).length = R₂ * 2 ^ n * r * w := topEnc_length w G
  obtain ⟨v₄, c₄, hu₄, hc₄, e₄⟩ := compactTopUnpadS_exec body h2 h3 v₃
    { S with R := Function.update Rd (reg .io) (encZ A w G) } (hTd.update_io _)
    (by simpa [Function.update_of_ne (reg_ne (show LReg.park ≠ .io by simp))] using hcfd)
    (by
      simp only [Function.update_self, hGl]
      have := Nat.mul_le_mul_right (2 ^ n * r * w) hR₂
      rw [Nat.mul_comm (2 ^ a) R]; nlinarith [this])
  dsimp only at e₄ hc₄
  rw [Function.update_self, Function.update_idem] at e₄
  have hunpad : (encZ A w G).take (2 ^ a * R * (2 ^ n * r * w)) =
      encZ A w (unpadRows hR₂ G) := by
    rw [topEnc_unpadRows]; congr 1; ring
  rw [hunpad] at e₄
  -- up
  obtain ⟨v₅, c₅, hu₅, hc₅, e₅⟩ := compactTopUpS_exec body h2 v₄ S hT hI
    (encZ A w (unpadRows hR₂ G))
  refine ⟨v₅, c₁ + (c₂ + (c₃ + (c₄ + c₅))), by rw [hu₅, hu₄, hu₃, hu₂, hu₁], ?_,
    Exec.seq e₁ (Exec.seq e₂ (Exec.seq e₃ (Exec.seq e₄ e₅)))⟩
  rw [hiod, Function.update_self, hGl, topEnc_length] at *
  unfold compactTopBlockCost
  have e1 : (2 ^ a * R) = R * 2 ^ a := Nat.mul_comm _ _
  simp only [compactTopPadCost, compactTopUnpadCost] at hc₂ hc₄ ⊢
  nlinarith [hc₁, hc₂, hc₃, hc₄, hc₅]

end
end IntegerMultBounds.MathlibTM2.LayerMachine
