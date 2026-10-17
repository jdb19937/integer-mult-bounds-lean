module

public import IntegerMultBounds.MathlibTM2.Node.CompactTopProc
public import IntegerMultBounds.MathlibTM2.Node.CompactLayerProcR
public import IntegerMultBounds.MathlibTM2.Node.ShrinkWord

/-!
# The rounded top program

`compactTopProgR` runs the simultaneous layer with rounded pieces: widening, the phase, the guard
(multiplication by `2^g`, `compactTopGuardS`), the top kernels, the pieces with the top bits as
rows, the phase, the unit, then the truncation by `2^s'` (`compactTopCutS`), `k` shrinks by one
(`compactTopShrinkS`) and the final truncating shift by `2^(s - s')` (`compactTopShiftSR`). The
configuration record is `topCfgR`: `topCfg` with the total shift `s`, followed by `g`, `s'`, `k`.

The pieces call a layer program with result `layerRW` (`CallSpecF`); the pieces as the tape
computes them are `piecesRW`, the array before the shifts `topPreRW`, and the output
`topRSW … s (k 2^s')` (`compactTopProgR_exec_RS`, by `tdiv_shrink_mul`). It is `topRS`
when the pieces run as `piecesR` (`topRSW_eq_topRS`).
-/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds IntegerMultBounds.Networks IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Layer
open IntegerMultBounds.MathlibTM2.Node hiding LReg

/-! ### The semantics -/

section Sem

variable {R r n : ℕ}

/-- A piece of the rounded layer as the tape computes it. -/
noncomputable def pieceRW (w u : ℕ) (ds : ComplexFramedExecution.Directions) (R₀ j : ℕ) {R₂ : ℕ}
    (hR : R₂ = rowsAt R₀ j) (e : Fin (bits u j) → Fin n) (Z : ZArr (Fin R₂ × Fin r) n) :
    ZArr (Fin R₂ × Fin r) n :=
  fun p => layerRW w u ds R₀ j e (fun q => Z ((Fin.cast hR.symm q.1.1, q.1.2), q.2))
    ((Fin.cast hR p.1.1, p.1.2), p.2)

/-- Run the pieces as the tape computes them. -/
noncomputable def piecesRW (w : ℕ) (ds : ComplexFramedExecution.Directions) {R₂ : ℕ} :
    List (Piece n R₂) → ZArr (Fin R₂ × Fin r) n → ZArr (Fin R₂ × Fin r) n
  | [], Z => Z
  | P :: Ps, Z => piecesRW w ds Ps (pieceRW w P.u ds P.R₀ P.j P.hR P.e Z)

/-- The array before the shifts, as the tape computes it. -/
noncomputable def topPreRW (ds : ComplexFramedExecution.Directions) (w a : ℕ) (low : List (Fin n))
    (top : List (Fin (n + a))) {R₂ : ℕ} (hR₂ : R * 2 ^ a ≤ R₂) (Ps : List (Piece n R₂)) (g : ℕ)
    (Z : ZArr (Fin R × Fin r) (n + a)) : ZArr (Fin R × Fin r) (n + a) :=
  fun p => unitD (topSel a low top).length * sZ (topSel a low top)
    (ofRows a (unpadRows hR₂ (piecesRW w ds Ps (padRows R₂ (toRows a
      (k2s top ((2 ^ g : GaussianInt) • sZ (topSel a low top) Z))))))) p

/-- The rounded top with a shrink, as the tape computes it. -/
noncomputable def topRSW (ds : ComplexFramedExecution.Directions) (w a : ℕ) (low : List (Fin n))
    (top : List (Fin (n + a))) {R₂ : ℕ} (hR₂ : R * 2 ^ a ≤ R₂) (Ps : List (Piece n R₂))
    (g s c : ℕ) (Z : ZArr (Fin R × Fin r) (n + a)) : ZArr (Fin R × Fin r) (n + a) :=
  fun p => tdivZ s (shrinkZ c (topPreRW ds w a low top hR₂ Ps g Z p))

/-- `topRSW` is `topRS` when the pieces of the tape agree with the rounded pieces on the padded
input. -/
lemma topRSW_eq_topRS (ds : ComplexFramedExecution.Directions) (w a : ℕ) (low : List (Fin n))
    (top : List (Fin (n + a))) {R₂ : ℕ} (hR₂ : R * 2 ^ a ≤ R₂) (Ps : List (Piece n R₂))
    (g s c : ℕ) (Z : ZArr (Fin R × Fin r) (n + a))
    (h : piecesRW w ds Ps (padRows R₂ (toRows a
        (k2s top ((2 ^ g : GaussianInt) • sZ (topSel a low top) Z)))) =
      piecesR ds Ps (padRows R₂ (toRows a
        (k2s top ((2 ^ g : GaussianInt) • sZ (topSel a low top) Z))))) :
    topRSW ds w a low top hR₂ Ps g s c Z = topRS ds a low top hR₂ Ps g s c Z := by
  funext p
  simp only [topRSW, topPreRW, h]
  rfl

/-- The pieces of the tape are the rounded pieces when every layer of the tape agrees with the
rounded layer on its input. -/
lemma piecesRW_eq_piecesR (w : ℕ) (ds : ComplexFramedExecution.Directions) {R₂ : ℕ} :
    ∀ (Ps : List (Piece n R₂)) (Z : ZArr (Fin R₂ × Fin r) n),
      (∀ Y : ZArr (Fin R₂ × Fin r) n, ∀ P ∈ Ps, pieceRW w P.u ds P.R₀ P.j P.hR P.e Y = pieceR P.u ds P.R₀ P.j P.hR P.e Y) →
      piecesRW w ds Ps Z = piecesR ds Ps Z
  | [], _, _ => rfl
  | P :: Ps, Z, h => by
      simp only [piecesRW, piecesR]
      rw [h Z P List.mem_cons_self]
      exact piecesRW_eq_piecesR w ds Ps _ fun Y Q hQ => h Y Q (List.mem_cons_of_mem _ hQ)

end Sem

noncomputable section
variable {BReg : Type} [Fintype BReg] {A Q : ℕ} {U P : Type}

local macro "compactTopPiecesFupd" : tactic => `(tactic| (simp only [Function.update_apply, reg_inj,
  reduceCtorEq, ↓reduceIte, eq_self_iff_true, LReg.sc.injEq, LReg.ph.injEq, LReg.lf.injEq,
  IntegerMultBounds.MathlibTM2.Node.LReg.k.injEq, Fin.reduceEq, Fin.isValue]))

local macro "compactTopFupd" : tactic => `(tactic| (simp only [Function.update_apply, reg_inj,
  reduceCtorEq, ↓reduceIte, eq_self_iff_true, LReg.sc.injEq, LReg.ph.injEq, LReg.lf.injEq,
  IntegerMultBounds.MathlibTM2.Node.LReg.k.injEq, Fin.reduceEq, Fin.isValue]))

/-! ### Pieces -/

/-- The conditions of a rounded piece: `TopPc.Ok` without the exponent bound. -/
structure TopPc.OkR (K n R₂ : ℕ) (pc : TopPc) : Prop where
  hu : 1 ≤ pc.u
  hR₀ : 1 ≤ pc.R₀
  hR : R₂ = rowsAt pc.R₀ pc.j
  hfit : pc.a₀ + K * bits pc.u pc.j ≤ n

/-- The piece of a machine piece. -/
noncomputable def TopPc.pieceR {ρ K n R₂ : ℕ} (hρ : ρ < K) (pc : TopPc) (h : pc.OkR K n R₂) :
    Piece n R₂ :=
  ⟨pc.u, pc.j, pc.R₀, h.hR, actMap pc.a₀ ρ K (bits pc.u pc.j) n (topFit hρ h.hfit)⟩

/-- The pieces of a list of machine pieces. -/
noncomputable def topPiecesR {ρ K n R₂ : ℕ} (hρ : ρ < K) :
    (pcs : List TopPc) → (∀ pc ∈ pcs, pc.OkR K n R₂) → List (Piece n R₂)
  | [], _ => []
  | pc :: pcs, h => pc.pieceR hρ (h pc List.mem_cons_self) ::
      topPiecesR hρ pcs (fun q hq => h q (List.mem_cons_of_mem _ hq))

/-- **One call** with a general result: `compactTopCallClr_exec` for `CallSpecF`. -/
theorem compactTopCallClrR_exec (body : P → Pr P (nT BReg) Q A U)
    (cp : Pr P (nT BReg) Q A U) (bc : BReg → List (Fin (A+4)) → Prop)
    {N r w K ρ R₀ j u a₀ cc : ℕ}
    (Fo : ZArr (Fin (rowsAt R₀ j) × Fin r) N → ZArr (Fin (rowsAt R₀ j) × Fin r) N)
    (hcall : CallSpecF body cp bc R₀ j u K ρ a₀ (K*bits u j) N r w Fo cc)
    (Z : ZArr (Fin (rowsAt R₀ j) × Fin r) N)
    (v : HS (nT BReg) Q A U) (S : Stacks (nT BReg) A)
    (hL : ∀ y, S.L y = []) (hpar : ParState S.R j u K ρ a₀ (K * bits u j) (rowsAt R₀ j) N w (r * w))
    (hrest : Rest bc N r w S.R) (hio : S.R (reg .io) = encZ A w Z) :
    ∃ (v' : HS (nT BReg) Q A U) (c : ℕ), v'.user = v.user ∧
      c ≤ cc +
        (2 * j + 2 * u + 2 * a₀ + 2 * (K * bits u j) + 2 * rowsAt R₀ j + 10) ∧
      Exec body (compactTopCallClr cp) (mk v S) c
        (mk v' { S with
          R := Function.update (Function.update (Function.update (Function.update (Function.update
            (Function.update S.R (reg .io) (encZ A w (Fo Z)))
            (reg .lev) []) (reg .u) []) (reg .a₀) []) (reg .L) []) (reg .rows) [] }) := by
  obtain ⟨v₁, c₁, hu₁, hc₁, e₁⟩ := hcall Z v S hL hpar hrest hio
  set X := encZ A w (Fo Z)
  set R₁ := Function.update S.R (reg .io) X with hR₁
  obtain ⟨v₂, hu₂, e₂⟩ := uclear_exec body (reg .lev) v₁ { S with R := R₁ }
  obtain ⟨v₃, hu₃, e₃⟩ := uclear_exec body (reg .u) v₂
    { S with R := Function.update R₁ (reg .lev) [] }
  obtain ⟨v₄, hu₄, e₄⟩ := uclear_exec body (reg .a₀) v₃
    { S with R := Function.update (Function.update R₁ (reg .lev) []) (reg .u) [] }
  obtain ⟨v₅, hu₅, e₅⟩ := uclear_exec body (reg .L) v₄
    { S with
      R := Function.update (Function.update (Function.update R₁ (reg .lev) []) (reg .u) [])
        (reg .a₀) [] }
  obtain ⟨v₆, hu₆, e₆⟩ := uclear_exec body (reg .rows) v₅
    { S with
      R := Function.update (Function.update (Function.update (Function.update R₁
        (reg .lev) []) (reg .u) []) (reg .a₀) []) (reg .L) [] }
  refine ⟨v₆, _, by rw [hu₆, hu₅, hu₄, hu₃, hu₂, hu₁], ?_,
    Exec.seq e₁ (Exec.seq e₂ (Exec.seq e₃ (Exec.seq e₄ (Exec.seq e₅ e₆))))⟩
  have h1 := hpar .lev
  have h2 := hpar .u
  have h3 := hpar .a₀
  have h4 := hpar .L
  have h5 := hpar .rows
  simp only [parSpec] at h1 h2 h3 h4 h5
  dsimp only
  simp only [hR₁]
  compactTopFupd
  rw [h1, h2, h3, h4, h5]
  omega

theorem compactTopPcBodyR_exec (body : P → Pr P (nT BReg) Q A U)
    (cp : Pr P (nT BReg) Q A U) (bc : BReg → List (Fin (A+4)) → Prop)
    (ds : ComplexFramedExecution.Directions) (cc : TopPc → ℕ)
    {cfg : List ℕ} {n r w K ρ R₂ : ℕ} (h4 : cfg[4]? = some R₂) (hρ : ρ < K) (pc : TopPc) (hok : pc.OkR K n R₂)
    (hcall : ∀ hfit : ∀ i<bits pc.u pc.j,pc.a₀+ρ+K*i<n,
      CallSpecF body cp bc pc.R₀ pc.j pc.u K ρ pc.a₀ (K*bits pc.u pc.j) n r w
      (layerRW w pc.u ds pc.R₀ pc.j (actMap pc.a₀ ρ K (bits pc.u pc.j) n hfit)) (cc pc)) (restPL : List (Fin (A + 4)))
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
            (encZ A w (pieceRW w (pc.pieceR hρ hok).u ds (pc.pieceR hρ hok).R₀
              (pc.pieceR hρ hok).j (pc.pieceR hρ hok).hR (pc.pieceR hρ hok).e Y))) (reg (.ph .arr))
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
  obtain ⟨v₆, c₆, hu₆, hc₆, e₆⟩ := compactTopCallClrR_exec body cp bc _
    (hcall (topFit hρ hok.hfit)) Z v₅ { S with R := F₅ } hL hpar hrest₅
    ((hF₅o .io (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)).trans
      (hio.trans (topEnc_cast hok.hR.symm Y).symm))
  set X := encZ A w (pieceRW w (pc.pieceR hρ hok).u ds (pc.pieceR hρ hok).R₀
    (pc.pieceR hρ hok).j (pc.pieceR hρ hok).hR (pc.pieceR hρ hok).e Y) with hX
  have hX' : encZ A w (layerRW w pc.u ds pc.R₀ pc.j
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

theorem compactTopPcLoopR_loop (body : P → Pr P (nT BReg) Q A U)
    (cp : Pr P (nT BReg) Q A U) (bc : BReg → List (Fin (A+4)) → Prop)
    (ds : ComplexFramedExecution.Directions) (cc : TopPc → ℕ)
    {cfg : List ℕ} {n r w K ρ R₂ : ℕ} (h4 : cfg[4]? = some R₂) (hρ : ρ < K) :
    ∀ (pcs : List TopPc) (hpcs : ∀ pc ∈ pcs, pc.OkR K n R₂)
      (_hcalls : ∀ pc∈pcs, ∀ hfit : ∀ i<bits pc.u pc.j,pc.a₀+ρ+K*i<n,
      CallSpecF body cp bc pc.R₀ pc.j pc.u K ρ pc.a₀ (K*bits pc.u pc.j) n r w
      (layerRW w pc.u ds pc.R₀ pc.j (actMap pc.a₀ ρ K (bits pc.u pc.j) n hfit)) (cc pc)) (Y : ZArr (Fin R₂ × Fin r) n)
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
              (encZ A w (piecesRW w ds (topPiecesR hρ pcs hpcs) Y))) (reg (.ph .arr)) [])
              (reg (.lf (.k .arr)))
              ((topRec (topPcRec K pcs)).reverse ++ S.R (reg (.lf (.k .arr)))) })
  | [], hpcs, hcalls, Y, v, S, hL, hT, hcf, hPL, hf, hio => by
      refine ⟨v, 1, rfl, le_refl _, ?_⟩
      have hS : ({ S with
          R := Function.update (Function.update (Function.update S.R (reg .io)
            (encZ A w (piecesRW w ds (topPiecesR hρ [] hpcs) Y))) (reg (.ph .arr)) [])
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
      obtain ⟨v₁, c₁, hu₁, hf₁, hc₁, e₁⟩ := compactTopPcBodyR_exec body cp bc ds cc h4 hρ pc
        hok (hcalls pc List.mem_cons_self) (topRec (topPcRec K pcs)) Y v S hL hT hcf hPL' hio
      set P := pc.pieceR hρ hok
      set Y' := pieceRW w P.u ds P.R₀ P.j P.hR P.e Y with hY'
      set S₁ : Stacks (nT BReg) A := { S with
        R := Function.update (Function.update (Function.update S.R (reg .io)
          (encZ A w Y')) (reg (.ph .arr)) (topRec (topPcRec K pcs)))
          (reg (.lf (.k .arr)))
          ((topRec (topPcFields K pc)).reverse ++ S.R (reg (.lf (.k .arr)))) } with hS₁
      have hT₁ : CompactTopRegs bc S₁.R n r w K ρ :=
        ((hT.update_store (Or.inl rfl) _).update_store (Or.inr (Or.inl rfl)) _).update_store
          (Or.inr (Or.inr rfl)) _
      obtain ⟨v₂, c₂, hu₂, hc₂, e₂⟩ := compactTopPcLoopR_loop body cp bc ds cc h4 hρ pcs
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
      split_ifs <;> simp_all [topPcRec, topRec_append, List.reverse_append, piecesRW, topPiecesR]
      rfl

theorem compactTopPcLoopR_exec (body : P → Pr P (nT BReg) Q A U)
    (cp : Pr P (nT BReg) Q A U) (bc : BReg → List (Fin (A+4)) → Prop)
    (ds : ComplexFramedExecution.Directions) (cc : TopPc → ℕ)
    {cfg : List ℕ} {n r w K ρ R₂ : ℕ} (h4 : cfg[4]? = some R₂) (hρ : ρ < K) (pcs : List TopPc) (hpcs : ∀ pc ∈ pcs, pc.OkR K n R₂)
    (hcalls : ∀ pc∈pcs, ∀ hfit : ∀ i<bits pc.u pc.j,pc.a₀+ρ+K*i<n,
      CallSpecF body cp bc pc.R₀ pc.j pc.u K ρ pc.a₀ (K*bits pc.u pc.j) n r w
      (layerRW w pc.u ds pc.R₀ pc.j (actMap pc.a₀ ρ K (bits pc.u pc.j) n hfit)) (cc pc))
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
            (encZ A w (piecesRW w ds (topPiecesR hρ pcs hpcs) Y)) }) := by
  have e₀ := Exec.act (body := body) (peekR (reg (.ph .arr)) : Act _ _ _ _) (mk v S)
  rw [peekR_run] at e₀
  obtain ⟨v₁, c₁, hu₁, hc₁, e₁⟩ := compactTopPcLoopR_loop body cp bc ds cc h4 hρ pcs hpcs hcalls Y
    { v with flag := (S.R (reg (.ph .arr))).head?.isSome } S hL hT hcf hPL rfl hio
  set R₁ := Function.update (Function.update (Function.update S.R (reg .io)
    (encZ A w (piecesRW w ds (topPiecesR hρ pcs hpcs) Y))) (reg (.ph .arr)) [])
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

theorem compactTopBlockSR_exec (body : P → Pr P (nT BReg) Q A U)
    (cp : Pr P (nT BReg) Q A U) (bc : BReg → List (Fin (A+4)) → Prop)
    (ds : ComplexFramedExecution.Directions) (cc : TopPc → ℕ)
    {cfg : List ℕ} {n a R R₂ r w K ρ : ℕ} (h2 : cfg[2]? = some a) (h3 : cfg[3]? = some R)
    (h4 : cfg[4]? = some R₂) (hρ : ρ < K) (hR₂ : R * 2 ^ a ≤ R₂)
    (pcs : List TopPc) (hpcs : ∀ pc ∈ pcs, pc.OkR K n R₂)
    (hcalls : ∀ pc∈pcs, ∀ hfit : ∀ i<bits pc.u pc.j,pc.a₀+ρ+K*i<n,
      CallSpecF body cp bc pc.R₀ pc.j pc.u K ρ pc.a₀ (K*bits pc.u pc.j) n r w
      (layerRW w pc.u ds pc.R₀ pc.j (actMap pc.a₀ ρ K (bits pc.u pc.j) n hfit)) (cc pc))
    (Y : ZArr (Fin (R * 2 ^ a) × Fin r) n) (v : HS (nT BReg) Q A U)
    (S : Stacks (nT BReg) A) (hL : ∀ y, S.L y = [])
    (hT : CompactTopRegs bc S.R (n + a) r w K ρ) (hI : CompactTopIn (BReg := BReg) S.R cfg (topPcRec K pcs))
    (hio : S.R (reg .io) = encZ A w Y) :
    ∃ (v' : HS (nT BReg) Q A U) (c : ℕ), v'.user = v.user ∧
      c ≤ compactTopBlockCost cfg K n a r w R R₂ cc pcs ∧
      Exec body (compactTopBlockS cp) (mk v S) c
        (mk v' { S with
          R := Function.update S.R (reg .io) (encZ A w
            (unpadRows hR₂ (piecesRW w ds (topPiecesR hρ pcs hpcs) (padRows R₂ Y)))) }) := by
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
  obtain ⟨v₃, c₃, hu₃, hc₃, e₃⟩ := compactTopPcLoopR_exec body cp bc ds cc h4 hρ pcs hpcs hcalls
    (padRows R₂ Y) v₂ { S with R := Function.update Rd (reg .io) (encZ A w
      (padRows R₂ Y)) } hL (hTd.update_io _)
    (by simpa [Function.update_of_ne (reg_ne (show LReg.park ≠ .io by simp))] using hcfd)
    (by dsimp only; rw [Function.update_of_ne (reg_ne (by simp)), hRd,
      compactTopDownR_of_ne (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)]; exact hI.pl)
    (by dsimp only; rw [Function.update_of_ne (reg_ne (by simp)), hRd,
      compactTopDownR_of_ne (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)]; exact hI.pb)
    (by simp)
  rw [Function.update_idem] at e₃
  set G := piecesRW w ds (topPiecesR hρ pcs hpcs) (padRows R₂ Y) with hG
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

/-! ### The guard, the cut and the shrinks -/

section Stages

variable {bc : BReg → List (Fin (A+4)) → Prop} (body : P → Pr P (nT BReg) Q A U)

/-- The guard: multiply the stream on `io` by `2^g`, `g` field `10` (`shiftInto` with `g` on
`sc 0` and `w' - g` on `sc 1`). -/
noncomputable def compactTopGuardS : Pr P (nT BReg) Q A U :=
  .seq (compactTopRd (reg (.sc 0)) 10)
  (.seq (ucopy (reg .w) (reg (.sc 1)) (reg .tS))
  (.seq (usub (reg (.sc 0)) (reg (.sc 1)) (reg .tS))
  (.seq (shiftInto (reg .io) (reg .rctmp) (reg .io) (reg (.sc 0)) (reg (.sc 1)) (reg .tS) (reg .tR)
      (pairSym A false false))
  (.seq (uclear (reg (.sc 0))) (uclear (reg (.sc 1)))))))

/-- The step bound of `compactTopGuardS`. -/
def compactTopGuardSCost (cfg : List ℕ) (R N r w' g : ℕ) : ℕ :=
  topGetCost cfg + (4 * w' + 4) + (4 * g + 4) + (R * 2 ^ N * r * (6 * w' + 4 * g + 14) + 4) +
    (2 * g + 2) + (2 * (w' - g) + 2)

theorem compactTopGuardS_exec {cfg pfs : List ℕ} {R N r w' K ρ g : ℕ}
    (h10 : cfg[10]? = some g) (hw' : 1 ≤ w') (hg : g ≤ w') (Z : ZArr (Fin R × Fin r) N)
    (v : HS (nT BReg) Q A U) (S : Stacks (nT BReg) A) (hT : CompactTopRegs bc S.R N r w' K ρ)
    (hI : CompactTopIn (BReg := BReg) S.R cfg pfs) (hio : S.R (reg .io) = encZ A w' Z) :
    ∃ (v' : HS (nT BReg) Q A U) (c : ℕ), v'.user = v.user ∧
      c ≤ compactTopGuardSCost cfg R N r w' g ∧
      Exec body compactTopGuardS (mk v S) c
        (mk v' { S with
          R := Function.update S.R (reg .io) (encZ A w' ((2 ^ g : GaussianInt) • Z)) }) := by
  have hl : 10 < cfg.length := (List.getElem?_eq_some_iff.1 h10).1
  have hc : cfg[10] = g := (List.getElem?_eq_some_iff.1 h10).2
  have hsc : ∀ i, S.R (reg (.sc i)) = [] := fun i => hT.rest (.sc i)
  have htS : S.R (reg .tS) = [] := hT.rest .tS
  have htR : S.R (reg .tR) = [] := hT.rest .tR
  have hlc : S.R (reg .lenctr) = [] := hT.rest .lenctr
  have hrc : S.R (reg .rctmp) = [] := hT.rest .rctmp
  obtain ⟨v₁, c₁, hu₁, hc₁, e₁⟩ := compactTopRd_exec body (x := .sc 0) (by simp) (by simp) 10 hl v S
    hlc hI.cf
  rw [hc, hsc 0, List.append_nil] at e₁
  set R₁ := Function.update S.R (reg (.sc 0)) (List.replicate g tick) with hR₁
  obtain ⟨v₂, hu₂, e₂⟩ := ucopy_exec body (a := reg .w) (b := reg (.sc 1)) (t := reg .tS)
    (reg_ne (by simp)) (reg_ne (by simp)) (reg_ne (by simp)) v₁ { S with R := R₁ }
    (by simp [hR₁, htS])
  dsimp only at e₂
  rw [show (R₁ (reg .w)).length = w' by simp [hR₁]; exact hT.hw,
    show R₁ (reg (.sc 1)) = [] by simp [hR₁, hsc], List.append_nil] at e₂
  set R₂ := Function.update R₁ (reg (.sc 1)) (List.replicate w' tick) with hR₂
  obtain ⟨v₃, hu₃, e₃⟩ := usub_exec body (a := reg (.sc 0)) (b := reg (.sc 1)) (t := reg .tS)
    (reg_ne (by simp)) (reg_ne (by simp)) (reg_ne (by simp)) v₂ { S with R := R₂ }
    (by simp [hR₂, hR₁, htS])
  dsimp only at e₃
  rw [show R₂ (reg (.sc 0)) = List.replicate g tick by simp [hR₂, hR₁],
    show R₂ (reg (.sc 1)) = List.replicate w' tick by simp [hR₂], List.length_replicate,
    List.drop_replicate] at e₃
  set R₃ := Function.update R₂ (reg (.sc 1)) (List.replicate (w' - g) tick) with hR₃
  obtain ⟨v₄, R₄, hu₄, -, e₄, hout₄, -, ho₄⟩ := shiftInto_exec body (reg .io) (reg .rctmp) (reg .io)
    (reg (.sc 0)) (reg (.sc 1)) (reg .tS) (reg .tR)
    (nodup_map_reg (l := [.io, .rctmp, .sc 0, .sc 1, .tS, .tR]) (by simp)) (reg_ne (by simp)) hw' hg
    (coeffList w' Z) v₃ { S with R := R₃ } (by simp [hR₃, hR₂, hR₁, hio]; rfl)
    (by simp [hR₃, hR₂, hR₁]) (by simp [hR₃]) (by simp [hR₃, hR₂, hR₁, htS])
    (by simp [hR₃, hR₂, hR₁, htR]) (by simp [hR₃, hR₂, hR₁, hrc])
  rw [length_coeffList] at e₄
  simp only [ite_true] at hout₄
  rw [← encZ_two_pow_smul] at hout₄
  obtain ⟨v₅, hu₅, e₅⟩ := uclear_exec body (reg (.sc 0)) v₄ { S with R := R₄ }
  obtain ⟨v₆, hu₆, e₆⟩ := uclear_exec body (reg (.sc 1)) v₅
    { S with R := Function.update R₄ (reg (.sc 0)) [] }
  have h40 : R₄ (reg (.sc 0)) = List.replicate g tick := by
    rw [ho₄ _ (reg_ne (by simp)) (reg_ne (by simp))]; simp [hR₃, hR₂, hR₁]
  have h41 : R₄ (reg (.sc 1)) = List.replicate (w' - g) tick := by
    rw [ho₄ _ (reg_ne (by simp)) (reg_ne (by simp))]; simp [hR₃]
  refine ⟨v₆, _, by rw [hu₆, hu₅, hu₄, hu₃, hu₂, hu₁], ?_,
    Exec.cast (Exec.seq e₁ (Exec.seq e₂ (Exec.seq e₃ (Exec.seq e₄ (Exec.seq e₅ e₆))))) rfl ?_⟩
  · dsimp only
    rw [Function.update_of_ne (reg_ne (by simp)), h41, h40]
    simp only [List.length_replicate]
    unfold compactTopGuardSCost
    omega
  · congr 2
    funext k
    by_cases h1 : k = reg (.sc 1)
    · subst h1; simp [hsc]
    by_cases h0 : k = reg (.sc 0)
    · subst h0; simp [hsc]
    by_cases hi : k = reg .io
    · subst hi; simp [hout₄]
    simp only [Function.update_of_ne h1, Function.update_of_ne h0, Function.update_of_ne hi]
    rw [ho₄ k hi hi]
    simp [hR₃, hR₂, hR₁, h0, h1]

/-- The cut: truncate the stream on `io` by `2^s'`, `s'` field `11`, keeping `w'` bits (the
truncating shift to `w' - s'` bits and the widening back). -/
noncomputable def compactTopCutS : Pr P (nT BReg) Q A U :=
  .seq (compactTopRd (reg (.sc 0)) 11)
  (.seq (ucopy (reg .w) (reg (.sc 1)) (reg .tS))
  (.seq (usub (reg (.sc 0)) (reg (.sc 1)) (reg .tS))
  (.seq (topPass (reg .io) (reg .rctmp) (topShiftWord (reg .io) (reg .rctmp) (reg .racc) (reg .w)
      (reg (.sc 0)) (reg (.sc 1)) (reg (.sc 2)) (reg (.sc 3)) (reg (.sc 4)) (reg (.sc 5))))
  (.seq (topPass (reg .io) (reg .rctmp)
      (topWidenWord (reg .io) (reg .rctmp) (reg (.sc 1)) (reg (.sc 0)) (reg (.sc 3))))
  (.seq (uclear (reg (.sc 0))) (uclear (reg (.sc 1))))))))

/-- The step bound of `compactTopCutS`. -/
def compactTopCutSCost (cfg : List ℕ) (R N r w' s' : ℕ) : ℕ :=
  topGetCost cfg + (4 * w' + 4) + (4 * s' + 4) + topShiftCost R N r w' s' (w' - s') +
    topWidenCost R N r (w' - s') w' + (2 * s' + 2) + (2 * (w' - s') + 2)

theorem compactTopCutS_exec (hA : 4 ≤ A) {cfg pfs : List ℕ} {R N r w' K ρ s' : ℕ}
    (h11 : cfg[11]? = some s') (hsw : s' < w') (Z : ZArr (Fin R × Fin r) N)
    (hZ : ∀ p, TopFitsZ w' (Z p))
    (v : HS (nT BReg) Q A U) (S : Stacks (nT BReg) A) (hT : CompactTopRegs bc S.R N r w' K ρ)
    (hI : CompactTopIn (BReg := BReg) S.R cfg pfs) (hio : S.R (reg .io) = encZ A w' Z) :
    ∃ (v' : HS (nT BReg) Q A U) (c : ℕ), v'.user = v.user ∧
      c ≤ compactTopCutSCost cfg R N r w' s' ∧
      Exec body compactTopCutS (mk v S) c
        (mk v' { S with
          R := Function.update S.R (reg .io) (encZ A w' (fun p => tdivZ s' (Z p))) }) := by
  have hl : 11 < cfg.length := (List.getElem?_eq_some_iff.1 h11).1
  have hc : cfg[11] = s' := (List.getElem?_eq_some_iff.1 h11).2
  have hsc : ∀ i, S.R (reg (.sc i)) = [] := fun i => hT.rest (.sc i)
  have htS : S.R (reg .tS) = [] := hT.rest .tS
  have hlc : S.R (reg .lenctr) = [] := hT.rest .lenctr
  have hrc : S.R (reg .rctmp) = [] := hT.rest .rctmp
  have hra : S.R (reg .racc) = [] := hT.rest .racc
  have hw1 : 1 ≤ w' := by omega
  obtain ⟨v₁, c₁, hu₁, hc₁, e₁⟩ := compactTopRd_exec body (x := .sc 0) (by simp) (by simp) 11 hl v S
    hlc hI.cf
  rw [hc, hsc 0, List.append_nil] at e₁
  set R₁ := Function.update S.R (reg (.sc 0)) (List.replicate s' tick) with hR₁
  obtain ⟨v₂, hu₂, e₂⟩ := ucopy_exec body (a := reg .w) (b := reg (.sc 1)) (t := reg .tS)
    (reg_ne (by simp)) (reg_ne (by simp)) (reg_ne (by simp)) v₁ { S with R := R₁ }
    (by simp [hR₁, htS])
  dsimp only at e₂
  rw [show (R₁ (reg .w)).length = w' by simp [hR₁]; exact hT.hw,
    show R₁ (reg (.sc 1)) = [] by simp [hR₁, hsc], List.append_nil] at e₂
  set R₂ := Function.update R₁ (reg (.sc 1)) (List.replicate w' tick) with hR₂
  obtain ⟨v₃, hu₃, e₃⟩ := usub_exec body (a := reg (.sc 0)) (b := reg (.sc 1)) (t := reg .tS)
    (reg_ne (by simp)) (reg_ne (by simp)) (reg_ne (by simp)) v₂ { S with R := R₂ }
    (by simp [hR₂, hR₁, htS])
  dsimp only at e₃
  rw [show R₂ (reg (.sc 0)) = List.replicate s' tick by simp [hR₂, hR₁],
    show R₂ (reg (.sc 1)) = List.replicate w' tick by simp [hR₂], List.length_replicate,
    List.drop_replicate] at e₃
  set R₃ := Function.update R₂ (reg (.sc 1)) (List.replicate (w' - s') tick) with hR₃
  obtain ⟨v₄, hu₄, e₄⟩ := topShiftP_exec body hA (src := reg .io) (dst := reg .rctmp)
    (tmp := reg .racc) (cW := reg .w) (cS := reg (.sc 0)) (cE := reg (.sc 1)) (cD := reg (.sc 2))
    (sp := reg (.sc 3)) (sg := reg (.sc 4)) (cy := reg (.sc 5))
    (nodup_map_reg (l := [.io, .rctmp, .racc, .w, .sc 0, .sc 1, .sc 2, .sc 3, .sc 4, .sc 5])
      (by simp)) hw1 (show s' + (w' - s') ≤ w' by omega) Z hZ v₃ { S with R := R₃ }
    (by simp [hR₃, hR₂, hR₁, hio]) (by simp [hR₃, hR₂, hR₁, hrc])
    ⟨by simp [hR₃, hR₂, hR₁]; exact hT.hw, by simp [hR₃, hR₂, hR₁], by simp [hR₃],
      by simp [hR₃, hR₂, hR₁, hsc], by simp [hR₃, hR₂, hR₁, hsc], by simp [hR₃, hR₂, hR₁, hsc],
      by simp [hR₃, hR₂, hR₁, hsc], by simp [hR₃, hR₂, hR₁, hra]⟩
  set R₄ := Function.update R₃ (reg .io) (encZ A (w' - s') (fun p => tdivZ s' (Z p))) with hR₄
  obtain ⟨v₅, hu₅, e₅⟩ := topWidenP_exec body (src := reg .io) (dst := reg .rctmp)
    (c₁ := reg (.sc 1)) (c₂ := reg (.sc 0)) (sp := reg (.sc 3))
    (nodup_map_reg (l := [.io, .rctmp, .sc 1, .sc 0, .sc 3]) (by simp)) (w := w' - s') (w' := w')
    (by omega) (by omega) (fun p => tdivZ s' (Z p))
    (fun p => topFitsZ_tdivZ hsw (hZ p)) v₄ { S with R := R₄ }
    (by simp [hR₄]) (by simp [hR₄, hR₃, hR₂, hR₁, hrc])
    ⟨by simp [hR₄, hR₃], by simp [hR₄, hR₃, hR₂, hR₁]; omega, by simp [hR₄, hR₃, hR₂, hR₁, hsc]⟩
  set R₅ := Function.update R₄ (reg .io) (encZ A w' (fun p => tdivZ s' (Z p))) with hR₅
  obtain ⟨v₆, hu₆, e₆⟩ := uclear_exec body (reg (.sc 0)) v₅ { S with R := R₅ }
  obtain ⟨v₇, hu₇, e₇⟩ := uclear_exec body (reg (.sc 1)) v₆
    { S with R := Function.update R₅ (reg (.sc 0)) [] }
  refine ⟨v₇, _, by rw [hu₇, hu₆, hu₅, hu₄, hu₃, hu₂, hu₁], ?_,
    Exec.cast (Exec.seq e₁ (Exec.seq e₂ (Exec.seq e₃ (Exec.seq e₄ (Exec.seq e₅
      (Exec.seq e₆ e₇)))))) rfl ?_⟩
  · simp only [hR₅, hR₄, hR₃, hR₂, hR₁]
    compactTopFupd
    simp only [List.length_replicate]
    unfold compactTopCutSCost
    omega
  · congr 2
    funext k
    by_cases h1 : k = reg (.sc 1)
    · subst h1; simp [hsc]
    by_cases h0 : k = reg (.sc 0)
    · subst h0; simp [hsc]
    simp [hR₅, hR₄, hR₃, hR₂, hR₁, Function.update_apply, h0, h1]

lemma topFitsZ_iterate_shrink {w' : ℕ} {z : GaussianInt} (hz : TopFitsZ w' z) :
    ∀ j, TopFitsZ w' ((shrinkZ 1)^[j] z)
  | 0 => hz
  | j + 1 => by
      rw [Function.iterate_succ_apply']
      exact topFitsZ_shrinkZ_one (topFitsZ_iterate_shrink hz j)

/-- The shrinks: `k` passes of `shrinkP`, `k` field `12` (counted on `sc 0`, spare `sc 1`). -/
noncomputable def compactTopShrinkS : Pr P (nT BReg) Q A U :=
  .seq (compactTopRd (reg (.sc 0)) 12)
  (.seq (scanP (reg (.sc 0)) (reg (.sc 1)) (topPass (reg .io) (reg .rctmp)
      (shrWord (reg .io) (reg .rctmp) (reg .racc) (reg .w) (reg (.sc 3)) (reg (.sc 4))
        (reg (.sc 5)))))
    (uclear (reg (.sc 0))))

/-- The step bound of `compactTopShrinkS`. -/
def compactTopShrinkSCost (cfg : List ℕ) (R N r w' k : ℕ) : ℕ :=
  topGetCost cfg + (k * (shrinkCost R N r w' + 3) + 2 * k + 4) + (2 * k + 2)

theorem compactTopShrinkS_exec (hA : 4 ≤ A) {cfg pfs : List ℕ} {R N r w' K ρ k : ℕ}
    (h12 : cfg[12]? = some k) (hw' : 1 ≤ w') (Z : ZArr (Fin R × Fin r) N)
    (hZ : ∀ p, TopFitsZ w' (Z p))
    (v : HS (nT BReg) Q A U) (S : Stacks (nT BReg) A) (hT : CompactTopRegs bc S.R N r w' K ρ)
    (hI : CompactTopIn (BReg := BReg) S.R cfg pfs) (hio : S.R (reg .io) = encZ A w' Z) :
    ∃ (v' : HS (nT BReg) Q A U) (c : ℕ), v'.user = v.user ∧
      c ≤ compactTopShrinkSCost cfg R N r w' k ∧
      Exec body compactTopShrinkS (mk v S) c
        (mk v' { S with
          R := Function.update S.R (reg .io) (encZ A w' (fun p => shrinkZ k (Z p))) }) := by
  have hl : 12 < cfg.length := (List.getElem?_eq_some_iff.1 h12).1
  have hc : cfg[12] = k := (List.getElem?_eq_some_iff.1 h12).2
  have hsc : ∀ i, S.R (reg (.sc i)) = [] := fun i => hT.rest (.sc i)
  have hlc : S.R (reg .lenctr) = [] := hT.rest .lenctr
  have hrc : S.R (reg .rctmp) = [] := hT.rest .rctmp
  have hra : S.R (reg .racc) = [] := hT.rest .racc
  obtain ⟨v₁, c₁, hu₁, hc₁, e₁⟩ := compactTopRd_exec body (x := .sc 0) (by simp) (by simp) 12 hl v S
    hlc hI.cf
  rw [hc, hsc 0, List.append_nil] at e₁
  set R₁ := Function.update S.R (reg (.sc 0)) (List.replicate k tick) with hR₁
  set Ψ : ℕ → Fin (nT BReg) → List (Fin (A + 4)) := fun j =>
    Function.update R₁ (reg .io) (encZ A w' (fun p => (shrinkZ 1)^[j] (Z p))) with hΨ
  have hp : IterSpec body (topPass (reg .io) (reg .rctmp)
      (shrWord (reg .io) (reg .rctmp) (reg .racc) (reg .w) (reg (.sc 3)) (reg (.sc 4))
        (reg (.sc 5)))) (reg (.sc 0)) (reg (.sc 1)) Ψ (fun _ => shrinkCost R N r w') k := by
    intro j _ v' S' hS'
    have hS : ∀ x : LReg BReg, x ≠ .sc 0 → x ≠ .sc 1 → S'.R (reg x) = Ψ j (reg x) :=
      fun x h0 h1 => hS' _ (reg_ne h0) (reg_ne h1)
    obtain ⟨v'', hu, he⟩ := shrinkP_exec body hA (src := reg .io) (dst := reg .rctmp)
      (tmp := reg .racc) (cW := reg .w) (sp := reg (.sc 3)) (sg := reg (.sc 4)) (cy := reg (.sc 5))
      (nodup_map_reg (l := [.io, .rctmp, .racc, .w, .sc 3, .sc 4, .sc 5]) (by simp)) hw'
      (fun p => (shrinkZ 1)^[j] (Z p)) (fun p => topFitsZ_iterate_shrink (hZ p) j) v' S'
      (by rw [hS _ (by simp) (by simp)]; simp [hΨ])
      (by rw [hS _ (by simp) (by simp)]; simp [hΨ, hR₁, hrc])
      ⟨by rw [hS _ (by simp) (by simp)]; simp [hΨ, hR₁]; exact hT.hw,
        by rw [hS _ (by simp) (by simp)]; simp [hΨ, hR₁, hsc],
        by rw [hS _ (by simp) (by simp)]; simp [hΨ, hR₁, hsc],
        by rw [hS _ (by simp) (by simp)]; simp [hΨ, hR₁, hsc],
        by rw [hS _ (by simp) (by simp)]; simp [hΨ, hR₁, hra]⟩
    refine ⟨v'', _, _, hu, le_refl _, he, by simp, by simp, ?_⟩
    intro q h0 h1
    by_cases hq : q = reg .io
    · subst hq
      simp only [Function.update_self, hΨ]
      congr 1
      funext p
      rw [Function.iterate_succ_apply']
    · rw [Function.update_of_ne hq, hS' q h0 h1, hΨ]
      simp only [Function.update_of_ne hq]
  obtain ⟨v₂, R₂, c₂, hu₂, hc₂, e₂, ha₂, ht₂, hΨ₂⟩ := scanP_exec body (reg_ne (by simp)) hp 0 v₁
    { S with R := R₁ } (by simp [hR₁])
    (fun q h0 h1 => by
      dsimp only
      simp only [hΨ, Function.iterate_zero, id]
      by_cases hq : q = reg .io
      · subst hq; simp [hR₁, hio]
      · simp [Function.update_of_ne hq])
  obtain ⟨v₃, hu₃, e₃⟩ := uclear_exec body (reg (.sc 0)) v₂ { S with R := R₂ }
  refine ⟨v₃, _, by rw [hu₃, hu₂, hu₁], ?_, Exec.cast (Exec.seq e₁ (Exec.seq e₂ e₃)) rfl ?_⟩
  · have h0 : (R₁ (reg (.sc 0))).length = k := by simp [hR₁]
    have h1 : R₁ (reg (.sc 1)) = [] := by simp [hR₁, hsc]
    dsimp only
    rw [ha₂]
    simp only [h0, h1, List.length_nil, List.reverse_nil, List.nil_append,
      Finset.sum_const, Finset.card_range, smul_eq_mul, Nat.mul_zero] at hc₂ ⊢
    unfold compactTopShrinkSCost
    omega
  · congr 2
    funext q
    dsimp only
    by_cases h0 : q = reg (.sc 0)
    · subst h0; simp [hsc]
    rw [Function.update_of_ne h0]
    by_cases h1 : q = reg (.sc 1)
    · subst h1; rw [ht₂]; simp [hsc]
    rw [hΨ₂ q h0 h1, hΨ]
    simp only [zero_add, hR₁]
    by_cases hq : q = reg .io
    · subst hq; simp only [Function.update_self]
      congr 1; funext p; rw [shrinkZ_iterate, List.length_replicate]
    · rw [Function.update_of_ne hq, Function.update_of_ne hq, Function.update_of_ne h0]

/-- The final shift with its amount already on `sc 0`. -/
noncomputable def compactTopShiftTail : Pr P (nT BReg) Q A U :=
  .seq (compactTopRd (reg (.sc 1)) 0)
  (.seq (ucopy (reg .w) (reg (.sc 2)) (reg .tS))
  (.seq (usub (reg (.sc 0)) (reg (.sc 2)) (reg .tS))
  (.seq (usub (reg (.sc 1)) (reg (.sc 2)) (reg .tS))
  (.seq (topPass (reg .io) (reg .rctmp) (topShiftWord (reg .io) (reg .rctmp) (reg .racc) (reg .w)
      (reg (.sc 0)) (reg (.sc 1)) (reg (.sc 2)) (reg (.sc 3)) (reg (.sc 4)) (reg (.sc 5))))
  (.seq (uclear (reg (.sc 0))) (.seq (uclear (reg (.sc 1))) (uclear (reg (.sc 2)))))))))

/-- The step bound of `compactTopShiftTail`. -/
def compactTopShiftTailCost (cfg : List ℕ) (R N r w' s w : ℕ) : ℕ :=
  topGetCost cfg + (4 * w' + 4) + (4 * s + 4) + (4 * w + 4) + topShiftCost R N r w' s w +
    (2 * s + 2) + (2 * w + 2) + (2 * (w' - s - w) + 2)

theorem compactTopShiftTail_exec (hA : 4 ≤ A) {cfg pfs : List ℕ} {R N r w' K ρ s w : ℕ}
    (h0 : cfg[0]? = some w) (hw' : 1 ≤ w') (hsw : s + w ≤ w')
    (Z : ZArr (Fin R × Fin r) N) (hZ : ∀ p, TopFitsZ w' (Z p))
    (v₁ : HS (nT BReg) Q A U) (S : Stacks (nT BReg) A) (hT : CompactTopRegs bc S.R N r w' K ρ)
    (hI : CompactTopIn (BReg := BReg) S.R cfg pfs) (hio : S.R (reg .io) = encZ A w' Z) :
    ∃ (v' : HS (nT BReg) Q A U) (c : ℕ), v'.user = v₁.user ∧
      c ≤ compactTopShiftTailCost cfg R N r w' s w ∧
      Exec body compactTopShiftTail
        (mk v₁ { S with R := Function.update S.R (reg (.sc 0)) (List.replicate s tick) }) c
        (mk v' { S with
          R := Function.update S.R (reg .io) (encZ A w (fun p => tdivZ s (Z p))) }) := by
  have hl0 : 0 < cfg.length := (List.getElem?_eq_some_iff.1 h0).1
  have hc0 : cfg[0] = w := (List.getElem?_eq_some_iff.1 h0).2
  have hsc : ∀ i, S.R (reg (.sc i)) = [] := fun i => hT.rest (.sc i)
  have htS : S.R (reg .tS) = [] := hT.rest .tS
  have hlc : S.R (reg .lenctr) = [] := hT.rest .lenctr
  set R₁ := Function.update S.R (reg (.sc 0)) (List.replicate s tick) with hR₁
  obtain ⟨v₂, c₂, hu₂, hc₂, e₂⟩ := compactTopRd_exec body (x := .sc 1) (by simp) (by simp) 0 hl0 v₁
    { S with R := R₁ } (by simp [hR₁, hlc]) (by simpa [hR₁] using hI.cf)
  dsimp only at e₂
  rw [hc0, show R₁ (reg (.sc 1)) = [] by simp [hR₁, hsc], List.append_nil] at e₂
  set R₂ := Function.update R₁ (reg (.sc 1)) (List.replicate w tick) with hR₂
  obtain ⟨v₃, hu₃, e₃⟩ := ucopy_exec body (a := reg .w) (b := reg (.sc 2)) (t := reg .tS)
    (reg_ne (by simp)) (reg_ne (by simp)) (reg_ne (by simp)) v₂ { S with R := R₂ }
    (by simp [hR₂, hR₁, htS])
  dsimp only at e₃
  rw [show (R₂ (reg .w)).length = w' by simp [hR₂, hR₁]; exact hT.hw,
    show R₂ (reg (.sc 2)) = [] by simp [hR₂, hR₁, hsc], List.append_nil] at e₃
  set R₃ := Function.update R₂ (reg (.sc 2)) (List.replicate w' tick) with hR₃
  obtain ⟨v₄, hu₄, e₄⟩ := usub_exec body (a := reg (.sc 0)) (b := reg (.sc 2)) (t := reg .tS)
    (reg_ne (by simp)) (reg_ne (by simp)) (reg_ne (by simp)) v₃ { S with R := R₃ }
    (by simp [hR₃, hR₂, hR₁, htS])
  dsimp only at e₄
  rw [show R₃ (reg (.sc 0)) = List.replicate s tick by simp [hR₃, hR₂, hR₁],
    show R₃ (reg (.sc 2)) = List.replicate w' tick by simp [hR₃], List.length_replicate,
    List.drop_replicate] at e₄
  set R₄ := Function.update R₃ (reg (.sc 2)) (List.replicate (w' - s) tick) with hR₄
  obtain ⟨v₅, hu₅, e₅⟩ := usub_exec body (a := reg (.sc 1)) (b := reg (.sc 2)) (t := reg .tS)
    (reg_ne (by simp)) (reg_ne (by simp)) (reg_ne (by simp)) v₄ { S with R := R₄ }
    (by simp [hR₄, hR₃, hR₂, hR₁, htS])
  dsimp only at e₅
  rw [show R₄ (reg (.sc 1)) = List.replicate w tick by simp [hR₄, hR₃, hR₂],
    show R₄ (reg (.sc 2)) = List.replicate (w' - s) tick by simp [hR₄], List.length_replicate,
    List.drop_replicate] at e₅
  set R₅ := Function.update R₄ (reg (.sc 2)) (List.replicate (w' - s - w) tick) with hR₅
  obtain ⟨v₆, hu₆, e₆⟩ := topShiftP_exec body hA (src := reg .io) (dst := reg .rctmp)
    (tmp := reg .racc) (cW := reg .w) (cS := reg (.sc 0)) (cE := reg (.sc 1)) (cD := reg (.sc 2))
    (sp := reg (.sc 3)) (sg := reg (.sc 4)) (cy := reg (.sc 5))
    (nodup_map_reg (l := [.io, .rctmp, .racc, .w, .sc 0, .sc 1, .sc 2, .sc 3, .sc 4, .sc 5])
      (by simp)) hw' hsw Z hZ v₅ { S with R := R₅ }
    (by simp [hR₅, hR₄, hR₃, hR₂, hR₁, hio])
    (by have h : S.R (reg .rctmp) = [] := hT.rest .rctmp; simp [hR₅, hR₄, hR₃, hR₂, hR₁, h])
    ⟨by simp [hR₅, hR₄, hR₃, hR₂, hR₁]; exact hT.hw, by simp [hR₅, hR₄, hR₃, hR₂, hR₁],
      by simp [hR₅, hR₄, hR₃, hR₂], by simp [hR₅], by simp [hR₅, hR₄, hR₃, hR₂, hR₁, hsc],
      by simp [hR₅, hR₄, hR₃, hR₂, hR₁, hsc], by simp [hR₅, hR₄, hR₃, hR₂, hR₁, hsc],
      by have h : S.R (reg .racc) = [] := hT.rest .racc; simp [hR₅, hR₄, hR₃, hR₂, hR₁, h]⟩
  set R₆ := Function.update R₅ (reg .io) (encZ A w (fun p => tdivZ s (Z p))) with hR₆
  obtain ⟨v₇, hu₇, e₇⟩ := uclear_exec body (reg (.sc 0)) v₆ { S with R := R₆ }
  obtain ⟨v₈, hu₈, e₈⟩ := uclear_exec body (reg (.sc 1)) v₇
    { S with R := Function.update R₆ (reg (.sc 0)) [] }
  obtain ⟨v₉, hu₉, e₉⟩ := uclear_exec body (reg (.sc 2)) v₈
    { S with R := Function.update (Function.update R₆ (reg (.sc 0)) []) (reg (.sc 1)) [] }
  refine ⟨v₉, _, by rw [hu₉, hu₈, hu₇, hu₆, hu₅, hu₄, hu₃, hu₂], ?_,
    Exec.cast ((Exec.seq e₂ (Exec.seq e₃ (Exec.seq e₄ (Exec.seq e₅ (Exec.seq e₆
      (Exec.seq e₇ (Exec.seq e₈ e₉)))))))) rfl ?_⟩
  · simp only [hR₆, hR₅, hR₄, hR₃, hR₂, hR₁]
    compactTopFupd
    simp only [List.length_replicate]
    unfold compactTopShiftTailCost
    omega
  · congr 2
    funext k
    by_cases h2 : k = reg (.sc 2)
    · subst h2; simp [hsc]
    by_cases h1 : k = reg (.sc 1)
    · subst h1; simp [hsc]
    by_cases h0 : k = reg (.sc 0)
    · subst h0; simp [hsc]
    simp [hR₆, hR₅, hR₄, hR₃, hR₂, hR₁, Function.update_apply, h0, h1, h2]


/-- The final shift of the rounded top: the remaining shift `s - s'` (fields `1` and `11`) on
`sc 0`, then `compactTopShiftTail`. -/
noncomputable def compactTopShiftSR : Pr P (nT BReg) Q A U :=
  .seq (compactTopRd (reg (.sc 0)) 1)
  (.seq (compactTopRd (reg (.sc 1)) 11)
  (.seq (usub (reg (.sc 1)) (reg (.sc 0)) (reg .tS))
  (.seq (uclear (reg (.sc 1))) compactTopShiftTail)))

/-- The step bound of `compactTopShiftSR`. -/
def compactTopShiftSRCost (cfg : List ℕ) (R N r w' s s' w : ℕ) : ℕ :=
  2 * topGetCost cfg + (4 * s' + 4) + (2 * s' + 2) + compactTopShiftTailCost cfg R N r w' (s - s') w

theorem compactTopShiftSR_exec (hA : 4 ≤ A) {cfg pfs : List ℕ} {R N r w' K ρ s s' w : ℕ}
    (h0 : cfg[0]? = some w) (h1 : cfg[1]? = some s) (h11 : cfg[11]? = some s')
    (hw' : 1 ≤ w') (hsw : (s - s') + w ≤ w')
    (Z : ZArr (Fin R × Fin r) N) (hZ : ∀ p, TopFitsZ w' (Z p))
    (v : HS (nT BReg) Q A U) (S : Stacks (nT BReg) A) (hT : CompactTopRegs bc S.R N r w' K ρ)
    (hI : CompactTopIn (BReg := BReg) S.R cfg pfs) (hio : S.R (reg .io) = encZ A w' Z) :
    ∃ (v' : HS (nT BReg) Q A U) (c : ℕ), v'.user = v.user ∧
      c ≤ compactTopShiftSRCost cfg R N r w' s s' w ∧
      Exec body compactTopShiftSR (mk v S) c
        (mk v' { S with
          R := Function.update S.R (reg .io) (encZ A w (fun p => tdivZ (s - s') (Z p))) }) := by
  have hl1 : 1 < cfg.length := (List.getElem?_eq_some_iff.1 h1).1
  have hl11 : 11 < cfg.length := (List.getElem?_eq_some_iff.1 h11).1
  have hc1 : cfg[1] = s := (List.getElem?_eq_some_iff.1 h1).2
  have hc11 : cfg[11] = s' := (List.getElem?_eq_some_iff.1 h11).2
  have hsc : ∀ i, S.R (reg (.sc i)) = [] := fun i => hT.rest (.sc i)
  have htS : S.R (reg .tS) = [] := hT.rest .tS
  have hlc : S.R (reg .lenctr) = [] := hT.rest .lenctr
  obtain ⟨v₁, c₁, hu₁, hc₁, e₁⟩ := compactTopRd_exec body (x := .sc 0) (by simp) (by simp) 1 hl1 v S
    hlc hI.cf
  rw [hc1, hsc 0, List.append_nil] at e₁
  set R₁ := Function.update S.R (reg (.sc 0)) (List.replicate s tick) with hR₁
  obtain ⟨v₂, c₂, hu₂, hc₂, e₂⟩ := compactTopRd_exec body (x := .sc 1) (by simp) (by simp) 11 hl11
    v₁ { S with R := R₁ } (by simp [hR₁, hlc]) (by simpa [hR₁] using hI.cf)
  dsimp only at e₂
  rw [hc11, show R₁ (reg (.sc 1)) = [] by simp [hR₁, hsc], List.append_nil] at e₂
  set R₂ := Function.update R₁ (reg (.sc 1)) (List.replicate s' tick) with hR₂
  obtain ⟨v₃, hu₃, e₃⟩ := usub_exec body (a := reg (.sc 1)) (b := reg (.sc 0)) (t := reg .tS)
    (reg_ne (by simp)) (reg_ne (by simp)) (reg_ne (by simp)) v₂ { S with R := R₂ }
    (by simp [hR₂, hR₁, htS])
  dsimp only at e₃
  rw [show R₂ (reg (.sc 1)) = List.replicate s' tick by simp [hR₂],
    show R₂ (reg (.sc 0)) = List.replicate s tick by simp [hR₂, hR₁], List.length_replicate,
    List.drop_replicate] at e₃
  set R₃ := Function.update R₂ (reg (.sc 0)) (List.replicate (s - s') tick) with hR₃
  obtain ⟨v₄, hu₄, e₄⟩ := uclear_exec body (reg (.sc 1)) v₃ { S with R := R₃ }
  have hR₄ : Function.update R₃ (reg (.sc 1)) [] =
      Function.update S.R (reg (.sc 0)) (List.replicate (s - s') tick) := by
    funext k
    simp only [hR₃, hR₂, hR₁, Function.update_apply]
    split_ifs with h1 h2 <;> simp_all
  obtain ⟨v₅, c₅, hu₅, hc₅, e₅⟩ := compactTopShiftTail_exec body hA (cfg := cfg) h0 hw' hsw Z hZ v₄
    S hT hI hio
  refine ⟨v₅, _, by rw [hu₅, hu₄, hu₃, hu₂, hu₁], ?_,
    Exec.seq e₁ (Exec.seq e₂ (Exec.seq e₃ (Exec.seq e₄ (by rw [hR₄]; exact e₅))))⟩
  rw [show (R₃ (reg (.sc 1))).length = s' by simp [hR₃, hR₂]]
  unfold compactTopShiftSRCost
  omega

end Stages

/-- At level `0` the layer of the tape is the exact layer: a `CallSpecF` with result `layerRW` is a
`CallSpec` (for the top kernels). -/
lemma CallSpecF.callSpec_zero {body : P → Pr P (nT BReg) Q A U} {cp : Pr P (nT BReg) Q A U}
    {bc : BReg → List (Fin (A+4)) → Prop} {ds : ComplexFramedExecution.Directions}
    {R₀ u K ρ a₀ L n r w cc : ℕ} (hfit : ∀ i < bits u 0, a₀ + ρ + K * i < n)
    (h : CallSpecF body cp bc R₀ 0 u K ρ a₀ L n r w
      (layerRW w u ds R₀ 0 (actMap a₀ ρ K (bits u 0) n hfit)) cc) :
    CallSpec body cp bc ds R₀ 0 u K ρ a₀ L n r w hfit cc := h

/-! ### The rounded top program -/

/-- The configuration record of the rounded top: `topCfg` with the total shift `s`, then the
guard `g`, the cut `s'` and the shrink count `k`; the final shift is `s - s'`. -/
def topCfgR (w s a R R₂ q aT K oS D g s' k : ℕ) : List ℕ :=
  topCfg w s a R R₂ q aT K oS D ++ [g, s', k]

/-- **The rounded host machine of the simultaneous layer**: widening, the phase, the guard, the
top kernels, the pieces, the phase, the unit, the cut, the shrinks and the final shift. -/
noncomputable def compactTopProgR (cp : Pr P (nT BReg) Q A U) : Pr P (nT BReg) Q A U :=
  .seq compactTopWidenS (.seq compactTopPhaseS (.seq compactTopGuardS (.seq (compactTopKerS cp)
    (.seq (compactTopBlockS cp) (.seq compactTopPhaseS (.seq compactTopUnitS (.seq compactTopCutS
      (.seq compactTopShrinkS compactTopShiftSR))))))))

/-- The step bound of `compactTopProgR`: the sum of the stage bounds. -/
def compactTopCostR (w w' s n a R r K ρ q aT oS D R₂ g s' k : ℕ) (pcs : List TopPc) (kc : ℕ)
    (cc : TopPc → ℕ) : ℕ :=
  compactTopWidenSCost (topCfgR w s a R R₂ q aT K oS D g s' k) R (n + a) r w w' +
    compactTopPhaseSCost (topCfgR w s a R R₂ q aT K oS D g s' k) (n + a) R r w' K ρ oS D +
    compactTopGuardSCost (topCfgR w s a R R₂ q aT K oS D g s' k) R (n + a) r w' g +
    compactTopKerSCost (topCfgR w s a R R₂ q aT K oS D g s' k) K R q aT kc +
    compactTopBlockCost (topCfgR w s a R R₂ q aT K oS D g s' k) K n a r w' R R₂ cc pcs +
    compactTopPhaseSCost (topCfgR w s a R R₂ q aT K oS D g s' k) (n + a) R r w' K ρ oS D +
    compactTopUnitSCost (topCfgR w s a R R₂ q aT K oS D g s' k) R (n + a) r w' D +
    compactTopCutSCost (topCfgR w s a R R₂ q aT K oS D g s' k) R (n + a) r w' s' +
    compactTopShrinkSCost (topCfgR w s a R R₂ q aT K oS D g s' k) R (n + a) r w' k +
    compactTopShiftSRCost (topCfgR w s a R R₂ q aT K oS D g s' k) R (n + a) r w' s s' w

lemma topFitsZ_mono' {k k' : ℕ} (hk : 1 ≤ k) (hkk : k ≤ k') {z : GaussianInt}
    (hz : TopFitsZ k z) : TopFitsZ k' z :=
  ⟨topFits_mono hk hkk hz.1, topFits_mono hk hkk hz.2⟩

/-- **The rounded host machine** (`compactTopProgR`). As `compactTopProg_exec`, with the
configuration `topCfgR w s a R R₂ q aT K oS D g s' k`, the pieces calling a layer program with
result `layerRW w'` (`CallSpecF`), `g ≤ w'`, `s' < w'`, `(s - s') + w ≤ w'` and the array
before the shifts fitting `w'` signed bits: the machine leaves on `io` the `w`-bit stream of
`tdivZ (s - s') (shrinkZ k (tdivZ s' (topPreRW …)))`. -/
theorem compactTopProgR_exec (body : P → Pr P (nT BReg) Q A U)
    (cp : Pr P (nT BReg) Q A U) (bc : BReg → List (Fin (A+4)) → Prop)
    (ds : ComplexFramedExecution.Directions) (kc : ℕ) (cc : TopPc → ℕ)
    (hA : 21 ≤ A)
    {w w' s n a R r K ρ q aT oS D R₂ g s' k : ℕ} (low : List (Fin n)) (pcs : List TopPc)
    (hr : 1 ≤ r) (hw : 1 ≤ w) (hsw : (s - s') + w ≤ w') (hg : g ≤ w') (hs' : s' < w') (hρ : ρ < K)
    (hfitT : ∀ i < q, aT + ρ + K * i < n + a)
    (hR₂ : R * 2 ^ a ≤ R₂) (hpcs : ∀ pc ∈ pcs, pc.OkR K n R₂)
    (hkernel : 1≤q → CallSpec body cp bc ds R 0 q K ρ aT (K*q) (n+a) r w'
      (by simpa only [bits] using hfitT) kc)
    (hcalls : ∀ pc∈pcs, ∀ hfit : ∀ i<bits pc.u pc.j,pc.a₀+ρ+K*i<n,
      CallSpecF body cp bc pc.R₀ pc.j pc.u K ρ pc.a₀ (K*bits pc.u pc.j) n r w'
        (layerRW w' pc.u ds pc.R₀ pc.j (actMap pc.a₀ ρ K (bits pc.u pc.j) n hfit)) (cc pc))
    (hselm : ∀ t : Fin (n + a), t ∈ topSel a low (topTop aT ρ K q (n + a) hfitT) ↔
      ∃ i < D, (t : ℕ) = ρ + oS + K * i)
    (hsel : (topSel a low (topTop aT ρ K q (n + a) hfitT)).Nodup)
    (hD : (topSel a low (topTop aT ρ K q (n + a) hfitT)).length = D)
    (Z : ZArr (Fin R × Fin r) (n + a)) (hZ : ∀ p, TopFitsZ w (Z p))
    (hX : ∀ p, TopFitsZ w' (topPreRW ds w' a low (topTop aT ρ K q (n + a) hfitT) hR₂
      (topPiecesR hρ pcs hpcs) g Z p))
    (v : HS (nT BReg) Q A U) (S : Stacks (nT BReg) A)
    (hL : ∀ y, S.L y = []) (hT : CompactTopRegs bc S.R (n + a) r w' K ρ)
    (hI : CompactTopIn (BReg := BReg) S.R (topCfgR w s a R R₂ q aT K oS D g s' k)
      (topPcRec K pcs))
    (hio : S.R (reg .io) = encZ A w Z) :
    ∃ (v' : HS (nT BReg) Q A U) (c : ℕ), v'.user = v.user ∧
      c ≤ compactTopCostR w w' s n a R r K ρ q aT oS D R₂ g s' k pcs kc cc ∧
      Exec body (compactTopProgR cp) (mk v S) c
        (mk v' { S with
          R := Function.update S.R (reg .io) (encZ A w (fun p => tdivZ (s - s') (shrinkZ k (tdivZ s'
            (topPreRW ds w' a low (topTop aT ρ K q (n + a) hfitT) hR₂
              (topPiecesR hρ pcs hpcs) g Z p))))) }) := by
  set cfg := topCfgR w s a R R₂ q aT K oS D g s' k with hcfg
  set top := topTop aT ρ K q (n + a) hfitT with htop
  set sel := topSel a low top with hseldef
  set Ps := topPiecesR hρ pcs hpcs with hPs
  have hw' : 1 ≤ w' := by omega
  have hK : 1 ≤ K := by omega
  have hA5 : 5 ≤ A := by omega
  have hA4 : 4 ≤ A := by omega
  have hmask : topMaskOf (n + a) ρ K oS D = topSelMask sel := topMaskOf_eq hK sel hselm
  have hT' : ∀ X, CompactTopRegs bc (Function.update S.R (reg .io) X) (n + a) r w' K ρ :=
    fun X => hT.update_io X
  have hI' : ∀ X, CompactTopIn (BReg := BReg) (Function.update S.R (reg .io) X) cfg
      (topPcRec K pcs) := fun X => hI.update_io X
  -- the arrays
  set Z₁ := sZ sel Z with hZ₁
  set Z₁g := (2 ^ g : GaussianInt) • Z₁ with hZ₁g
  set Z₂ := k2s top Z₁g with hZ₂
  set G := unpadRows hR₂ (piecesRW w' ds Ps (padRows R₂ (toRows a Z₂))) with hG
  set Z₃ := ofRows a G with hZ₃
  set Z₄ := sZ sel Z₃ with hZ₄
  set Z₅ := topPreRW ds w' a low top hR₂ Ps g Z with hZ₅
  have hZ₅e : Z₅ = fun p => unitD D * Z₄ p := by rw [hZ₅, ← hD]; rfl
  set Z₆ := fun p => tdivZ s' (Z₅ p) with hZ₆
  set Z₇ := fun p => shrinkZ k (Z₆ p) with hZ₇
  have hZ₆f : ∀ p, TopFitsZ w' (Z₆ p) := fun p =>
    topFitsZ_mono' (by omega) (Nat.sub_le w' s') (topFitsZ_tdivZ hs' (hX p))
  have hZ₇f : ∀ p, TopFitsZ w' (Z₇ p) := fun p => by
    simp only [hZ₇]; rw [shrinkZ_iterate]; exact topFitsZ_iterate_shrink (hZ₆f p) k
  -- 1. widen
  obtain ⟨v₁, c₁, hu₁, hc₁, e₁⟩ := compactTopWidenS_exec body (cfg := cfg)
    (by simp [hcfg, topCfgR, topCfg]) hw (by omega : w ≤ w') Z hZ v S hT hI hio
  -- 2. phase
  obtain ⟨v₂, c₂, hu₂, hc₂, e₂⟩ := compactTopPhaseS_exec body hA5 (cfg := cfg) (R := R) (oS := oS)
    (D := D)
    (by simp [hcfg, topCfgR, topCfg]) (by simp [hcfg, topCfgR, topCfg])
    (by simp [hcfg, topCfgR, topCfg]) hr hw' hK Z v₁
    { S with R := Function.update S.R (reg .io) (encZ A w' Z) } (hT' _) (hI' _)
    (by simp)
  rw [hmask, topPhase_sZ sel hsel, topIo] at e₂
  -- 3. the guard
  obtain ⟨v₃, c₃, hu₃, hc₃, e₃⟩ := compactTopGuardS_exec body (cfg := cfg)
    (by simp [hcfg, topCfgR, topCfg]) hw' hg Z₁ v₂
    { S with R := Function.update S.R (reg .io) (encZ A w' Z₁) } (hT' _) (hI' _) (by simp)
  rw [topIo] at e₃
  -- 4. the top kernels
  obtain ⟨v₄, c₄, hu₄, hc₄, e₄⟩ := compactTopKerS_exec body cp bc ds kc (cfg := cfg)
    (by simp [hcfg, topCfgR, topCfg]) (by simp [hcfg, topCfgR, topCfg])
    (by simp [hcfg, topCfgR, topCfg]) (by simp [hcfg, topCfgR, topCfg]) hfitT hkernel Z₁g v₃
    { S with R := Function.update S.R (reg .io) (encZ A w' Z₁g) } hL (hT' _) (hI' _)
    (by simp)
  rw [topIo] at e₄
  -- 5. the pieces with the top bits as rows
  obtain ⟨v₅, c₅, hu₅, hc₅, e₅⟩ := compactTopBlockSR_exec body cp bc ds cc (cfg := cfg)
    (by simp [hcfg, topCfgR, topCfg]) (by simp [hcfg, topCfgR, topCfg])
    (by simp [hcfg, topCfgR, topCfg]) hρ hR₂ pcs hpcs hcalls (toRows a Z₂) v₄
    { S with R := Function.update S.R (reg .io) (encZ A w' Z₂) } hL (hT' _) (hI' _)
    (by simp [topEnc_toRows])
  rw [topIo, ← hG, ← topEnc_ofRows a G, ← hZ₃] at e₅
  -- 6. phase
  obtain ⟨v₆, c₆, hu₆, hc₆, e₆⟩ := compactTopPhaseS_exec body hA5 (cfg := cfg) (R := R) (oS := oS)
    (D := D)
    (by simp [hcfg, topCfgR, topCfg]) (by simp [hcfg, topCfgR, topCfg])
    (by simp [hcfg, topCfgR, topCfg]) hr hw' hK Z₃ v₅
    { S with R := Function.update S.R (reg .io) (encZ A w' Z₃) } (hT' _) (hI' _)
    (by simp)
  rw [hmask, topPhase_sZ sel hsel, topIo] at e₆
  -- 7. the unit
  obtain ⟨v₇, c₇, hu₇, hc₇, e₇⟩ := compactTopUnitS_exec body hA (cfg := cfg) (D := D)
    (by simp [hcfg, topCfgR, topCfg]) hw' Z₄ v₆
    { S with R := Function.update S.R (reg .io) (encZ A w' Z₄) } (hT' _) (hI' _)
    (by simp)
  rw [topIo, ← hZ₅e] at e₇
  -- 8. the cut
  obtain ⟨v₈, c₈, hu₈, hc₈, e₈⟩ := compactTopCutS_exec body hA4 (cfg := cfg)
    (by simp [hcfg, topCfgR, topCfg]) hs' Z₅ hX v₇
    { S with R := Function.update S.R (reg .io) (encZ A w' Z₅) } (hT' _) (hI' _) (by simp)
  rw [topIo] at e₈
  -- 9. the shrinks
  obtain ⟨v₉, c₉, hu₉, hc₉, e₉⟩ := compactTopShrinkS_exec body hA4 (cfg := cfg) (k := k)
    (by simp [hcfg, topCfgR, topCfg]) hw' Z₆ hZ₆f v₈
    { S with R := Function.update S.R (reg .io) (encZ A w' Z₆) } (hT' _) (hI' _) (by simp)
  rw [topIo] at e₉
  -- 10. the final shift
  obtain ⟨v₁₀, c₁₀, hu₁₀, hc₁₀, e₁₀⟩ := compactTopShiftSR_exec body hA4 (cfg := cfg)
    (by simp [hcfg, topCfgR, topCfg]) (by simp [hcfg, topCfgR, topCfg])
    (by simp [hcfg, topCfgR, topCfg]) hw' hsw Z₇ hZ₇f v₉
    { S with R := Function.update S.R (reg .io) (encZ A w' Z₇) } (hT' _) (hI' _) (by simp)
  rw [topIo] at e₁₀
  refine ⟨v₁₀, _, by rw [hu₁₀, hu₉, hu₈, hu₇, hu₆, hu₅, hu₄, hu₃, hu₂, hu₁], ?_,
    Exec.cast (Exec.seq e₁ (Exec.seq e₂ (Exec.seq e₃ (Exec.seq e₄ (Exec.seq e₅ (Exec.seq e₆
      (Exec.seq e₇ (Exec.seq e₈ (Exec.seq e₉ e₁₀))))))))) rfl rfl⟩
  unfold compactTopCostR
  rw [← hcfg]
  omega

/-- **The rounded layer.** `compactTopProgR_exec` with the shrink identity: the machine leaves on
`io` the stream of `topRSW … s (k 2^s') Z`, the shrink by `k 2^s'` before the shift by `2^s`,
for `s' ≤ s`. -/
theorem compactTopProgR_exec_RS (body : P → Pr P (nT BReg) Q A U)
    (cp : Pr P (nT BReg) Q A U) (bc : BReg → List (Fin (A+4)) → Prop)
    (ds : ComplexFramedExecution.Directions) (kc : ℕ) (cc : TopPc → ℕ)
    (hA : 21 ≤ A)
    {w w' s n a R r K ρ q aT oS D R₂ g s' k : ℕ} (low : List (Fin n)) (pcs : List TopPc)
    (hr : 1 ≤ r) (hw : 1 ≤ w) (hsw : (s - s') + w ≤ w') (hg : g ≤ w') (hs' : s' < w')
    (hss : s' ≤ s) (hρ : ρ < K)
    (hfitT : ∀ i < q, aT + ρ + K * i < n + a)
    (hR₂ : R * 2 ^ a ≤ R₂) (hpcs : ∀ pc ∈ pcs, pc.OkR K n R₂)
    (hkernel : 1≤q → CallSpec body cp bc ds R 0 q K ρ aT (K*q) (n+a) r w'
      (by simpa only [bits] using hfitT) kc)
    (hcalls : ∀ pc∈pcs, ∀ hfit : ∀ i<bits pc.u pc.j,pc.a₀+ρ+K*i<n,
      CallSpecF body cp bc pc.R₀ pc.j pc.u K ρ pc.a₀ (K*bits pc.u pc.j) n r w'
        (layerRW w' pc.u ds pc.R₀ pc.j (actMap pc.a₀ ρ K (bits pc.u pc.j) n hfit)) (cc pc))
    (hselm : ∀ t : Fin (n + a), t ∈ topSel a low (topTop aT ρ K q (n + a) hfitT) ↔
      ∃ i < D, (t : ℕ) = ρ + oS + K * i)
    (hsel : (topSel a low (topTop aT ρ K q (n + a) hfitT)).Nodup)
    (hD : (topSel a low (topTop aT ρ K q (n + a) hfitT)).length = D)
    (Z : ZArr (Fin R × Fin r) (n + a)) (hZ : ∀ p, TopFitsZ w (Z p))
    (hX : ∀ p, TopFitsZ w' (topPreRW ds w' a low (topTop aT ρ K q (n + a) hfitT) hR₂
      (topPiecesR hρ pcs hpcs) g Z p))
    (v : HS (nT BReg) Q A U) (S : Stacks (nT BReg) A)
    (hL : ∀ y, S.L y = []) (hT : CompactTopRegs bc S.R (n + a) r w' K ρ)
    (hI : CompactTopIn (BReg := BReg) S.R (topCfgR w s a R R₂ q aT K oS D g s' k)
      (topPcRec K pcs))
    (hio : S.R (reg .io) = encZ A w Z) :
    ∃ (v' : HS (nT BReg) Q A U) (c : ℕ), v'.user = v.user ∧
      c ≤ compactTopCostR w w' s n a R r K ρ q aT oS D R₂ g s' k pcs kc cc ∧
      Exec body (compactTopProgR cp) (mk v S) c
        (mk v' { S with
          R := Function.update S.R (reg .io) (encZ A w (topRSW ds w' a low
            (topTop aT ρ K q (n + a) hfitT) hR₂ (topPiecesR hρ pcs hpcs) g s (k * 2 ^ s')
              Z)) }) := by
  obtain ⟨v', c, hu, hc, he⟩ := compactTopProgR_exec body cp bc ds kc cc hA low pcs hr hw hsw hg
    hs' hρ hfitT hR₂ hpcs hkernel hcalls hselm hsel hD Z hZ hX v S hL hT hI hio
  refine ⟨v', c, hu, hc, Exec.cast he rfl ?_⟩
  congr 4
  funext p
  rw [← tdiv_shrink_mul k s' (s - s') _, Nat.add_sub_cancel' hss]
  rfl

end
end IntegerMultBounds.MathlibTM2.LayerMachine
