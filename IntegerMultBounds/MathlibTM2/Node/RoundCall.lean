module

public import IntegerMultBounds.MathlibTM2.Node.Factor
public import IntegerMultBounds.MathlibTM2.Node.TopWord
public import IntegerMultBounds.MathlibTM2.Layer.LayerR

/-!
# The rounded child call

The rounded layer (`Layer/LayerR.lean`) truncates every child result by `2 ^ scaleR u ds j` and
runs its nodes with child exponent `0`. On the tape the words are `w` bits wide, so a child
result is known modulo `2 ^ w`: the truncation acts on the symmetric representative
(`symZ w`, both parts in `[-2^(w-1), 2^(w-1))`), which is the true value whenever the true value
fits `w` signed bits (`symI_eq`).

**Truncation** (`truncP`, `truncP_exec`). At the parameters of level `j`, `s = scaleR u ds j` is
`expSeq G 0 u j` with `G` the gate count (`scaleR_eq_expSeq`): `expProg G 0` builds it on `sc 0`,
`w - s` goes on `sc 1`, the truncating shift (`topShiftP_exec`) maps the `w`-bit stream of
`symArr w X` to the `w - s`-bit stream of its truncation, and the widening pass (`topWidenP_exec`)
returns to `w` bits. So `io` goes from `encZ A w X` to `encZ A w (tdivArr s (symArr w X))`, for any
representative `X`, provided `s < w`.

**Calls.** `CallSpecF … Fo cc` is `CallSpec` with an arbitrary result `Fo`; `CallSpecF.trunc`
appends `truncP`. `callCoreR`, `childCallR` are `callCore`, `childCall` with an empty `Tc`
register: `callPostR` only restores `a₀` and `lev`.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.LayerMachine

open IntegerMultBounds IntegerMultBounds.Networks IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Layer
open IntegerMultBounds.MathlibTM2.Node hiding LReg

/-- Evaluate register updates at register names. -/
local macro "fupd" : tactic => `(tactic| (simp only [Function.update_apply, reg_inj, reduceCtorEq,
  ↓reduceIte, eq_self_iff_true, LReg.sc.injEq, LReg.wire.injEq, LReg.wtmp.injEq, LReg.bc.injEq,
  LReg.ph.injEq, LReg.lf.injEq, Fin.reduceEq, Fin.isValue, movedR, List.map_id, id]) <;> try rfl)

/-! ### Symmetric representatives -/

section Sym

/-- The representative of `x` modulo `2 ^ w` in `[-2^(w-1), 2^(w-1))`. -/
def symI (w : ℕ) (x : ℤ) : ℤ := (x + 2 ^ (w - 1)) % 2 ^ w - 2 ^ (w - 1)

/-- The symmetric representative of both parts. -/
def symZ (w : ℕ) (z : GaussianInt) : GaussianInt := ⟨symI w z.re, symI w z.im⟩

/-- The symmetric representative of every entry. -/
def symArr {Y : Type} {n : ℕ} (w : ℕ) (f : ZArr Y n) : ZArr Y n := fun p => symZ w (f p)

lemma two_pow_eq_two_mul {w : ℕ} (hw : 1 ≤ w) : (2 : ℤ) ^ w = 2 * 2 ^ (w - 1) := by
  rw [← pow_succ']; congr 1; omega

lemma symI_fits {w : ℕ} (hw : 1 ≤ w) (x : ℤ) : TopFits w (symI w x) := by
  have h2 := two_pow_eq_two_mul hw
  have hpos : (0 : ℤ) < 2 ^ w := by positivity
  have h0 := Int.emod_nonneg (x + 2 ^ (w - 1)) hpos.ne'
  have h1 := Int.emod_lt_of_pos (x + 2 ^ (w - 1)) hpos
  unfold TopFits symI
  constructor <;> linarith

lemma symI_cast (w : ℕ) (x : ℤ) : ((symI w x : ℤ) : ZMod (2 ^ w)) = (x : ZMod (2 ^ w)) := by
  unfold symI
  rw [Int.emod_def]
  push_cast
  have h : ((2 : ZMod (2 ^ w)) ^ w) = 0 := by exact_mod_cast ZMod.natCast_self (2 ^ w)
  rw [h]; ring

/-- A value fitting `w` signed bits is its own symmetric representative. -/
lemma symI_eq {w : ℕ} (hw : 1 ≤ w) {x : ℤ} (hx : TopFits w x) : symI w x = x := by
  have h2 := two_pow_eq_two_mul hw
  obtain ⟨h0, h1⟩ := hx
  unfold symI
  rw [Int.emod_eq_of_lt (by linarith) (by linarith)]
  ring

lemma red_symZ (w : ℕ) (z : GaussianInt) : red w (symZ w z) = red w z := by
  simp only [red, symZ, symI_cast]

lemma topFitsZ_symZ {w : ℕ} (hw : 1 ≤ w) (z : GaussianInt) : TopFitsZ w (symZ w z) :=
  ⟨symI_fits hw _, symI_fits hw _⟩

lemma symZ_eq {w : ℕ} (hw : 1 ≤ w) {z : GaussianInt} (hz : TopFitsZ w z) : symZ w z = z := by
  unfold symZ; rw [symI_eq hw hz.1, symI_eq hw hz.2]

lemma encZ_symArr {A R r n : ℕ} (w : ℕ) (X : ZArr (Fin R × Fin r) n) :
    encZ A w (symArr w X) = encZ A w X := by
  simp only [encZ, coeffList_eq_map, symArr, red_symZ]

/-- Truncation by `2 ^ s` takes `w` signed bits to `w - s`. -/
lemma topFits_tdiv {w s : ℕ} (hs : s < w) {x : ℤ} (hx : TopFits w x) :
    TopFits (w - s) (x.tdiv (2 ^ s)) := by
  have hM : (2 : ℤ) ^ (w - 1) = 2 ^ (w - s - 1) * 2 ^ s := by
    rw [← pow_add]; congr 1; omega
  have hd : (0 : ℤ) < 2 ^ s := by positivity
  have hM0 : (0 : ℤ) < 2 ^ (w - s - 1) := by positivity
  obtain ⟨h0, h1⟩ := hx
  unfold TopFits
  rcases le_or_gt 0 x with hx0 | hx0
  · rw [Int.tdiv_eq_ediv_of_nonneg hx0]
    have := Int.ediv_nonneg hx0 hd.le
    refine ⟨by linarith, Int.ediv_lt_of_lt_mul hd (by linarith)⟩
  · have hneg : x.tdiv (2 ^ s) = -((-x) / 2 ^ s) := by
      rw [← Int.tdiv_eq_ediv_of_nonneg (by linarith), Int.neg_tdiv, neg_neg]
    rw [hneg]
    have h3 : (-x) / 2 ^ s ≤ 2 ^ (w - s - 1) := Int.ediv_le_of_le_mul hd (by linarith)
    have h4 := Int.ediv_nonneg (show 0 ≤ -x by linarith) hd.le
    constructor <;> linarith

lemma topFitsZ_tdivZ {w s : ℕ} (hs : s < w) {z : GaussianInt} (hz : TopFitsZ w z) :
    TopFitsZ (w - s) (tdivZ s z) :=
  ⟨topFits_tdiv hs hz.1, topFits_tdiv hs hz.2⟩

/-- The scale of the rounded layer is the exponent sequence with the gate count and no factor
term. -/
lemma scaleR_eq_expSeq (u : ℕ) (ds : ComplexFramedExecution.Directions) (j : ℕ) :
    scaleR u ds j = expSeq (gateCount (program ds)) 0 u j := by
  cases j with
  | zero => rfl
  | succ j => simp [scaleR, expSeq, nodeExp, progExp_eq]

end Sym

/-! ### Truncation on the tape -/

section Trunc

variable {BReg : Type} [Fintype BReg] {Q A : ℕ} {U P : Type}
  (body : P → Pr P (nT BReg) Q A U)

/-- Truncate the stream on `io` by `2 ^ s`, `s = expSeq G 0 |u| |lev|`: `s` on `sc 0` and `w - s`
on `sc 1`, the truncating shift from `w` to `w - s` bits (spares `rctmp`, `racc`, `sc 2`–`sc 5`),
the widening back to `w` bits, and `sc 0`, `sc 1` cleared. -/
noncomputable def truncP (G : ℕ) : Pr P (nT BReg) Q A U :=
  .seq (expProg G 0 (reg .u) (reg .lev) (reg (.sc 0)) (reg (.sc 3)) (reg (.sc 4)) (reg (.sc 5)))
  (.seq (ucopy (reg .w) (reg (.sc 1)) (reg .tS))
  (.seq (usub (reg (.sc 0)) (reg (.sc 1)) (reg .tS))
  (.seq (topPass (reg .io) (reg .rctmp) (topShiftWord (reg .io) (reg .rctmp) (reg .racc) (reg .w)
      (reg (.sc 0)) (reg (.sc 1)) (reg (.sc 2)) (reg (.sc 3)) (reg (.sc 4)) (reg (.sc 5))))
  (.seq (topPass (reg .io) (reg .rctmp)
      (topWidenWord (reg .io) (reg .rctmp) (reg (.sc 1)) (reg (.sc 0)) (reg (.sc 3))))
  (.seq (uclear (reg (.sc 0))) (uclear (reg (.sc 1))))))))

/-- The step bound of `truncP` at level `j` on arrays of `R` rows. -/
def truncCost (G u j R n r w : ℕ) : ℕ :=
  expCost G 0 u j + (4 * w + 4) + (4 * expSeq G 0 u j + 4) +
    topShiftCost R n r w (expSeq G 0 u j) (w - expSeq G 0 u j) +
    topWidenCost R n r (w - expSeq G 0 u j) w + (2 * expSeq G 0 u j + 2) +
    (2 * (w - expSeq G 0 u j) + 2)

/-- **Truncation.** With `u`, `lev`, `w` holding `u`, `j`, `w` symbols, `s = expSeq G 0 u j < w`,
the scratch registers empty and `io` the `w`-bit stream of `X`, `truncP G` leaves on `io` the
`w`-bit stream of `tdivArr s (symArr w X)`; every other register and `user` end as they
started. -/
theorem truncP_exec (hA : 4 ≤ A) (G : ℕ) {R r n w u j : ℕ} (hsw : expSeq G 0 u j < w)
    (X : ZArr (Fin R × Fin r) n) (v : HS (nT BReg) Q A U) (S : Stacks (nT BReg) A)
    (hu : (S.R (reg .u)).length = u) (hlev : (S.R (reg .lev)).length = j)
    (hw : (S.R (reg .w)).length = w) (hsc : ∀ i, S.R (reg (.sc i)) = [])
    (htS : S.R (reg .tS) = []) (hrc : S.R (reg .rctmp) = []) (hra : S.R (reg .racc) = [])
    (hio : S.R (reg .io) = encZ A w X) :
    ∃ (v' : HS (nT BReg) Q A U) (c : ℕ), v'.user = v.user ∧ c ≤ truncCost G u j R n r w ∧
      Exec body (truncP G) (mk v S) c (mk v' { S with
        R := Function.update S.R (reg .io)
          (encZ A w (tdivArr (expSeq G 0 u j) (symArr w X))) }) := by
  set s := expSeq G 0 u j with hs
  have hw1 : 1 ≤ w := by omega
  obtain ⟨v₁, m₁, hu₁, hm₁, e₁⟩ := expProg_exec body G 0 (uR := reg .u) (jR := reg .lev)
    (eR := reg (.sc 0)) (t₁ := reg (.sc 3)) (t₂ := reg (.sc 4)) (t₃ := reg (.sc 5))
    (nodup_map_reg (l := [.u, .lev, .sc 0, .sc 3, .sc 4, .sc 5]) (by simp)) v S (hsc 0) (hsc 3)
    (hsc 4) (hsc 5)
  rw [hu, hlev] at e₁ hm₁
  set R₁ := Function.update S.R (reg (.sc 0)) (List.replicate s tick) with hR₁
  obtain ⟨v₂, hu₂, e₂⟩ := ucopy_exec body (a := reg .w) (b := reg (.sc 1)) (t := reg .tS)
    (reg_ne (by simp)) (reg_ne (by simp)) (reg_ne (by simp)) v₁ { S with R := R₁ }
    (by simp [hR₁, htS])
  dsimp only at e₂
  rw [show (R₁ (reg .w)).length = w by simp [hR₁, hw],
    show R₁ (reg (.sc 1)) = [] by simp [hR₁, hsc], List.append_nil] at e₂
  set R₂ := Function.update R₁ (reg (.sc 1)) (List.replicate w tick) with hR₂
  obtain ⟨v₃, hu₃, e₃⟩ := usub_exec body (a := reg (.sc 0)) (b := reg (.sc 1)) (t := reg .tS)
    (reg_ne (by simp)) (reg_ne (by simp)) (reg_ne (by simp)) v₂ { S with R := R₂ }
    (by simp [hR₂, hR₁, htS])
  dsimp only at e₃
  rw [show R₂ (reg (.sc 0)) = List.replicate s tick by simp [hR₂, hR₁],
    show R₂ (reg (.sc 1)) = List.replicate w tick by simp [hR₂], List.length_replicate,
    List.drop_replicate] at e₃
  set R₃ := Function.update R₂ (reg (.sc 1)) (List.replicate (w - s) tick) with hR₃
  obtain ⟨v₄, hu₄, e₄⟩ := topShiftP_exec body hA (src := reg .io) (dst := reg .rctmp)
    (tmp := reg .racc) (cW := reg .w) (cS := reg (.sc 0)) (cE := reg (.sc 1)) (cD := reg (.sc 2))
    (sp := reg (.sc 3)) (sg := reg (.sc 4)) (cy := reg (.sc 5))
    (nodup_map_reg (l := [.io, .rctmp, .racc, .w, .sc 0, .sc 1, .sc 2, .sc 3, .sc 4, .sc 5])
      (by simp)) hw1 (show s + (w - s) ≤ w by omega) (symArr w X)
    (fun _ => topFitsZ_symZ hw1 _) v₃ { S with R := R₃ }
    (by simp [hR₃, hR₂, hR₁, hio, encZ_symArr]) (by simp [hR₃, hR₂, hR₁, hrc])
    ⟨by simp [hR₃, hR₂, hR₁, hw], by simp [hR₃, hR₂, hR₁], by simp [hR₃],
      by simp [hR₃, hR₂, hR₁, hsc], by simp [hR₃, hR₂, hR₁, hsc], by simp [hR₃, hR₂, hR₁, hsc],
      by simp [hR₃, hR₂, hR₁, hsc], by simp [hR₃, hR₂, hR₁, hra]⟩
  set R₄ := Function.update R₃ (reg .io) (encZ A (w - s) (fun p => tdivZ s (symArr w X p)))
    with hR₄
  obtain ⟨v₅, hu₅, e₅⟩ := topWidenP_exec body (src := reg .io) (dst := reg .rctmp)
    (c₁ := reg (.sc 1)) (c₂ := reg (.sc 0)) (sp := reg (.sc 3))
    (nodup_map_reg (l := [.io, .rctmp, .sc 1, .sc 0, .sc 3]) (by simp)) (w := w - s) (w' := w)
    (by omega) (by omega) (fun p => tdivZ s (symArr w X p))
    (fun _ => topFitsZ_tdivZ hsw (topFitsZ_symZ hw1 _)) v₄ { S with R := R₄ }
    (by simp [hR₄]) (by simp [hR₄, hR₃, hR₂, hR₁, hrc])
    ⟨by simp [hR₄, hR₃], by simp [hR₄, hR₃, hR₂, hR₁]; omega, by simp [hR₄, hR₃, hR₂, hR₁, hsc]⟩
  set R₅ := Function.update R₄ (reg .io) (encZ A w (fun p => tdivZ s (symArr w X p))) with hR₅
  obtain ⟨v₆, hu₆, e₆⟩ := uclear_exec body (reg (.sc 0)) v₅ { S with R := R₅ }
  obtain ⟨v₇, hu₇, e₇⟩ := uclear_exec body (reg (.sc 1)) v₆
    { S with R := Function.update R₅ (reg (.sc 0)) [] }
  refine ⟨v₇, _, by rw [hu₇, hu₆, hu₅, hu₄, hu₃, hu₂, hu₁], ?_,
    Exec.cast (Exec.seq e₁ (Exec.seq e₂ (Exec.seq e₃ (Exec.seq e₄ (Exec.seq e₅
      (Exec.seq e₆ e₇)))))) rfl ?_⟩
  · simp only [hR₅, hR₄, hR₃, hR₂, hR₁]
    fupd
    simp only [List.length_replicate]
    have hm₁' : m₁ ≤ expCost G 0 u j := hm₁
    unfold truncCost
    simp only [← hs]
    omega
  · congr 2
    funext k
    by_cases h1 : k = reg (.sc 1)
    · subst h1; simp [hsc]
    by_cases h0 : k = reg (.sc 0)
    · subst h0; simp [hsc]
    simp [hR₅, hR₄, hR₃, hR₂, hR₁, Function.update_apply, h0, h1]; rfl

end Trunc

/-! ### Calls with general results -/

section CallR

variable {BReg : Type} [Fintype BReg] {Q A : ℕ} {U P : Type}
  (body : P → Pr P (nT BReg) Q A U)

/-- **Child programs with result `Fo`.** `CallSpec` with the layer replaced by `Fo`: from the
parameters of level `j`, every register at rest, every left stack empty and `io` holding the stream
of `Z`, the program `cp` ends with `io` holding the stream of `Fo Z`, every other register and
`user` as before, within `cc` steps. -/
def CallSpecF (cp : Pr P (nT BReg) Q A U) (bcRest : BReg → List (Fin (A + 4)) → Prop)
    (R₀ j u K ρ a₀ L n r w : ℕ)
    (Fo : ZArr (Fin (rowsAt R₀ j) × Fin r) n → ZArr (Fin (rowsAt R₀ j) × Fin r) n) (cc : ℕ) :
    Prop :=
  ∀ (Z : ZArr (Fin (rowsAt R₀ j) × Fin r) n) (v : HS (nT BReg) Q A U) (S : Stacks (nT BReg) A),
    (∀ y, S.L y = []) → ParState S.R j u K ρ a₀ L (rowsAt R₀ j) n w (r * w) →
    Rest bcRest n r w S.R → S.R (reg .io) = encZ A w Z →
    ∃ (v' : HS (nT BReg) Q A U) (c : ℕ), v'.user = v.user ∧ c ≤ cc ∧
      Exec body cp (mk v S) c (mk v' { S with
        R := Function.update S.R (reg .io) (encZ A w (Fo Z)) })

lemma CallSpecF.mono {cp : Pr P (nT BReg) Q A U} {bcRest : BReg → List (Fin (A + 4)) → Prop}
    {R₀ j u K ρ a₀ L n r w : ℕ}
    {Fo : ZArr (Fin (rowsAt R₀ j) × Fin r) n → ZArr (Fin (rowsAt R₀ j) × Fin r) n} {cc cc' : ℕ}
    (h : CallSpecF body cp bcRest R₀ j u K ρ a₀ L n r w Fo cc) (hc : cc ≤ cc') :
    CallSpecF body cp bcRest R₀ j u K ρ a₀ L n r w Fo cc' := fun Z v S hL hp hr hio => by
  obtain ⟨v', c, hu, hc', he⟩ := h Z v S hL hp hr hio
  exact ⟨v', c, hu, hc'.trans hc, he⟩

/-- **The truncated call.** `cp` followed by `truncP G` returns `tdivArr s (symArr w (Fo Z))`,
`s = expSeq G 0 u j < w`. -/
theorem CallSpecF.trunc (hA : 4 ≤ A) (G : ℕ) {cp : Pr P (nT BReg) Q A U}
    {bcRest : BReg → List (Fin (A + 4)) → Prop} {R₀ j u K ρ a₀ L n r w : ℕ}
    {Fo : ZArr (Fin (rowsAt R₀ j) × Fin r) n → ZArr (Fin (rowsAt R₀ j) × Fin r) n} {cc : ℕ}
    (hsw : expSeq G 0 u j < w) (h : CallSpecF body cp bcRest R₀ j u K ρ a₀ L n r w Fo cc) :
    CallSpecF body (.seq cp (truncP G)) bcRest R₀ j u K ρ a₀ L n r w
      (fun Z => tdivArr (expSeq G 0 u j) (symArr w (Fo Z)))
      (cc + truncCost G u j (rowsAt R₀ j) n r w) := by
  intro Z v S hL hpar hrest hio
  obtain ⟨v₁, c₁, hu₁, hc₁, e₁⟩ := h Z v S hL hpar hrest hio
  have hR : ∀ x : LReg BReg, x ≠ .io →
      Function.update S.R (reg .io) (encZ A w (Fo Z)) (reg x) = S.R (reg x) :=
    fun x hx => Function.update_of_ne (reg_ne hx) _ _
  obtain ⟨v₂, c₂, hu₂, hc₂, e₂⟩ := truncP_exec body hA G hsw (Fo Z) v₁
    { S with R := Function.update S.R (reg .io) (encZ A w (Fo Z)) }
    (by dsimp only; rw [hR _ (by simp)]; exact hpar .u)
    (by dsimp only; rw [hR _ (by simp)]; exact hpar .lev)
    (by dsimp only; rw [hR _ (by simp)]; exact hpar .w)
    (fun i => by dsimp only; rw [hR _ (by simp)]; exact hrest (.sc i))
    (by dsimp only; rw [hR _ (by simp)]; exact hrest .tS)
    (by dsimp only; rw [hR _ (by simp)]; exact hrest .rctmp)
    (by dsimp only; rw [hR _ (by simp)]; exact hrest .racc)
    (by dsimp only; rw [Function.update_self])
  refine ⟨v₂, c₁ + c₂, by rw [hu₂, hu₁], by omega, Exec.cast (Exec.seq e₁ e₂) rfl ?_⟩
  dsimp only
  rw [Function.update_idem]

/-- After a call with an empty `Tc`: `a₀` loses `s |L|` symbols and the top symbol of `park`
returns to `lev`. -/
noncomputable def callPostR (s : ℕ) : Pr P (nT BReg) Q A U :=
  .seq (umul s (reg .L) (reg .lenctr) (reg (.sc 1)))
  (.seq (usub (reg .lenctr) (reg .a₀) (reg (.sc 1)))
  (.seq (uclear (reg .lenctr))
    (.act (moveStep (reg .park) (reg .lev) id))))

theorem callPostR_exec (s : ℕ) {x₀ : Fin (A + 4)} {a p : List (Fin (A + 4))}
    (v : HS (nT BReg) Q A U) (S : Stacks (nT BReg) A) (hl : S.R (reg .lenctr) = [])
    (hs1 : S.R (reg (.sc 1)) = [])
    (ha : S.R (reg .a₀) = List.replicate (s * (S.R (reg .L)).length) tick ++ a)
    (hpark : S.R (reg .park) = x₀ :: p) :
    ∃ v' : HS (nT BReg) Q A U, v'.user = v.user ∧
      Exec body (callPostR s) (mk v S)
        ((4 * (S.R (reg .L)).length + 4) + ((4 * (s * (S.R (reg .L)).length) + 4) +
          ((2 * (s * (S.R (reg .L)).length) + 2) + 1)))
        (mk v' { S with
          R := Function.update (Function.update (Function.update S.R (reg .a₀) a) (reg .park) p)
            (reg .lev) (x₀ :: S.R (reg .lev)) }) := by
  set q := s * (S.R (reg .L)).length with hq
  obtain ⟨v₁, hu₁, he₁⟩ := umul_exec body s (a := reg .L) (b := reg .lenctr) (t := reg (.sc 1))
    (reg_ne (by simp)) (reg_ne (by simp)) (reg_ne (by simp)) v S hs1
  set R₁ := Function.update S.R (reg .lenctr) (List.replicate q tick ++ S.R (reg .lenctr))
    with hR₁
  obtain ⟨v₂, hu₂, he₂⟩ := usub_exec body (a := reg .lenctr) (b := reg .a₀) (t := reg (.sc 1))
    (reg_ne (by simp)) (reg_ne (by simp)) (reg_ne (by simp)) v₁ { S with R := R₁ }
    (by simp only [hR₁, Function.update_apply, reg_inj, reduceCtorEq, ↓reduceIte]; exact hs1)
  set R₂ := Function.update R₁ (reg .a₀) ((R₁ (reg .a₀)).drop (R₁ (reg .lenctr)).length)
    with hR₂
  obtain ⟨v₃, hu₃, he₃⟩ := uclear_exec body (reg .lenctr) v₂ { S with R := R₂ }
  set R₃ := Function.update R₂ (reg .lenctr) [] with hR₃
  have h3 : ∀ k, k ≠ reg .a₀ → R₃ k = S.R k := by
    intro k hk
    rw [hR₃, hR₂, Function.update_apply, Function.update_of_ne hk, hR₁, Function.update_apply]
    split_ifs with h
    · rw [h, hl]
    · rfl
  have h3a : R₃ (reg .a₀) = a := by
    rw [hR₃, Function.update_of_ne (reg_ne (by simp)), hR₂, Function.update_self, hR₁,
      Function.update_self, Function.update_of_ne (reg_ne (by simp)), ha, hl, List.append_nil,
      List.length_replicate, List.drop_left' (List.length_replicate ..)]
  have he₄ := Exec.act (body := body) (moveStep (reg .park) (reg .lev) id)
    (mk v₃ { S with R := R₃ })
  rw [moveStep_run (reg_ne (by simp)) id v₃ { S with R := R₃ }
    (by dsimp only; rw [h3 _ (reg_ne (by simp)), hpark])] at he₄
  refine ⟨{ v₃ with sym := some x₀, flag := p.head?.isSome },
    by show v₃.user = v.user; rw [hu₃, hu₂, hu₁],
    Exec.cast (Exec.seq he₁ (Exec.seq he₂ (Exec.seq he₃ he₄))) ?_ ?_⟩
  · have h1l : (R₁ (reg .lenctr)).length = q := by
      rw [hR₁, Function.update_self, hl, List.append_nil, List.length_replicate]
    have h2l : (R₂ (reg .lenctr)).length = q := by
      rw [hR₂, Function.update_of_ne (reg_ne (by simp)), h1l]
    dsimp only
    rw [h1l, h2l]
  · congr 2
    funext k
    dsimp only
    by_cases h1 : k = reg .lev
    · subst h1
      rw [Function.update_self, Function.update_self, h3 _ (reg_ne (by simp))]
      rfl
    rw [Function.update_of_ne h1, Function.update_of_ne h1]
    by_cases h2 : k = reg .park
    · subst h2
      rw [Function.update_self, Function.update_self]
    rw [Function.update_of_ne h2, Function.update_of_ne h2]
    by_cases h5 : k = reg .a₀
    · subst h5
      rw [h3a, Function.update_self]
    rw [Function.update_of_ne h5, h3 k h5]

/-- The child call proper with an empty `Tc`: `callPre`, the call `cp`, `callPostR`. -/
noncomputable def callCoreR (s : ℕ) (cp : Pr P (nT BReg) Q A U) : Pr P (nT BReg) Q A U :=
  .seq (callPre s) (.seq cp (callPostR s))

/-- The step bound of `callCoreR`: slot width `Lc`, pivot `s`, call bound `cc`. -/
def callCostR (Lc s cc : ℕ) : ℕ :=
  (1 + (2 * 0 + 2) + (4 * Lc + 4)) + cc +
    ((4 * Lc + 4) + ((4 * (s * Lc) + 4) + ((2 * (s * Lc) + 2) + 1)))

/-- **The child call proper with an empty `Tc`.** From the parameters of level `j + 1` with the
child's slot width `Lc` and row count `rowsAt R₀ j`, every register at rest (`Tc` empty) and `io`
the stream of `Z`, `callCoreR` leaves on `io` the stream of `Fo Z`; every other register ends as
it started. -/
theorem callCoreR_exec {bcRest : BReg → List (Fin (A + 4)) → Prop}
    {R₀ j u K ρ a₀ Lc n r w s cc : ℕ} (cp : Pr P (nT BReg) Q A U)
    (Fo : ZArr (Fin (rowsAt R₀ j) × Fin r) n → ZArr (Fin (rowsAt R₀ j) × Fin r) n)
    (hcall : CallSpecF body cp bcRest R₀ j u K ρ (a₀ + s * Lc) Lc n r w Fo cc)
    (Z : ZArr (Fin (rowsAt R₀ j) × Fin r) n) (v : HS (nT BReg) Q A U) (S : Stacks (nT BReg) A)
    (hL : ∀ y, S.L y = [])
    (hpar : ParState S.R (j + 1) u K ρ a₀ Lc (rowsAt R₀ j) n w (r * w))
    (hrest : RestBut bcRest n r w (· = .Tc) S.R)
    (hTc : S.R (reg .Tc) = []) (hio : S.R (reg .io) = encZ A w Z) :
    ∃ (v' : HS (nT BReg) Q A U) (c : ℕ), v'.user = v.user ∧ c ≤ callCostR Lc s cc ∧
      Exec body (callCoreR s cp) (mk v S) c (mk v' { S with
        R := Function.update S.R (reg .io) (encZ A w (Fo Z)) }) := by
  have hlev : (S.R (reg .lev)).length = j + 1 := hpar .lev
  obtain ⟨x₀, rest, hl⟩ : ∃ x₀ rest, S.R (reg .lev) = x₀ :: rest := by
    cases h : S.R (reg .lev) with
    | nil => rw [h] at hlev; simp at hlev
    | cons x rest => exact ⟨x, rest, rfl⟩
  have hrl : rest.length = j := by rw [hl] at hlev; simpa using hlev
  have hs : ∀ i, S.R (reg (.sc i)) = [] := fun i => hrest (.sc i) (by simp)
  have hLc : (S.R (reg .L)).length = Lc := hpar .L
  obtain ⟨v₁, hu₁, he₁⟩ := callPre_exec body s v S hl (hs 1)
  rw [hTc, List.reverse_nil, List.nil_append, List.length_nil] at he₁
  set Rp := Function.update (Function.update (Function.update (Function.update S.R
    (reg .lev) rest) (reg .park) (x₀ :: S.R (reg .park)))
    (reg .Tc) []) (reg .a₀) (List.replicate (s * (S.R (reg .L)).length) tick ++ S.R (reg .a₀))
    with hRp
  have hpf : ∀ k, k ≠ reg .lev → k ≠ reg .park → k ≠ reg .Tc → k ≠ reg .a₀ → Rp k = S.R k :=
    fun k h1 h2 h3 h4 => by
      rw [hRp, Function.update_of_ne h4, Function.update_of_ne h3, Function.update_of_ne h2,
        Function.update_of_ne h1]
  have hparC : ParState Rp j u K ρ (a₀ + s * Lc) Lc (rowsAt R₀ j) n w (r * w) := by
    intro x
    by_cases hx1 : x = .lev
    · subst hx1
      show (Rp (reg .lev)).length = j
      simp only [hRp]; fupd; exact hrl
    by_cases hx2 : x = .a₀
    · subst hx2
      show (Rp (reg .a₀)).length = a₀ + s * Lc
      simp only [hRp]; fupd
      rw [List.length_append, List.length_replicate, hLc, hpar .a₀]
      ring
    by_cases hx3 : x = .park
    · subst hx3; exact trivial
    by_cases hx4 : x = .Tc
    · subst hx4; exact trivial
    have h := hpar x
    rw [← hpf (reg x) (reg_ne hx1) (reg_ne hx3) (reg_ne hx4) (reg_ne hx2)] at h
    cases x <;> first | exact trivial | exact absurd rfl hx1 | exact absurd rfl hx2 | exact h
  have hrestC : Rest bcRest n r w Rp := by
    intro x
    by_cases hx1 : x = .lev
    · subst hx1; exact trivial
    by_cases hx2 : x = .a₀
    · subst hx2; exact trivial
    by_cases hx3 : x = .park
    · subst hx3; exact trivial
    by_cases hx4 : x = .Tc
    · subst hx4
      show Rp (reg .Tc) = []
      simp only [hRp]; fupd
    rw [hpf (reg x) (reg_ne hx1) (reg_ne hx3) (reg_ne hx4) (reg_ne hx2)]
    exact hrest x hx4
  obtain ⟨v₂, c₂, hu₂, hc₂, he₂⟩ := hcall Z v₁ { S with R := Rp } hL hparC hrestC
    (by dsimp only; rw [hpf _ (reg_ne (by simp)) (reg_ne (by simp)) (reg_ne (by simp))
      (reg_ne (by simp)), hio])
  set Y := encZ A w (Fo Z) with hY
  set Rc := Function.update Rp (reg .io) Y with hRc
  have hcf : ∀ k, k ≠ reg .io → k ≠ reg .lev → k ≠ reg .park → k ≠ reg .Tc → k ≠ reg .a₀ →
      Rc k = S.R k := fun k h0 h1 h2 h3 h4 => by
    rw [hRc, Function.update_of_ne h0, hpf k h1 h2 h3 h4]
  have hcfr : ∀ x : LReg BReg, x ≠ .io → x ≠ .lev → x ≠ .park → x ≠ .Tc → x ≠ .a₀ →
      Rc (reg x) = S.R (reg x) := fun x h0 h1 h2 h3 h4 =>
    hcf _ (reg_ne h0) (reg_ne h1) (reg_ne h2) (reg_ne h3) (reg_ne h4)
  obtain ⟨v₃, hu₃, he₃⟩ := callPostR_exec body s (x₀ := x₀) (a := S.R (reg .a₀))
    (p := S.R (reg .park)) v₂ { S with R := Rc }
    (by dsimp only
        rw [hcfr _ (by simp) (by simp) (by simp) (by simp) (by simp)]
        exact hrest .lenctr (by simp))
    (by dsimp only; rw [hcfr _ (by simp) (by simp) (by simp) (by simp) (by simp)]; exact hs 1)
    (by dsimp only; rw [hcfr .L (by simp) (by simp) (by simp) (by simp) (by simp)]
        simp only [hRc, hRp]; fupd)
    (by dsimp only; simp only [hRc, hRp]; fupd)
  refine ⟨v₃, _, by rw [hu₃, hu₂, hu₁], ?_, Exec.cast (Exec.seq he₁ (Exec.seq he₂ he₃)) rfl ?_⟩
  · dsimp only
    rw [hcfr .L (by simp) (by simp) (by simp) (by simp) (by simp), hLc]
    unfold callCostR
    omega
  · congr 2
    funext k
    dsimp only
    by_cases h1 : k = reg .lev
    · subst h1; simp only [hRc, hRp]; fupd; exact hl.symm
    by_cases h2 : k = reg .park
    · subst h2; simp only [hRc, hRp]; fupd
    by_cases h3 : k = reg .Tc
    · subst h3; simp only [hRc, hRp]; fupd; exact hTc.symm
    by_cases h4 : k = reg .a₀
    · subst h4; simp only [hRc, hRp]; fupd
    by_cases h0 : k = reg .io
    · subst h0; simp only [hRc, hRp]; fupd
    rw [Function.update_of_ne h1, Function.update_of_ne h2, Function.update_of_ne h4,
      Function.update_of_ne h0, hcf k h0 h1 h2 h3 h4]

/-- **The child call on wire `fw` with an empty `Tc`**: `childCall` with `callCoreR`. -/
noncomputable def childCallR (fw : NWire) (s : ℕ) (cp : Pr P (nT BReg) Q A U) :
    Pr P (nT BReg) Q A U :=
  .seq (parkW (otherW fw))
  (.seq (moveR (reg (.wire fw)) (reg (.wtmp fw)) id)
  (.seq (moveR (reg (.wtmp fw)) (reg .io) id)
  (.seq (callCoreR s cp)
  (.seq (ucopy (reg .io) (reg .lenctr) (reg (.sc 1)))
  (.seq (moveR (reg .io) (reg (.wtmp fw)) id)
  (.seq (moveR (reg (.wtmp fw)) (reg (.wire fw)) id)
  (.seq (unparkW (otherW fw).reverse)
    (uclear (reg .lenctr)))))))))

/-- The step bound of `childCallR` on wires of `N` symbols. -/
noncomputable def childCostR (N Lc s cc : ℕ) : ℕ :=
  (NW * (2 * N + 2) + 1) + (2 * N + 2) + (2 * N + 2) + callCostR Lc s cc + (4 * N + 4) +
    (2 * N + 2) + (2 * N + 2) + (NW * (4 * N + 5) + 1) + (2 * N + 2)

/-- **The child call on a wire with an empty `Tc`.** From the node-internal state at level
`j + 1` with the child's slot width `Lc` and row count, `Tc` empty and the wires holding the bank
`B`, `childCallR` replaces wire `fw` by `Fo (B fw)`; every other register ends as it started. -/
theorem childCallR_exec {bcRest : BReg → List (Fin (A + 4)) → Prop}
    {R₀ j u K ρ a₀ Lc n r w s cc : ℕ} (cp : Pr P (nT BReg) Q A U)
    (Fo : ZArr (Fin (rowsAt R₀ j) × Fin r) n → ZArr (Fin (rowsAt R₀ j) × Fin r) n)
    (hcall : CallSpecF body cp bcRest R₀ j u K ρ (a₀ + s * Lc) Lc n r w Fo cc) (fw : NWire)
    (B : NWire → ZArr (Fin (rowsAt R₀ j) × Fin r) n) (v : HS (nT BReg) Q A U)
    (S : Stacks (nT BReg) A) (hL : ∀ y, S.L y = [])
    (hpar : ParState S.R (j + 1) u K ρ a₀ Lc (rowsAt R₀ j) n w (r * w))
    (hrest : RestBut bcRest n r w (fun x => (∃ y, x = .wire y) ∨ x = .Tc) S.R)
    (hio : S.R (reg .io) = []) (hTc : S.R (reg .Tc) = [])
    (hB : ∀ x, S.R (reg (.wire x)) = encZ A w (B x)) :
    ∃ (v' : HS (nT BReg) Q A U) (c : ℕ), v'.user = v.user ∧
      c ≤ childCostR (rowsAt R₀ j * 2 ^ n * (r * w)) Lc s cc ∧
      Exec body (childCallR fw s cp) (mk v S) c (mk v' { S with
        R := Function.update S.R (reg (.wire fw)) (encZ A w (Fo (B fw))) }) := by
  set N := rowsAt R₀ j * 2 ^ n * (r * w) with hN
  set W : NWire → List (Fin (A + 4)) := fun x => encZ A w (B x) with hW
  have hWN : ∀ x, (W x).length = N := fun x => length_encZ _
  set Y := encZ A w (Fo (B fw)) with hY
  have hYN : Y.length = N := length_encZ _
  have hfwo : fw ∉ otherW fw := fun h => mem_otherW.1 h rfl
  have hwo : ∀ x, x ≠ fw → x ∈ otherW fw := fun x h => mem_otherW.2 h
  -- park the other wires
  obtain ⟨v₁, R₁, hu₁, he₁, hp₁, hw₁, ho₁⟩ := parkW_exec body W (otherW fw) (nodup_otherW fw) v S
    (fun x _ => hB x)
  have hf₁ : ∀ x : LReg BReg, x ≠ .park → (∀ y, x ≠ .wire y) → R₁ (reg x) = S.R (reg x) :=
    fun x h1 h2 => ho₁ _ (reg_ne h1) (fun y _ => reg_ne (h2 y))
  have h1fw : R₁ (reg (.wire fw)) = W fw := by
    rw [ho₁ _ (reg_ne (by simp)) (fun y hy => reg_ne (by
      simp only [ne_eq, LReg.wire.injEq]; rintro rfl; exact hfwo hy))]
    exact hB fw
  -- `fw` onto `io`
  obtain ⟨v₂, hu₂, he₂⟩ := moveR_exec body (reg (.wire fw)) (reg (.wtmp fw)) (reg_ne (by simp)) id
    v₁ { S with R := R₁ }
  set R₂ := movedR R₁ (reg (.wire fw)) (reg (.wtmp fw)) id (R₁ (reg (.wire fw))) with hR₂
  obtain ⟨v₃, hu₃, he₃⟩ := moveR_exec body (reg (.wtmp fw)) (reg .io) (reg_ne (by simp)) id
    v₂ { S with R := R₂ }
  set R₃ := movedR R₂ (reg (.wtmp fw)) (reg .io) id (R₂ (reg (.wtmp fw))) with hR₃
  have h2t : R₂ (reg (.wtmp fw)) = (W fw).reverse := by
    rw [hR₂, movedR, Function.update_self, h1fw, List.map_id, hf₁ _ (by simp) (by simp),
      hrest (.wtmp fw) (by simp), List.append_nil]
  have h3 : ∀ k, k ≠ reg .io → k ≠ reg (.wtmp fw) → k ≠ reg (.wire fw) → R₃ k = R₁ k :=
    fun k h1 h2 h3 => by
      rw [hR₃, movedR, Function.update_of_ne h1, Function.update_of_ne h2, hR₂, movedR,
        Function.update_of_ne h2, Function.update_of_ne h3]
  have h3io : R₃ (reg .io) = W fw := by
    rw [hR₃, movedR, Function.update_self, h2t, List.map_id, List.reverse_reverse, hR₂, movedR,
      Function.update_of_ne (reg_ne (by simp)), Function.update_of_ne (reg_ne (by simp)),
      hf₁ _ (by simp) (by simp), hio, List.append_nil]
  have h3fw : R₃ (reg (.wire fw)) = [] := by
    rw [hR₃, movedR, Function.update_of_ne (reg_ne (by simp)),
      Function.update_of_ne (reg_ne (by simp)),
      hR₂, movedR, Function.update_of_ne (reg_ne (by simp)), Function.update_self]
  have h3t : R₃ (reg (.wtmp fw)) = [] := by
    rw [hR₃, movedR, Function.update_of_ne (reg_ne (by simp)), Function.update_self]
  have h3w : ∀ x, R₃ (reg (.wire x)) = [] := by
    intro x
    by_cases hx : x = fw
    · subst hx; exact h3fw
    rw [h3 _ (reg_ne (by simp)) (reg_ne (by simp)) (reg_ne (by simp [hx])), hw₁ x (hwo x hx)]
  have hf₃ : ∀ x : LReg BReg, x ≠ .park → (∀ y, x ≠ .wire y) → x ≠ .io → x ≠ .wtmp fw →
      R₃ (reg x) = S.R (reg x) := fun x h1 h2 h3' h4 =>
    (h3 _ (reg_ne h3') (reg_ne h4) (reg_ne (h2 fw))).trans (hf₁ x h1 h2)
  -- the call
  obtain ⟨v₄, c₄, hu₄, hc₄, he₄⟩ := callCoreR_exec body cp Fo hcall (B fw) v₃
    { S with R := R₃ } hL
    (hpar.congr fun x hx => hf₃ x (by
        simp only [parRegs, List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp)
      (parRegs_ne hx).2.1 (parRegs_ne hx).1 (by
        simp only [parRegs, List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp))
    (fun x hx => by
      dsimp only
      by_cases hxw : ∃ y, x = .wire y
      · obtain ⟨y, rfl⟩ := hxw; rw [h3w]; rfl
      push Not at hxw
      by_cases hxp : x = .park
      · subst hxp; exact trivial
      by_cases hxi : x = .io
      · subst hxi; exact trivial
      by_cases hxt : x = .wtmp fw
      · subst hxt; rw [h3t]; rfl
      rw [hf₃ x hxp hxw hxi hxt]
      exact hrest x (by rintro (⟨y, hy⟩ | hy); exacts [hxw y hy, hx hy]))
    (by dsimp only; rw [hf₃ _ (by simp) (by simp) (by simp) (by simp)]; exact hTc)
    (by dsimp only; rw [h3io])
  set R₄ := Function.update R₃ (reg .io) Y with hR₄
  -- `io` back onto `fw`, with the length counter
  obtain ⟨v₅, hu₅, he₅⟩ := ucopy_exec body (a := reg .io) (b := reg .lenctr) (t := reg (.sc 1))
    (reg_ne (by simp)) (reg_ne (by simp)) (reg_ne (by simp)) v₄ { S with R := R₄ }
    (by dsimp only; rw [hR₄, Function.update_of_ne (reg_ne (by simp)),
      hf₃ _ (by simp) (by simp) (by simp) (by simp)]; exact hrest (.sc 1) (by simp))
  set R₅ := Function.update R₄ (reg .lenctr)
    (List.replicate (R₄ (reg .io)).length tick ++ R₄ (reg .lenctr)) with hR₅
  obtain ⟨v₆, hu₆, he₆⟩ := moveR_exec body (reg .io) (reg (.wtmp fw)) (reg_ne (by simp)) id
    v₅ { S with R := R₅ }
  set R₆ := movedR R₅ (reg .io) (reg (.wtmp fw)) id (R₅ (reg .io)) with hR₆
  obtain ⟨v₇, hu₇, he₇⟩ := moveR_exec body (reg (.wtmp fw)) (reg (.wire fw)) (reg_ne (by simp)) id
    v₆ { S with R := R₆ }
  set R₇ := movedR R₆ (reg (.wtmp fw)) (reg (.wire fw)) id (R₆ (reg (.wtmp fw))) with hR₇
  have h4io : R₄ (reg .io) = Y := by rw [hR₄, Function.update_self]
  have h5io : R₅ (reg .io) = Y := by rw [hR₅, Function.update_of_ne (reg_ne (by simp)), h4io]
  have h5l : R₅ (reg .lenctr) = List.replicate N tick := by
    rw [hR₅, Function.update_self, h4io, hYN, hR₄, Function.update_of_ne (reg_ne (by simp)),
      hf₃ _ (by simp) (by simp) (by simp) (by simp), hrest .lenctr (by simp), List.append_nil]
  have h5 : ∀ k, k ≠ reg .io → k ≠ reg .lenctr → R₅ k = R₃ k := fun k h1 h2 => by
    rw [hR₅, Function.update_of_ne h2, hR₄, Function.update_of_ne h1]
  have h6t : R₆ (reg (.wtmp fw)) = Y.reverse := by
    rw [hR₆, movedR, Function.update_self, h5io, List.map_id,
      h5 _ (reg_ne (by simp)) (reg_ne (by simp)), h3t, List.append_nil]
  have h7 : ∀ k, k ≠ reg .io → k ≠ reg (.wtmp fw) → k ≠ reg (.wire fw) → k ≠ reg .lenctr →
      R₇ k = R₃ k := fun k h1 h2 h3' h4 => by
    rw [hR₇, movedR, Function.update_of_ne h3', Function.update_of_ne h2, hR₆, movedR,
      Function.update_of_ne h2, Function.update_of_ne h1, h5 k h1 h4]
  have h7fw : R₇ (reg (.wire fw)) = Y := by
    rw [hR₇, movedR, Function.update_self, h6t, List.map_id, List.reverse_reverse, hR₆, movedR,
      Function.update_of_ne (reg_ne (by simp)), Function.update_of_ne (reg_ne (by simp)),
      h5 _ (reg_ne (by simp)) (reg_ne (by simp)), h3fw, List.append_nil]
  have h7io : R₇ (reg .io) = [] := by
    rw [hR₇, movedR, Function.update_of_ne (reg_ne (by simp)),
      Function.update_of_ne (reg_ne (by simp)),
      hR₆, movedR, Function.update_of_ne (reg_ne (by simp)), Function.update_self]
  have h7t : R₇ (reg (.wtmp fw)) = [] := by
    rw [hR₇, movedR, Function.update_of_ne (reg_ne (by simp)), Function.update_self]
  have h7l : R₇ (reg .lenctr) = List.replicate N tick := by
    rw [hR₇, movedR, Function.update_of_ne (reg_ne (by simp)),
      Function.update_of_ne (reg_ne (by simp)), hR₆, movedR,
      Function.update_of_ne (reg_ne (by simp)), Function.update_of_ne (reg_ne (by simp)), h5l]
  -- unpark
  obtain ⟨v₈, R₈, hu₈, he₈, hp₈, hw₈, ho₈⟩ := unparkW_exec body W N hWN (otherW fw).reverse
    (List.nodup_reverse.2 (nodup_otherW fw)) v₇ { S with R := R₇ } (S.R (reg .park))
    (by dsimp only; rw [h7l, List.length_replicate])
    (by dsimp only; rw [h7 _ (reg_ne (by simp)) (reg_ne (by simp)) (reg_ne (by simp))
      (reg_ne (by simp)), hf₃ _ (by simp) (by simp) (by simp) (by simp)]
        exact hrest (.sc 1) (by simp))
    (by dsimp only; rw [h7 _ (reg_ne (by simp)) (reg_ne (by simp)) (reg_ne (by simp))
      (reg_ne (by simp)), h3 _ (reg_ne (by simp)) (reg_ne (by simp)) (reg_ne (by simp)), hp₁])
    (fun x hx => by
      have hx' : x ≠ fw := mem_otherW.1 (List.mem_reverse.1 hx)
      dsimp only
      rw [h7 _ (reg_ne (by simp)) (reg_ne (by simp)) (reg_ne (by simp [hx'])) (reg_ne (by simp)),
        h3w])
  obtain ⟨v₉, hu₉, he₉⟩ := uclear_exec body (reg .lenctr) v₈ { S with R := R₈ }
  have ho₈' : ∀ k, k ≠ reg .park → (∀ x ∈ (otherW fw).reverse, k ≠ reg (.wire x)) →
      R₈ k = R₇ k := ho₈
  have hlen8 : (R₈ (reg .lenctr)).length = N := by
    rw [ho₈' _ (reg_ne (by simp)) (fun x _ => reg_ne (by simp)), h7l, List.length_replicate]
  refine ⟨v₉, _, by rw [hu₉, hu₈, hu₇, hu₆, hu₅, hu₄, hu₃, hu₂, hu₁], ?_,
    Exec.cast (Exec.seq he₁ (Exec.seq he₂ (Exec.seq he₃ (Exec.seq he₄ (Exec.seq he₅
      (Exec.seq he₆ (Exec.seq he₇ (Exec.seq he₈ he₉)))))))) rfl ?_⟩
  · have hsum : ((otherW fw).map fun x => 2 * (W x).length + 2).sum ≤ NW * (2 * N + 2) := by
      rw [List.map_congr_left (g := fun _ => 2 * N + 2) (fun x _ => by rw [hWN])]
      simp only [List.map_const', List.sum_replicate, smul_eq_mul]
      exact Nat.mul_le_mul_right _ (length_otherW_le fw)
    have hlo : (otherW fw).reverse.length * (4 * N + 5) ≤ NW * (4 * N + 5) := by
      rw [List.length_reverse]; exact Nat.mul_le_mul_right _ (length_otherW_le fw)
    dsimp only
    rw [h1fw, hWN, h2t, List.length_reverse, hWN, h4io, hYN, h5io, hYN, h6t, List.length_reverse,
      hYN, hlen8]
    unfold childCostR
    omega
  · congr 2
    funext k
    dsimp only
    by_cases hl : k = reg .lenctr
    · subst hl; rw [Function.update_self, Function.update_of_ne (reg_ne (by simp)),
        hrest .lenctr (by simp)]
    rw [Function.update_of_ne hl]
    by_cases hp : k = reg .park
    · subst hp; rw [hp₈, Function.update_of_ne (reg_ne (by simp))]
    by_cases hwk : ∃ x, k = reg (.wire x)
    · obtain ⟨x, rfl⟩ := hwk
      by_cases hx : x = fw
      · subst hx
        rw [ho₈' _ hp (fun y hy => reg_ne (by
          simp only [ne_eq, LReg.wire.injEq]; rintro rfl; exact hfwo (List.mem_reverse.1 hy))),
          h7fw, Function.update_self]
      · rw [hw₈ x (List.mem_reverse.2 (hwo x hx)), Function.update_of_ne (reg_ne (by simp [hx]))]
        exact (hB x).symm
    push Not at hwk
    rw [ho₈' k hp (fun x _ => hwk x), Function.update_of_ne (hwk fw)]
    by_cases hi : k = reg .io
    · subst hi; rw [h7io, hio]
    by_cases ht : k = reg (.wtmp fw)
    · subst ht; rw [h7t, hrest (.wtmp fw) (by simp)]
    rw [h7 k hi ht (hwk fw) hl]
    obtain ⟨x, rfl⟩ := (regEquiv BReg).surjective k
    exact hf₃ x (fun h => hp (by rw [h]; rfl)) (fun y h => hwk y (by rw [h]; rfl))
      (fun h => hi (by rw [h]; rfl)) (fun h => ht (by rw [h]; rfl))


end CallR

end IntegerMultBounds.MathlibTM2.LayerMachine
