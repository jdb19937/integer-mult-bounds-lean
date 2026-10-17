module

public import IntegerMultBounds.MathlibTM2.Fast.PrepB
public import IntegerMultBounds.MathlibTM2.Fast.LoadChirp
public import IntegerMultBounds.MathlibTM2.Fast.ConvBox
public import IntegerMultBounds.MathlibTM2.Fast.LoadRing
public import IntegerMultBounds.MathlibTM2.Fast.CRTMachine

/-!
# The register file of the source transform

The source transform `F'` (`Mult/Pipeline.srcMap`) and its opposite (`oppMap`) run the closed
stage machines one after the other on one register file. This file fixes that register file,
lifts the stage contracts to it, and proves the stream identities between the stage formats.

**Registers** (`SrcR t₀`, layout `rg : SrcR t₀ → Fin T`, injective and disjoint from the 64
Schönhage–Strassen registers `ι`). One family per stage, each with the register type of its
stage theorem:
* `a r` (`r : RsaR (RsaX t₀)`): `Ã` (`Fast/PrepA.rsaStage_exec`), box register `a .ln`;
* `b r` (`r : RsbR ⊕ RsbX t₀`): `B̃₀` (`Fast/BandStage.bandStage_exec`), box register `b (.inl .src)`;
* `k r` (`r : CsR ldcX`): the chirp kernel (`Fast/LoadChirp.ldChirpStage_exec`), kernel on
  `k .kr`;
* `v r` (`r : CvR`): the complex convolution (`Fast/ConvBox.cvBox_convBox`); its complex-product
  registers `v (.cm x)` also run the second chirp product;
* `c r` (`r : CrtReg`) and `cb j` (`j : Fin (swapT 6)`): the CRT layout machines
  (`Fast/CRTMachine`), with their interchange bank on `cb`;
* `m x` (`x : CR`): the complex-product registers of the first chirp product (shift `p + 1`);
* `x j` (`j : SrcX`): the transfer registers: the result `sb`, the spare `tr`, the copy spares
  `cA`, `cB`, `c1`, `c2`, the registers `gS`, `gR`, `gT`, `gU`, `gD` of the scale by `2^γ`, the
  unary `ℓ` of the ring header `lU`, and the stored chirp descriptions `tSp`, `sSp`.

A register file is a record `SrcF` of one function per family; `SrcF.get` is the file as a
function on `SrcR t₀`, and `SrcF.upd_*`, `SrcF.ext_*` turn register updates and lifted stage
results into record updates.

**Contracts.** `SrcRuns body rg ι Pre p ρ ρ' b` is `ResampA.RsaRuns` from stacks meeting `Pre`
(the transforms' precondition of `Fast/ConvSpec`); `SrcFramed rg Pre`: `Pre` survives every
change confined to the layout. Framing: `src_lift` lifts a contract of a family layout
`rg ∘ f` (`f` injective) to the composite, the other registers unchanged
(`Function.extend f ρ' ρ`); `SrcRuns.lift` does the same with `Pre`; `src_of_crt` turns the
whole-file contracts of the CRT machines (`crtRuns`) into composite contracts.
`src_mv_runs`: a stream moved in forward order through an empty spare (`srcMv`).

**Formats.** `src_rsbBox_eq`: `rsbBox = rsaBox`. `src_crtBox_rsaBox`: the CRT box along
`List.finRange d` with widths `a j` is the padded box stream `rsaBox d t` for `t j = 2^{a j}`
(axis `0` most significant in both). The chirp, convolution and resampling stages all read
`rsaBox` streams of coefficients (`cstNumBox q t f = rsaBox d t (numer q ∘ f ∘ cast)`), so no
data moves between stages.
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Fast.Src

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.ResampA IntegerMultBounds.MathlibTM2.Fast.ChirpSt IntegerMultBounds.MathlibTM2.Fast.ConvSt


/-! ### Registers -/

noncomputable section

/-- The transfer registers of the composite. -/
inductive SrcX where
  | sb | tr | cA | cB | c1 | c2 | gS | gR | gT | gU | gD | lU | tSp | sSp
  deriving DecidableEq

/-- The registers of the source transform: one family per stage and the transfer registers. -/
inductive SrcR (t₀ : ℕ) where
  | a (r : RsaR (RsaX t₀))
  | b (r : RsbR ⊕ RsbX t₀)
  | k (r : CsR ChirpSt.ldcX)
  | v (r : CvR)
  | c (r : CrtReg)
  | cb (j : Fin (swapT 6))
  | m (x : CR)
  | x (j : SrcX)
  deriving DecidableEq

end

section Inj

variable {t₀ : ℕ}

lemma SrcR.a_inj : Function.Injective (SrcR.a : RsaR (RsaX t₀) → SrcR t₀) :=
  fun _ _ h => SrcR.a.inj h
lemma SrcR.b_inj : Function.Injective (SrcR.b : RsbR ⊕ RsbX t₀ → SrcR t₀) :=
  fun _ _ h => SrcR.b.inj h
lemma SrcR.k_inj : Function.Injective (SrcR.k : CsR ChirpSt.ldcX → SrcR t₀) :=
  fun _ _ h => SrcR.k.inj h
lemma SrcR.v_inj : Function.Injective (SrcR.v : CvR → SrcR t₀) :=
  fun _ _ h => SrcR.v.inj h
lemma SrcR.c_inj : Function.Injective (SrcR.c : CrtReg → SrcR t₀) :=
  fun _ _ h => SrcR.c.inj h
lemma SrcR.cb_inj : Function.Injective (SrcR.cb : Fin (swapT 6) → SrcR t₀) :=
  fun _ _ h => SrcR.cb.inj h
lemma SrcR.m_inj : Function.Injective (SrcR.m : CR → SrcR t₀) :=
  fun _ _ h => SrcR.m.inj h
lemma SrcR.vcm_inj : Function.Injective (fun x : CR => (SrcR.v (CvR.cm x) : SrcR t₀)) :=
  fun _ _ h => CvR.cm.inj (SrcR.v.inj h)

end Inj

/-! ### Register files -/

/-- A register file of the composite, one function per family. -/
@[ext]
structure SrcF (t₀ A : ℕ) where
  a : RsaR (RsaX t₀) → List (Fin (A + 4))
  b : RsbR ⊕ RsbX t₀ → List (Fin (A + 4))
  k : CsR ChirpSt.ldcX → List (Fin (A + 4))
  v : CvR → List (Fin (A + 4))
  c : CrtReg → List (Fin (A + 4))
  cb : Fin (swapT 6) → List (Fin (A + 4))
  m : CR → List (Fin (A + 4))
  x : SrcX → List (Fin (A + 4))

section Files

variable {t₀ A : ℕ}

/-- The register file as a function. -/
def SrcF.get (F : SrcF t₀ A) : SrcR t₀ → List (Fin (A + 4))
  | .a r => F.a r
  | .b r => F.b r
  | .k r => F.k r
  | .v r => F.v r
  | .c r => F.c r
  | .cb j => F.cb j
  | .m x => F.m x
  | .x j => F.x j

@[simp] lemma SrcF.get_a (F : SrcF t₀ A) (r : RsaR (RsaX t₀)) : F.get (.a r) = F.a r := rfl
@[simp] lemma SrcF.get_b (F : SrcF t₀ A) (r : RsbR ⊕ RsbX t₀) : F.get (.b r) = F.b r := rfl
@[simp] lemma SrcF.get_k (F : SrcF t₀ A) (r : CsR ChirpSt.ldcX) : F.get (.k r) = F.k r := rfl
@[simp] lemma SrcF.get_v (F : SrcF t₀ A) (r : CvR) : F.get (.v r) = F.v r := rfl
@[simp] lemma SrcF.get_c (F : SrcF t₀ A) (r : CrtReg) : F.get (.c r) = F.c r := rfl
@[simp] lemma SrcF.get_cb (F : SrcF t₀ A) (j : Fin (swapT 6)) : F.get (.cb j) = F.cb j := rfl
@[simp] lemma SrcF.get_m (F : SrcF t₀ A) (x : CR) : F.get (.m x) = F.m x := rfl
@[simp] lemma SrcF.get_x (F : SrcF t₀ A) (j : SrcX) : F.get (.x j) = F.x j := rfl

lemma SrcF.upd_a (F : SrcF t₀ A) (r : RsaR (RsaX t₀)) (l : List (Fin (A + 4))) :
    Function.update F.get (.a r) l = { F with a := Function.update F.a r l }.get := by
  funext y; cases y <;> simp [SrcF.get, Function.update_apply]

lemma SrcF.upd_b (F : SrcF t₀ A) (r : RsbR ⊕ RsbX t₀) (l : List (Fin (A + 4))) :
    Function.update F.get (.b r) l = { F with b := Function.update F.b r l }.get := by
  funext y; cases y <;> simp [SrcF.get, Function.update_apply]

lemma SrcF.upd_k (F : SrcF t₀ A) (r : CsR ChirpSt.ldcX) (l : List (Fin (A + 4))) :
    Function.update F.get (.k r) l = { F with k := Function.update F.k r l }.get := by
  funext y; cases y <;> simp [SrcF.get, Function.update_apply]

lemma SrcF.upd_v (F : SrcF t₀ A) (r : CvR) (l : List (Fin (A + 4))) :
    Function.update F.get (.v r) l = { F with v := Function.update F.v r l }.get := by
  funext y; cases y <;> simp [SrcF.get, Function.update_apply]

lemma SrcF.upd_c (F : SrcF t₀ A) (r : CrtReg) (l : List (Fin (A + 4))) :
    Function.update F.get (.c r) l = { F with c := Function.update F.c r l }.get := by
  funext y; cases y <;> simp [SrcF.get, Function.update_apply]

lemma SrcF.upd_m (F : SrcF t₀ A) (r : CR) (l : List (Fin (A + 4))) :
    Function.update F.get (.m r) l = { F with m := Function.update F.m r l }.get := by
  funext y; cases y <;> simp [SrcF.get, Function.update_apply]

lemma SrcF.upd_x (F : SrcF t₀ A) (r : SrcX) (l : List (Fin (A + 4))) :
    Function.update F.get (.x r) l = { F with x := Function.update F.x r l }.get := by
  funext y; cases y <;> simp [SrcF.get, Function.update_apply]

lemma SrcF.ext_a (F : SrcF t₀ A) (ρ : RsaR (RsaX t₀) → List (Fin (A + 4))) :
    Function.extend SrcR.a ρ F.get = { F with a := ρ }.get := by
  funext y
  cases y with
  | a r => exact SrcR.a_inj.extend_apply _ _ r
  | _ => exact Function.extend_apply' _ _ _ (by rintro ⟨r, hr⟩; cases hr)

lemma SrcF.ext_b (F : SrcF t₀ A) (ρ : RsbR ⊕ RsbX t₀ → List (Fin (A + 4))) :
    Function.extend SrcR.b ρ F.get = { F with b := ρ }.get := by
  funext y
  cases y with
  | b r => exact SrcR.b_inj.extend_apply _ _ r
  | _ => exact Function.extend_apply' _ _ _ (by rintro ⟨r, hr⟩; cases hr)

lemma SrcF.ext_k (F : SrcF t₀ A) (ρ : CsR ChirpSt.ldcX → List (Fin (A + 4))) :
    Function.extend SrcR.k ρ F.get = { F with k := ρ }.get := by
  funext y
  cases y with
  | k r => exact SrcR.k_inj.extend_apply _ _ r
  | _ => exact Function.extend_apply' _ _ _ (by rintro ⟨r, hr⟩; cases hr)

lemma SrcF.ext_v (F : SrcF t₀ A) (ρ : CvR → List (Fin (A + 4))) :
    Function.extend SrcR.v ρ F.get = { F with v := ρ }.get := by
  funext y
  cases y with
  | v r => exact SrcR.v_inj.extend_apply _ _ r
  | _ => exact Function.extend_apply' _ _ _ (by rintro ⟨r, hr⟩; cases hr)

end Files

/-! ### Contracts -/

section Contracts

variable {T Q A : ℕ} {U P R : Type} [DecidableEq R] (body : P → Pr P T Q A U) (rg : R → Fin T)
  (ι : Fin 64 → Fin T) (Pre : Stacks T A → Prop)

/-- `Pre` survives every change confined to the layout. -/
def SrcFramed : Prop := ∀ S S' : Stacks T A, Pre S → rsaFr rg S S' → Pre S'

/-- `ResampA.RsaRuns` from stacks meeting `Pre`. -/
def SrcRuns (p : Pr P T Q A U) (ρ ρ' : R → List (Fin (A + 4))) (b : ℕ) : Prop :=
  ∀ v S, rsaClean ι S → Pre S → rsaHolds rg S ρ → ∃ v' S' n, v'.user = v.user ∧ n ≤ b ∧
    Exec body p (mk v S) n (mk v' S') ∧ rsaHolds rg S' ρ' ∧ rsaFr rg S S'

variable {body rg ι Pre}

omit [DecidableEq R] in
theorem SrcRuns.of_rsa {p : Pr P T Q A U} {ρ ρ' : R → List (Fin (A + 4))} {b : ℕ}
    (h : RsaRuns body rg ι p ρ ρ' b) : SrcRuns body rg ι Pre p ρ ρ' b :=
  fun v S hc _ hS => h v S hc hS

omit [DecidableEq R] in
theorem SrcRuns.seq (hdisj : ∀ r j, rg r ≠ ι j) (hP : SrcFramed rg Pre) {p q : Pr P T Q A U}
    {ρ₁ ρ₂ ρ₃ : R → List (Fin (A + 4))} {b₁ b₂ : ℕ} (h₁ : SrcRuns body rg ι Pre p ρ₁ ρ₂ b₁)
    (h₂ : SrcRuns body rg ι Pre q ρ₂ ρ₃ b₂) : SrcRuns body rg ι Pre (.seq p q) ρ₁ ρ₃ (b₁ + b₂) := by
  intro v S hc hpre hS
  obtain ⟨v₁, S₁, n₁, hu₁, hn₁, he₁, hS₁, hf₁⟩ := h₁ v S hc hpre hS
  obtain ⟨v₂, S₂, n₂, hu₂, hn₂, he₂, hS₂, hf₂⟩ :=
    h₂ v₁ S₁ (hc.of_fr hdisj hf₁) (hP S S₁ hpre hf₁) hS₁
  exact ⟨v₂, S₂, n₁ + n₂, hu₂.trans hu₁, by omega, Exec.seq he₁ he₂, hS₂, hf₁.trans hf₂⟩

omit [DecidableEq R] in
theorem SrcRuns.mono {p : Pr P T Q A U} {ρ ρ' : R → List (Fin (A + 4))} {b b' : ℕ}
    (h : SrcRuns body rg ι Pre p ρ ρ' b) (hb : b ≤ b') : SrcRuns body rg ι Pre p ρ ρ' b' := by
  intro v S hc hpre hS
  obtain ⟨v', S', n, hu, hn, he, hS', hf⟩ := h v S hc hpre hS
  exact ⟨v', S', n, hu, hn.trans hb, he, hS', hf⟩

omit [DecidableEq R] in
theorem SrcRuns.congr {p : Pr P T Q A U} {ρ ρ' ρ'' : R → List (Fin (A + 4))} {b : ℕ}
    (h : SrcRuns body rg ι Pre p ρ ρ' b) (he : ρ' = ρ'') : SrcRuns body rg ι Pre p ρ ρ'' b :=
  he ▸ h

omit [DecidableEq R] in
theorem SrcRuns.congr_pre {p : Pr P T Q A U} {ρ₀ ρ ρ' : R → List (Fin (A + 4))} {b : ℕ}
    (h : SrcRuns body rg ι Pre p ρ ρ' b) (he : ρ₀ = ρ) : SrcRuns body rg ι Pre p ρ₀ ρ' b :=
  he ▸ h

omit [DecidableEq R] in
/-- A framed `Pre` is framed for every sub-layout. -/
theorem SrcFramed.comp {R' : Type} {f : R' → R} (hP : SrcFramed rg Pre) :
    SrcFramed (fun x => rg (f x)) Pre := fun S S' hS h =>
  hP S S' hS ⟨h.1, h.2.1, h.2.2.1, fun k hk => h.2.2.2 k (fun x => hk (f x))⟩

variable (hrg : Function.Injective rg)
include hrg

omit [DecidableEq R] in
/-- **Framing.** A contract of the family layout `rg ∘ f` lifts to the composite: the family's
registers change as in the contract, every other register is kept. -/
theorem src_lift {R' : Type} {f : R' → R} (hf : Function.Injective f) {p : Pr P T Q A U}
    {ρs ρs' : R' → List (Fin (A + 4))} {b : ℕ} (h : RsaRuns body (fun x => rg (f x)) ι p ρs ρs' b)
    (ρ : R → List (Fin (A + 4))) (hρ : ∀ x, ρ (f x) = ρs x) :
    RsaRuns body rg ι p ρ (Function.extend f ρs' ρ) b := by
  intro v S hcl hS
  obtain ⟨v', S', n, hu, hn, he, hS', hf'⟩ := h v S hcl (fun x => by rw [hS, hρ])
  refine ⟨v', S', n, hu, hn, he, fun r => ?_, hf'.1, hf'.2.1, hf'.2.2.1, fun k hk =>
    hf'.2.2.2 k (fun x => hk (f x))⟩
  by_cases hr : ∃ x, f x = r
  · obtain ⟨x, rfl⟩ := hr
    rw [hf.extend_apply, hS' x]
  · rw [Function.extend_apply' _ _ _ hr]
    rw [hf'.2.2.2 (rg r) (fun x hx => hr ⟨x, hrg hx⟩), hS]

omit [DecidableEq R] in
/-- **Framing with `Pre`.** -/
theorem SrcRuns.lift {R' : Type} {f : R' → R} (hf : Function.Injective f) {p : Pr P T Q A U}
    {ρs ρs' : R' → List (Fin (A + 4))} {b : ℕ}
    (h : SrcRuns body (fun x => rg (f x)) ι Pre p ρs ρs' b)
    (ρ : R → List (Fin (A + 4))) (hρ : ∀ x, ρ (f x) = ρs x) :
    SrcRuns body rg ι Pre p ρ (Function.extend f ρs' ρ) b := by
  intro v S hcl hpre hS
  obtain ⟨v', S', n, hu, hn, he, hS', hf'⟩ := h v S hcl hpre (fun x => by rw [hS, hρ])
  refine ⟨v', S', n, hu, hn, he, fun r => ?_, hf'.1, hf'.2.1, hf'.2.2.1, fun k hk =>
    hf'.2.2.2 k (fun x => hk (f x))⟩
  by_cases hr : ∃ x, f x = r
  · obtain ⟨x, rfl⟩ := hr
    rw [hf.extend_apply, hS' x]
  · rw [Function.extend_apply' _ _ _ hr]
    rw [hf'.2.2.2 (rg r) (fun x hx => hr ⟨x, hrg hx⟩), hS]

/-- A whole-file contract (`crtRuns`) whose final file changes one layout register. -/
theorem src_of_crt {p : Pr P T Q A U} {ρ : R → List (Fin (A + 4))} {x : R}
    {l : List (Fin (A + 4))} {b : ℕ}
    (h : ∀ S : Stacks T A, rsaClean ι S → rsaHolds rg S ρ →
      crtRuns body p S.R (Function.update S.R (rg x) l) b) :
    RsaRuns body rg ι p ρ (Function.update ρ x l) b := by
  intro v S hc hS
  obtain ⟨v', m, hu, hm, he⟩ := h S hc hS v S rfl hc.1
  exact ⟨v', _, m, hu, hm, he, rsa_holds_upd hrg hS x l, rfl, rfl, rfl,
    fun k hk => rsa_upd_off _ _ _ hk⟩

variable (rg) in
/-- Move a stream in forward order from `a` onto `b` through the empty spare `sp`. -/
def srcMv (a b sp : R) : Pr P T Q A U :=
  .seq (moveR (rg a) (rg sp) id) (moveR (rg sp) (rg b) id)

variable (hdisj : ∀ r j, rg r ≠ ι j)
include hdisj

/-- **A forward transfer.** `b` gains the stream of `a` on top, `a` ends empty. -/
theorem src_mv_runs {a b sp : R} (hab : a ≠ b) (ha : a ≠ sp) (hb : b ≠ sp)
    (ρ : R → List (Fin (A + 4))) (ht : ρ sp = []) :
    RsaRuns body rg ι (srcMv rg a b sp) ρ
      (Function.update (Function.update ρ a []) b (ρ a ++ ρ b)) (4 * (ρ a).length + 4) := by
  have h1 := rsa_moveR (body := body) (ι := ι) hrg ha ρ
  have h2 := rsa_moveR (body := body) (ι := ι) hrg (Ne.symm hb)
    (Function.update (Function.update ρ a []) sp ((ρ a).reverse ++ ρ sp))
  refine ((RsaRuns.seq hdisj h1 h2).congr ?_).mono ?_
  · funext k
    simp only [Function.update_apply, ht, List.append_nil]
    split_ifs <;> subst_vars <;> simp_all
  · simp only [Function.update_self, ht, List.append_nil, List.length_reverse]
    omega

end Contracts

/-! ### Stream identities -/

section Streams

/-- The box streams of the two resampling stages agree. -/
theorem src_rsbBox_eq {α : Type} : ∀ (d : ℕ) (t : Fin d → ℕ) (F : ((i : Fin d) → Fin (t i)) → α),
    rsbBox d t F = rsaBox d t F
  | 0, _, _ => rfl
  | d + 1, t, F => by
      simp only [rsbBox, rsaBox]
      congr 1
      funext x₀
      exact src_rsbBox_eq d _ _

/-- Decoding along a layout of the axes `1, …, d` of a `(d + 1)`-axis box. -/
theorem src_crtDec_succ {d : ℕ} (a : Fin (d + 1) → ℕ) :
    ∀ (o : List (Fin d)) (n : ℕ) (x : Fin (d + 1) → ℕ),
      crtDec a (o.map Fin.succ) n x =
        Fin.cons (x 0) (crtDec (fun i => a i.succ) o n (Fin.tail x))
  | [], n, x => by simp [crtDec]
  | j :: o, n, x => by
      have hw : crtW a (o.map Fin.succ) = crtW (fun i => a i.succ) o := by
        simp [crtW, List.map_map, Function.comp_def]
      rw [List.map_cons, crtDec_cons, crtDec_cons, src_crtDec_succ a o, hw]
      congr 1
      simp [Fin.tail_update_succ]

theorem src_crtBox_succ {α : Type} {d : ℕ} (a : Fin (d + 1) → ℕ) (o : List (Fin d))
    (C : (Fin (d + 1) → ℕ) → α) (x : Fin (d + 1) → ℕ) :
    crtBox a (o.map Fin.succ) C x =
      crtBox (fun i => a i.succ) o (fun y => C (Fin.cons (x 0) y)) (Fin.tail x) := by
  have hw : crtW a (o.map Fin.succ) = crtW (fun i => a i.succ) o := by
    simp [crtW, List.map_map, Function.comp_def]
  unfold crtBox
  rw [hw]
  exact List.map_congr_left fun n _ => by rw [src_crtDec_succ]

/-- **The CRT box is the padded box stream.** Along `List.finRange d` with widths `a j` and
`t j = 2^{a j}`, the box of content `C` lists `C` at the addresses of `∏ [0, t j)` in the order
of `rsaBox` (axis `0` most significant). -/
theorem src_crtBox_rsaBox {α : Type} : ∀ (d : ℕ) (a t : Fin d → ℕ), (∀ j, t j = 2 ^ a j) →
    ∀ (C : (Fin d → ℕ) → α) (x : Fin d → ℕ),
      crtBox a (List.finRange d) C x = rsaBox d t (fun y => C (fun j => (y j : ℕ)))
  | 0, a, t, _, C, x => by
      simp only [List.finRange_zero, crtBox_nil, rsaBox]
      congr 2
      funext j; exact j.elim0
  | d + 1, a, t, ht, C, x => by
      rw [List.finRange_succ, crtBox_cons, rsaBox]
      have hl : (List.finRange (t 0)).flatMap (fun x₀ => rsaBox d (fun i => t i.succ)
          (fun y => C (fun j => ((Fin.cons x₀ y : (i : Fin (d + 1)) → Fin (t i)) j : ℕ)))) =
          (List.range (t 0)).flatMap (fun y₀ => rsaBox d (fun i => t i.succ)
            (fun y => C (Fin.cons y₀ fun j => (y j : ℕ)))) := by
        rw [← List.map_coe_finRange_eq_range, List.flatMap_map]
        refine List.flatMap_congr fun x₀ _ => ?_
        congr 1
        funext y
        congr 1
        funext j
        refine Fin.cases ?_ (fun i => ?_) j <;> simp
      rw [hl, ht 0]
      refine List.flatMap_congr fun y₀ _ => ?_
      rw [src_crtBox_succ, src_crtBox_rsaBox d (fun i => a i.succ) (fun i => t i.succ)
        (fun i => ht i.succ)]
      simp

end Streams

end IntegerMultBounds.MathlibTM2.Fast.Src
