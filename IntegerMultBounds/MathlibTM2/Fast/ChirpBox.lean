module

public import IntegerMultBounds.MathlibTM2.Fast.ResampABox
public import IntegerMultBounds.MathlibTM2.Mult.Chirp
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein
public import IntegerMultBounds.MathlibTM2.Fast.CMul
public import IntegerMultBounds.MathlibTM2.Mult.CRT

/-!
# Numerator boxes and the chirp kernel on numerators

Arithmetic of the entrywise stages of the pipeline (`Fast/ChirpStage`, `Fast/PointStage`).

**Grid values.** A grid value at scale `2^q` is `cstGrid q N = N / 2^q` for a numerator
`N : GaussianInt`; `numer q` recovers `N` (`cst_numer_grid`) and returns the numerator of every
`q`-bit fixed-point number (`cst_grid_numer`). On numerators:

* `cst_rhoC_grid_mul`: `Q_q (N₁/2^q · N₂/2^q) = tdivN q (N₁ N₂) / 2^q`;
* `cst_rhoC_grid_shift`: `Q_p (X / 2^(p+s)) = tdivN s X / 2^p`;
* `cst_diskPhase_grid`: `diskPhase p (M / 2^(p+g)) = tdivN (p+g+2) (M · cstDiskC p) / 2^p` with the
  real constant `cstDiskC p = 2^(p+2) - 1`;
* `cst_numer_conj`: `numer q (conj z) = star (numer q z)` for every `z`;
* `cst_numer_two_pow_mul`: `numer q (2^γ z) = 2^γ numer q z` on the grid.

**Boxes.** A box array on `∏_{i<d} [0, t_i)` is stored in address order, axis `0` most
significant: `ResampA.rsaBox d t F`. `cstAddrs ns` lists the addresses of `∏ [0, n_i)` in this
order as lists of naturals; `cst_rsaBox_eq_addrs` identifies `rsaBox d t F` with
`(cstAddrs (List.ofFn t)).map H` when `F x = H [x_0, …, x_{d-1}]`, and `cstAddrs_append` adds a
least significant axis. `cstNumBox q t f` is the box of the numerators at scale `2^q` of a
function `f` on `∏ ZMod (t i)`, entry `x` at the address `(x_i : ZMod (t i))`, the convention of
`ResampA.rsa_tensor`. `cst_zipWith_rsaBox`: two boxes entrywise; `cst_mem_rsaBox`: every entry
is a value of `F`.

**Register files.** `cst_extend_update` reads off the final register file of
`ResampA.RsaRuns.of_c` for a complex-product contract that updates one register;
`cst_ready_of_eq` transfers `Ready` across register files that agree off the operand, save,
result and output registers; the tactic `cst_upd` closes equations between register files
built from `Function.update`.

**The chirp kernel.** `cstTP q Ns` is the truncated product of numerators, left to right with
`tdivN q` after each multiplication (`cst_truncProd_grid`: it is the numerator of
`Chirp.truncProd q`). For axis tables `tab k j` (axis `k`, entry `j`), `cstEnt q tab l` is the
truncated product along the address `l`, and `cstEnt_append` is the step that adds an axis.
`cstAxTab p g t s k j` is the numerator of `axisPhase p g (t k) (s k) j` at scale `2^(p+g)`;
`cst_numer_chirpProd`: the numerator at scale `2^p` of `chirpProd p g t s` at address `x` is
`tdivN (p+g+2) (cstEnt (p+g) (cstAxTab p g t s) x · cstDiskC p)`.

**Bounds.** `cst_fits_numer`: `‖z‖ < 2^k` and `q + k + 1 ≤ w` give `Fits w (numer q z)`.
`cst_fits_axTab`, `cst_fits_ent`: for `p + g + 3 ≤ w` and `d ≤ 2^(p+g)` every table entry and
every partial product fits `w` bits (`‖truncProd‖ ≤ (1 + 2^{-(p+g)})^d ≤ e < 4`).
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Fast.ChirpSt

open IntegerMultBounds IntegerMultBounds.NLogN Complex
open IntegerMultBounds.MathlibTM2.Mult.ComplexConv IntegerMultBounds.MathlibTM2.Mult.Chirp
open IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.ResampA

/-- Close a goal about register files built from `Function.update`, splitting on register
equalities. -/
macro "cst_upd" : tactic =>
  `(tactic| (
    try simp only [Function.update_apply]
    try split_ifs
    all_goals (try subst_vars)
    all_goals simp_all))

noncomputable section

/-! ### Grid values -/

/-- The grid value `N / 2^q` of a numerator. -/
def cstGrid (q : ℕ) (N : GaussianInt) : ℂ := GaussianInt.toComplex N / 2 ^ q

theorem cst_numer_grid (q : ℕ) (N : GaussianInt) : numer q (cstGrid q N) = N := numer_grid q N

/-- A `q`-bit fixed-point number is the grid value of its numerator. -/
theorem cst_grid_numer {q : ℕ} {u : ℂ} (hu : IsFixed q u) : cstGrid q (numer q u) = u := by
  unfold cstGrid
  rw [← rhoC_eq_numer, rhoC_of_isFixed hu]

theorem cst_isFixed_grid (q : ℕ) (N : GaussianInt) : IsFixed q (cstGrid q N) := by
  refine ⟨N.re, N.im, ?_⟩
  unfold cstGrid
  rw [two_pow_complex]
  apply Complex.ext
  · rw [toComplex_div_re]
  · rw [toComplex_div_im]

theorem cst_rhoC_grid_mul (q : ℕ) (N₁ N₂ : GaussianInt) :
    rhoC q (cstGrid q N₁ * cstGrid q N₂) = cstGrid q (tdivN q (N₁ * N₂)) :=
  rhoC_mul_grid q N₁ N₂

/-- Truncating a grid value at the coarser scale `2^p`. -/
theorem cst_rhoC_grid_shift (p s : ℕ) (X : GaussianInt) :
    rhoC p (cstGrid (p + s) X) = cstGrid p (tdivN s X) := by
  have hpos : (2 : ℝ) ^ p ≠ 0 := by positivity
  have hs : (2 : ℝ) ^ s ≠ 0 := by positivity
  unfold cstGrid
  rw [two_pow_complex (p + s), two_pow_complex p]
  apply Complex.ext
  · rw [rhoC_re, toComplex_div_re, toComplex_div_re, tdivN_re, tdiv_rho0]
    congr 2
    rw [pow_add]
    field_simp
  · rw [rhoC_im, toComplex_div_im, toComplex_div_im, tdivN_im, tdiv_rho0]
    congr 2
    rw [pow_add]
    field_simp

/-- The real constant `2^(p+2) - 1` of the disk rounding. -/
def cstDiskC (p : ℕ) : GaussianInt := ⟨2 ^ (p + 2) - 1, 0⟩

/-- `diskPhase p` on a grid value at scale `2^(p+g)`: multiplication by `2^(p+2) - 1` and
truncation by `p + g + 2` bits. -/
theorem cst_diskPhase_grid (p g : ℕ) (M : GaussianInt) :
    diskPhase p (cstGrid (p + g) M) = cstGrid p (tdivN (p + g + 2) (M * cstDiskC p)) := by
  unfold diskPhase
  have h : (((1 - 1 / 2 ^ (p + 2) : ℝ) : ℂ) * cstGrid (p + g) M) =
      cstGrid (p + (p + g + 2)) (M * cstDiskC p) := by
    have hC : GaussianInt.toComplex (cstDiskC p) = (2 : ℂ) ^ (p + 2) - 1 := by
      rw [cstDiskC, GaussianInt.toComplex_def']
      push_cast
      ring
    unfold cstGrid
    rw [GaussianInt.toComplex_mul, hC]
    have h2 : (2 : ℂ) ^ (p + 2) ≠ 0 := pow_ne_zero _ two_ne_zero
    have h3 : (2 : ℂ) ^ (p + g) ≠ 0 := pow_ne_zero _ two_ne_zero
    push_cast
    rw [show p + (p + g + 2) = (p + 2) + (p + g) by ring, pow_add]
    field_simp
    ring
  rw [h, cst_rhoC_grid_shift]

/-- Conjugation of a grid value. -/
theorem cst_conj_grid (q : ℕ) (N : GaussianInt) :
    starRingEnd ℂ (cstGrid q N) = cstGrid q (star N) := by
  unfold cstGrid
  rw [map_div₀, GaussianInt.toComplex_star, map_pow, map_ofNat]

theorem cst_rho0_neg (x : ℝ) : rho0 (-x) = -rho0 x := by
  unfold rho0
  split_ifs with h1 h2 h2
  · have : x = 0 := by linarith
    subst this; simp
  · rw [Int.floor_neg]
  · rw [Int.ceil_neg]
  · exfalso; linarith

/-- The numerator of a conjugate is the conjugate numerator. -/
theorem cst_numer_conj (q : ℕ) (z : ℂ) : numer q (starRingEnd ℂ z) = star (numer q z) := by
  simp only [numer, Complex.conj_re, Complex.conj_im, Zsqrtd.star_mk, mul_neg, cst_rho0_neg]

/-- Scaling a grid value by `2^γ`. -/
theorem cst_two_pow_mul_grid (q γ : ℕ) (N : GaussianInt) :
    (2 : ℂ) ^ γ * cstGrid q N = cstGrid q (2 ^ γ * N) := by
  unfold cstGrid
  rw [GaussianInt.toComplex_mul, map_pow]
  simp only [map_ofNat]
  ring

/-- On the grid, `numer` commutes with the scale by `2^γ`. -/
theorem cst_numer_two_pow_mul {q : ℕ} {z : ℂ} (hz : IsFixed q z) (γ : ℕ) :
    numer q ((2 : ℂ) ^ γ * z) = 2 ^ γ * numer q z := by
  conv_lhs => rw [← cst_grid_numer hz]
  rw [cst_two_pow_mul_grid, cst_numer_grid]

/-- The numerator of a rounded product of grid values. -/
theorem cst_numer_rhoC_mul {q : ℕ} {u v : ℂ} (hu : IsFixed q u) (hv : IsFixed q v) :
    numer q (rhoC q (u * v)) = tdivN q (numer q u * numer q v) := by
  conv_lhs => rw [← cst_grid_numer hu, ← cst_grid_numer hv]
  rw [cst_rhoC_grid_mul, cst_numer_grid]

/-! ### Box addresses -/

/-- The addresses of the box `∏ [0, n_i)` in increasing order, axis `0` most significant. -/
def cstAddrs : List ℕ → List (List ℕ)
  | [] => [[]]
  | n :: ns => (List.range n).flatMap fun x => (cstAddrs ns).map (x :: ·)

/-- A least significant axis of length `m`: every address is followed by `0, …, m - 1`. -/
theorem cstAddrs_append (ns : List ℕ) (m : ℕ) :
    cstAddrs (ns ++ [m]) = (cstAddrs ns).flatMap fun l => (List.range m).map fun x => l ++ [x] := by
  induction ns with
  | nil =>
      simp only [List.nil_append, cstAddrs, List.flatMap_cons, List.flatMap_nil, List.append_nil,
        List.map_cons, List.map_nil]
      induction (List.range m) with
      | nil => rfl
      | cons a l ih => simp [ih]
  | cons n ns ih =>
      simp only [List.cons_append, cstAddrs, ih, List.flatMap_assoc, List.map_flatMap,
        List.flatMap_map, List.map_map]
      rfl

theorem cst_length_of_mem_addrs : ∀ {ns : List ℕ} {l : List ℕ}, l ∈ cstAddrs ns →
    l.length = ns.length
  | [], l, h => by simp [cstAddrs] at h; simp [h]
  | n :: ns, l, h => by
      simp only [cstAddrs, List.mem_flatMap, List.mem_range, List.mem_map] at h
      obtain ⟨x, _, l', hl', rfl⟩ := h
      simp [cst_length_of_mem_addrs hl']

theorem cst_length_addrs : ∀ ns : List ℕ, (cstAddrs ns).length = ns.prod
  | [] => rfl
  | n :: ns => by
      simp only [cstAddrs, List.length_flatMap, List.length_map, cst_length_addrs ns,
        List.prod_cons]
      simp [List.map_const', List.sum_replicate]

theorem cst_map_val_finRange (n : ℕ) : (List.finRange n).map Fin.val = List.range n := by
  apply List.ext_getElem (by simp)
  intro i h₁ h₂
  simp

/-- The box stream `rsaBox d t G` as a map over the address lists. -/
theorem cst_rsaBox_eq_addrs {α : Type} : ∀ (d : ℕ) (t : Fin d → ℕ)
    (G : ((i : Fin d) → Fin (t i)) → α) (H : List ℕ → α),
    (∀ x, G x = H (List.ofFn fun i => (x i : ℕ))) →
      rsaBox d t G = (cstAddrs (List.ofFn t)).map H
  | 0, t, G, H, h => by
      simp only [rsaBox, List.ofFn_zero, cstAddrs, List.map_cons, List.map_nil]
      rw [h]
      simp
  | d + 1, t, G, H, h => by
      simp only [rsaBox, List.ofFn_succ, cstAddrs, List.map_flatMap, List.map_map]
      rw [← cst_map_val_finRange, List.flatMap_map]
      refine List.flatMap_congr fun x₀ _ => ?_
      rw [cst_rsaBox_eq_addrs d (fun i => t i.succ) _ (fun l => H ((x₀ : ℕ) :: l))]
      · rfl
      · intro y
        rw [h]
        congr 1
        simp [List.ofFn_succ]

/-! ### Numerator boxes -/

/-- The box of the numerators at scale `2^q` of `f` on `∏ ZMod (t i)`, in address order, the
entry at `x` being the numerator of `f` at `(x_i : ZMod (t i))`. -/
def cstNumBox (q : ℕ) {d : ℕ} (t : Fin d → ℕ) (f : ((i : Fin d) → ZMod (t i)) → ℂ) :
    List GaussianInt :=
  rsaBox d t fun x => numer q (f fun i => ((x i : ℕ) : ZMod (t i)))

theorem cst_length_numBox (q : ℕ) {d : ℕ} (t : Fin d → ℕ)
    (f : ((i : Fin d) → ZMod (t i)) → ℂ) :
    (cstNumBox q t f).length = ∏ i, t i :=
  length_rsaBox d t _

/-- Two boxes entrywise. -/
theorem cst_zipWith_rsaBox {α β γ : Type} (φ : α → β → γ) (d : ℕ) (t : Fin d → ℕ)
    (F : ((i : Fin d) → Fin (t i)) → α) (G : ((i : Fin d) → Fin (t i)) → β) :
    List.zipWith φ (rsaBox d t F) (rsaBox d t G) = rsaBox d t fun x => φ (F x) (G x) := by
  have hF : rsaBox d t F = (rsaBox d t fun x => (F x, G x)).map Prod.fst := by
    rw [← rsaBox_map]
  have hG : rsaBox d t G = (rsaBox d t fun x => (F x, G x)).map Prod.snd := by
    rw [← rsaBox_map]
  rw [hF, hG, List.zipWith_map, List.zipWith_self, ← rsaBox_map]

/-! ### Membership and layouts -/

theorem cst_mem_rsaBox {α : Type} : ∀ (d : ℕ) (t : Fin d → ℕ)
    (F : ((i : Fin d) → Fin (t i)) → α) (y : α), y ∈ rsaBox d t F → ∃ x, F x = y
  | 0, t, F, y, h => by
      simp only [rsaBox, List.mem_singleton] at h
      exact ⟨_, h.symm⟩
  | d + 1, t, F, y, h => by
      simp only [rsaBox, List.mem_flatMap] at h
      obtain ⟨x₀, _, hy⟩ := h
      obtain ⟨x, hx⟩ := cst_mem_rsaBox d _ _ y hy
      exact ⟨_, hx⟩

theorem cst_mem_numBox {q d : ℕ} {t : Fin d → ℕ} {f : ((i : Fin d) → ZMod (t i)) → ℂ}
    {N : GaussianInt} (h : N ∈ cstNumBox q t f) :
    ∃ x : (i : Fin d) → Fin (t i), numer q (f fun i => ((x i : ℕ) : ZMod (t i))) = N :=
  cst_mem_rsaBox d t _ N h

/-- A complex-product layout lifted through an injective map `c`: the final register file of
`RsaRuns.of_c` for a contract that updates one register. -/
lemma cst_extend_update {R : Type} [DecidableEq R] {A : ℕ} (c : CR → R)
    (hc : Function.Injective c) (ρ : R → List (Fin (A + 4))) (a : CR) (l : List (Fin (A + 4))) :
    Function.extend c (Function.update (fun x => ρ (c x)) a l) ρ =
      Function.update ρ (c a) l := by
  funext r
  by_cases hr : ∃ x, c x = r
  · obtain ⟨x, rfl⟩ := hr
    rw [hc.extend_apply]
    by_cases hx : x = a
    · subst hx; simp
    · rw [Function.update_of_ne hx, Function.update_of_ne (hc.ne hx)]
  · rw [Function.extend_apply' _ _ _ hr, Function.update_of_ne]
    rintro rfl
    exact hr ⟨a, rfl⟩


/-- `Ready` depends only on the scratch and unary registers. -/
lemma cst_ready_of_eq {A : ℕ} {ρ ρ' : CR → List (Fin (A + 4))} {w q : ℕ} (hr : Ready ρ w q)
    (h : ∀ x, x ≠ .xs → x ≠ .ys → x ≠ .xsv → x ≠ .ysv → x ≠ .acc → x ≠ .out →
      ρ' x = ρ x) :
    Ready ρ' w q := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
    h20, h21, h22, h23, h24⟩ := hr
  constructor <;> simp [*]

/-! ### Truncated products of numerators -/

/-- The truncated product of numerators at scale `2^q`, left to right with `tdivN q` after each
multiplication; the unit `2^q` for the empty list. -/
def cstTP (q : ℕ) : List GaussianInt → GaussianInt
  | [] => ⟨2 ^ q, 0⟩
  | N :: Ns => Ns.foldl (fun acc M => tdivN q (acc * M)) N

theorem cstTP_append (q : ℕ) : ∀ (Ns : List GaussianInt), Ns ≠ [] → ∀ M : GaussianInt,
    cstTP q (Ns ++ [M]) = tdivN q (cstTP q Ns * M)
  | N :: Ns, _, M => by simp [cstTP, List.foldl_append]

theorem cst_foldl_grid (q : ℕ) : ∀ (Ns : List GaussianInt) (acc : GaussianInt),
    (Ns.map (cstGrid q)).foldl (fun a b => rhoC q (a * b)) (cstGrid q acc) =
      cstGrid q (Ns.foldl (fun acc M => tdivN q (acc * M)) acc)
  | [], _ => rfl
  | N :: Ns, acc => by
      simp only [List.map_cons, List.foldl_cons, cst_rhoC_grid_mul]
      exact cst_foldl_grid q Ns _

/-- `cstTP` is the numerator of `Chirp.truncProd`. -/
theorem cst_truncProd_grid (q : ℕ) (Ns : List GaussianInt) :
    truncProd q (Ns.map (cstGrid q)) = cstGrid q (cstTP q Ns) := by
  cases Ns with
  | nil =>
      have h : (2 : ℂ) ^ q ≠ 0 := pow_ne_zero _ two_ne_zero
      simp only [List.map_nil, truncProd, cstTP, cstGrid, GaussianInt.toComplex_def']
      push_cast
      simp [h]
  | cons N Ns => exact cst_foldl_grid q Ns N

/-- The truncated product along the address `l`: entry `l_k` of the table of axis `k`. -/
def cstEnt (q : ℕ) (tab : ℕ → ℕ → GaussianInt) (l : List ℕ) : GaussianInt :=
  cstTP q (l.mapIdx tab)

theorem cstEnt_single (q : ℕ) (tab : ℕ → ℕ → GaussianInt) (j : ℕ) :
    cstEnt q tab [j] = tab 0 j := rfl

/-- Adding a least significant axis. -/
theorem cstEnt_append (q : ℕ) (tab : ℕ → ℕ → GaussianInt) {l : List ℕ} (hl : l ≠ [])
    (x : ℕ) : cstEnt q tab (l ++ [x]) = tdivN q (cstEnt q tab l * tab l.length x) := by
  unfold cstEnt
  rw [List.mapIdx_append]
  simp only [List.mapIdx_cons, List.mapIdx_nil, Nat.zero_add]
  exact cstTP_append q _ (by simpa using hl) _

/-! ### The chirp kernel -/

/-- The numerator at scale `2^(p+g)` of the chirp table entry `axisPhase p g (t k) (s k) j`
(`0` for `k ≥ d`). -/
def cstAxTab (p g : ℕ) {d : ℕ} (t s : Fin d → ℕ) (k j : ℕ) : GaussianInt :=
  if h : k < d then
    numer (p + g) (axisPhase p g (t ⟨k, h⟩) (s ⟨k, h⟩) (j : ZMod (t ⟨k, h⟩)))
  else 0

theorem cst_grid_axTab (p g : ℕ) {d : ℕ} (t s : Fin d → ℕ) {k : ℕ} (hk : k < d)
    (j : ℕ) :
    cstGrid (p + g) (cstAxTab p g t s k j) =
      axisPhase p g (t ⟨k, hk⟩) (s ⟨k, hk⟩) (j : ZMod (t ⟨k, hk⟩)) := by
  unfold cstAxTab
  simp only [hk, ↓reduceDIte]
  exact cst_grid_numer (isFixed_roundC _ _)

/-- The numerator at scale `2^p` of the chirp kernel at the address `x`. -/
theorem cst_numer_chirpProd (p g : ℕ) {d : ℕ} (t s : Fin d → ℕ)
    (x : (i : Fin d) → Fin (t i)) :
    numer p (chirpProd p g t s fun i => ((x i : ℕ) : ZMod (t i))) =
      tdivN (p + g + 2)
        (cstEnt (p + g) (cstAxTab p g t s) (List.ofFn fun i => (x i : ℕ)) * cstDiskC p) := by
  have hl : (List.ofFn fun i => axisPhase p g (t i) (s i) ((x i : ℕ) : ZMod (t i))) =
      ((List.ofFn fun i => (x i : ℕ)).mapIdx (cstAxTab p g t s)).map (cstGrid (p + g)) := by
    apply List.ext_getElem (by simp)
    intro i h₁ h₂
    simp only [List.getElem_ofFn, List.getElem_map, List.getElem_mapIdx]
    rw [cst_grid_axTab p g t s (by simpa using h₁)]
  unfold chirpProd
  rw [hl, cst_truncProd_grid, cst_diskPhase_grid, cst_numer_grid]
  rfl

/-- The numerator box of the chirp kernel: the truncated products over all addresses, then the
disk rounding. -/
theorem cstNumBox_chirpProd (p g : ℕ) {d : ℕ} (t s : Fin d → ℕ) :
    cstNumBox p t (chirpProd p g t s) =
      ((cstAddrs (List.ofFn t)).map (cstEnt (p + g) (cstAxTab p g t s))).map
        fun M => tdivN (p + g + 2) (M * cstDiskC p) := by
  rw [List.map_map]
  exact cst_rsaBox_eq_addrs d t _ _ fun x => cst_numer_chirpProd p g t s x

/-! ### Bounds -/

/-- A complex number below `2^k` has a numerator at scale `2^q` that fits `w` bits when
`q + k + 1 ≤ w`. -/
theorem cst_fits_numer {q k w : ℕ} {z : ℂ} (hz : ‖z‖ < 2 ^ k) (hw : q + k + 1 ≤ w) :
    Fits w (numer q z) := by
  have hq : (0 : ℝ) < 2 ^ q := by positivity
  have hpow : (2 : ℝ) ^ q * 2 ^ k ≤ 2 ^ (w - 1) := by
    rw [← pow_add]; exact pow_le_pow_right₀ (by norm_num) (by omega)
  have key : ∀ x : ℝ, |x| ≤ ‖z‖ → |(rho0 (2 ^ q * x) : ℤ)| < (2 : ℤ) ^ (w - 1) := by
    intro x hx
    have h1 := abs_rho0_le (2 ^ q * x)
    rw [abs_mul, abs_of_pos hq] at h1
    have h2 : (2 : ℝ) ^ q * |x| < 2 ^ q * 2 ^ k := by
      exact mul_lt_mul_of_pos_left (lt_of_le_of_lt hx hz) hq
    have h3 : (|(rho0 (2 ^ q * x) : ℤ)| : ℝ) < ((2 : ℤ) ^ (w - 1) : ℤ) := by
      push_cast
      rw [← Int.cast_abs] at h1 ⊢
      linarith
    exact_mod_cast h3
  exact ⟨key z.re (Complex.abs_re_le_norm z), key z.im (Complex.abs_im_le_norm z)⟩

/-- The truncated product stays below the `|l|`-th power of a bound `B ≥ 1` on the entries. -/
theorem cst_norm_truncProd_le (q : ℕ) {B : ℝ} (hB : 1 ≤ B) :
    ∀ l : List ℂ, (∀ z ∈ l, ‖z‖ ≤ B) → ‖truncProd q l‖ ≤ B ^ l.length
  | [], _ => by simp [truncProd]
  | a :: l, h => by
      have key : ∀ (l : List ℂ) (acc : ℂ) (m : ℕ), (∀ z ∈ l, ‖z‖ ≤ B) →
          ‖acc‖ ≤ B ^ m →
          ‖l.foldl (fun acc b => rhoC q (acc * b)) acc‖ ≤ B ^ (m + l.length) := by
        intro l
        induction l with
        | nil => intro acc m _ h; simpa using h
        | cons b l ih =>
            intro acc m hl hacc
            simp only [List.foldl_cons, List.length_cons]
            have hstep : ‖rhoC q (acc * b)‖ ≤ B ^ (m + 1) :=
              calc ‖rhoC q (acc * b)‖ ≤ ‖acc * b‖ := norm_rhoC_le _ _
                _ = ‖acc‖ * ‖b‖ := norm_mul _ _
                _ ≤ B ^ m * B := mul_le_mul hacc (hl b (by simp)) (norm_nonneg _) (by positivity)
                _ = B ^ (m + 1) := by rw [pow_succ]
            have := ih (rhoC q (acc * b)) (m + 1) (fun z hz => hl z (by simp [hz])) hstep
            rwa [show m + (l.length + 1) = m + 1 + l.length by ring]
      have := key l a 1 (fun z hz => h z (by simp [hz])) (by simpa using h a (by simp))
      simpa [truncProd, Nat.add_comm] using this

/-- `(1 + 2^{-q})^d < 4` for `d ≤ 2^q`. -/
theorem cst_pow_lt_four {q d : ℕ} (hd : d ≤ 2 ^ q) : (1 + 1 / 2 ^ q : ℝ) ^ d < 4 := by
  have h1 : (1 + 1 / 2 ^ q : ℝ) ≤ Real.exp (1 / 2 ^ q) := by
    have := Real.add_one_le_exp (1 / 2 ^ q : ℝ); linarith
  have h2 : (1 + 1 / 2 ^ q : ℝ) ^ d ≤ Real.exp (1 / 2 ^ q) ^ d :=
    pow_le_pow_left₀ (by positivity) h1 d
  rw [← Real.exp_nat_mul] at h2
  have h3 : (d : ℝ) * (1 / 2 ^ q) ≤ 1 := by
    rw [mul_one_div, div_le_one (by positivity)]; exact_mod_cast hd
  have h4 := Real.exp_le_exp.2 h3
  have h5 := Real.exp_one_lt_d9
  linarith

/-- Every chirp table entry fits `w` bits for `p + g + 3 ≤ w`. -/
theorem cst_fits_axTab {p g w d : ℕ} (t s : Fin d → ℕ) [∀ i, NeZero (t i)]
    (hw : p + g + 3 ≤ w) (k j : ℕ) : Fits w (cstAxTab p g t s k j) := by
  unfold cstAxTab
  split_ifs with hk
  · apply cst_fits_numer (k := 2) _ (by omega)
    have h := (axisPhase_spec p g (t ⟨k, hk⟩) (s ⟨k, hk⟩) (j : ZMod (t ⟨k, hk⟩))).2.2
    have h1 : (1 : ℝ) / 2 ^ (p + g) ≤ 1 := by
      rw [div_le_one (by positivity)]; exact one_le_pow₀ (by norm_num)
    norm_num
    linarith
  · constructor <;> simp

/-- Every partial chirp product along an address of at most `d` axes fits `w` bits for
`p + g + 3 ≤ w` and `d ≤ 2^(p+g)`. -/
theorem cst_fits_ent {p g w d : ℕ} (t s : Fin d → ℕ) [∀ i, NeZero (t i)]
    (hw : p + g + 3 ≤ w) (hd : d ≤ 2 ^ (p + g)) (l : List ℕ) (hl : l.length ≤ d) :
    Fits w (cstEnt (p + g) (cstAxTab p g t s) l) := by
  rw [← cst_numer_grid (p + g) (cstEnt (p + g) (cstAxTab p g t s) l)]
  apply cst_fits_numer (k := 2) _ (by omega)
  unfold cstEnt
  rw [← cst_truncProd_grid]
  have hB : (1 : ℝ) ≤ 1 + 1 / 2 ^ (p + g) := by
    have : (0 : ℝ) ≤ 1 / 2 ^ (p + g) := by positivity
    linarith
  have h := cst_norm_truncProd_le (p + g) hB ((l.mapIdx (cstAxTab p g t s)).map (cstGrid (p + g)))
    (by
      intro z hz
      obtain ⟨N, hN, rfl⟩ := List.mem_map.1 hz
      obtain ⟨i, hi, rfl⟩ := List.mem_mapIdx.1 hN
      rw [cst_grid_axTab p g t s (by omega)]
      exact (axisPhase_spec _ _ _ _ _).2.2)
  simp only [List.length_map, List.length_mapIdx] at h
  calc _ ≤ (1 + 1 / 2 ^ (p + g) : ℝ) ^ l.length := h
    _ ≤ (1 + 1 / 2 ^ (p + g) : ℝ) ^ d := pow_le_pow_right₀ hB hl
    _ < 4 := cst_pow_lt_four hd
    _ = 2 ^ 2 := by norm_num

/-- The disk constant fits `w` bits for `p + 3 ≤ w`. -/
theorem cst_fits_diskC {p w : ℕ} (hw : p + 3 ≤ w) : Fits w (cstDiskC p) := by
  have h : (2 : ℤ) ^ (p + 2) ≤ 2 ^ (w - 1) := pow_le_pow_right₀ (by norm_num) (by omega)
  have h0 : (1 : ℤ) ≤ 2 ^ (p + 2) := one_le_pow₀ (by norm_num)
  refine ⟨?_, by simp [cstDiskC]⟩
  simp only [cstDiskC]
  rw [abs_of_nonneg (by omega)]
  omega

end

end IntegerMultBounds.MathlibTM2.Fast.ChirpSt
