module

public import IntegerMultBounds.MathlibTM2.Host.BinArith
public import IntegerMultBounds.MathlibTM2.Layer.Format

/-!
# A binary register machine for the integer tables

The table machines run on host registers (`IntegerMultBounds.MathlibTM2.Host`) through a small structured language of
binary registers. A program `TblCode n` has `n` variables, each held in its own host register as
a `W`-bit numeral `binSyms W x` (least significant bit on top), and an emission register `acc`.

## Registers

`rg : TblR n → Fin T` is an injective register layout:

* `v i`, `i : Fin n`: the variables;
* `wr`: `W` symbols (any), the word width; `wn`: `w` symbols (any), the emission width;
* `acc`: the emitted symbols, the latest on top;
* `z j`, `j : Fin 12`: scratch registers, empty before and after every instruction.
  Instructions compute on copies of their operands in scratch registers and store the result
  last, so operands and destination may coincide.

## Host programs of the instructions

* `add`, `sub`: `badd`, `bsub` on the copies; `mul`: `bmul` into `2W` bits, then the low `W`
  bits move out (`tbl_xfer_runs`); `div`, `mod`: a zero test (`beq`) and `bdivmod`
  (`tbl_divCore_runs`); `inc`: `countIter`; `emit`: one pair symbol per symbol of `wn`
  (`tbl_emitScan_runs`).
* Tests `a < b` (`tblTest`): `blt` into the scan slot of `z 10`, read by `tblTst`
  (`tbl_test_exec`).
* Each instruction costs at most `tblC W w` steps (`tbl_ins_runs`): `bmul` is the largest,
  `24 W² + 100 W + 100`.

## Semantics

`TblIns.run` gives the effect of one instruction on a state `TblSt n A` (variable values and the
emission list), with arithmetic modulo `2 ^ W`:

* `add`, `sub`, `mul`: `c := (a + b) mod 2^W`, `(a - b) mod 2^W`, `a b mod 2^W`;
* `div`, `mod`: `c := a / b`, `a % b` (natural division, `a / 0 = 0`, `a % 0 = a`);
* `copy`, `zero`, `inc`: `c := a`, `0`, `(c + 1) mod 2^W`;
* `emit a b`: `acc` gains the `w` pair symbols `coeffSyms A w (a mod 2^w, b mod 2^w)`, least
  significant first, so the last one ends on top.

`TblBig A W w c st st' k` is the big-step semantics of `TblCode` (`seq`, `ite a b` on `a < b`,
`loop a b` while `a < b`) with an atom count `k`.

## Compilation

`tblCompile rg c` is the host program of `c`. `tblCompile_runs`: from registers carrying a state
`st` with all values below `2 ^ W`, the program reaches registers carrying `st'` in at most
`k · tblC W w` steps, `tblC W w = 32 (W + 4)² + 8 w`, every register outside the layout, the
input and output stacks and the left stacks unchanged, and the `user` component kept.
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Fast.TableVM

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Layer


/-! ### Register roles -/

/-- Register roles of a table machine with `n` variables. -/
inductive TblR (n : ℕ) where
  | v (i : Fin n)
  | wr
  | wn
  | acc
  | z (j : Fin 12)
  deriving DecidableEq

section Contracts

variable {T Q A : ℕ} {U : Type} {P : Type} (body : P → Pr P T Q A U) {n : ℕ}
  (rg : TblR n → Fin T)

/-- The stacks `S` carry the register file `ρ`. -/
def tblHolds (S : Stacks T A) (ρ : TblR n → List (Fin (A + 4))) : Prop := ∀ r, S.R (rg r) = ρ r

/-- `S'` agrees with `S` on `inp`, `out`, the left stacks and every register outside `rg`. -/
def tblFr (S S' : Stacks T A) : Prop :=
  S'.inp = S.inp ∧ S'.out = S.out ∧ S'.L = S.L ∧ ∀ k, (∀ r, rg r ≠ k) → S'.R k = S.R k

/-- The contract of a program on the register file: from `ρ` to `ρ'` within `b` steps. -/
def tblRuns (p : Pr P T Q A U) (ρ ρ' : TblR n → List (Fin (A + 4))) (b : ℕ) : Prop :=
  ∀ v S, tblHolds rg S ρ → ∃ v' S' m, v'.user = v.user ∧ m ≤ b ∧
    Exec body p (mk v S) m (mk v' S') ∧ tblHolds rg S' ρ' ∧ tblFr rg S S'

variable {body rg}

lemma tblFr.refl (S : Stacks T A) : tblFr rg S S := ⟨rfl, rfl, rfl, fun _ _ => rfl⟩

lemma tblFr.trans {S₁ S₂ S₃ : Stacks T A} (h₁ : tblFr rg S₁ S₂) (h₂ : tblFr rg S₂ S₃) :
    tblFr rg S₁ S₃ :=
  ⟨h₂.1.trans h₁.1, h₂.2.1.trans h₁.2.1, h₂.2.2.1.trans h₁.2.2.1,
    fun k hk => (h₂.2.2.2 k hk).trans (h₁.2.2.2 k hk)⟩

theorem tblRuns.seq {p q : Pr P T Q A U} {ρ₁ ρ₂ ρ₃ : TblR n → List (Fin (A + 4))} {b₁ b₂ : ℕ}
    (h₁ : tblRuns body rg p ρ₁ ρ₂ b₁) (h₂ : tblRuns body rg q ρ₂ ρ₃ b₂) :
    tblRuns body rg (.seq p q) ρ₁ ρ₃ (b₁ + b₂) := by
  intro v S hS
  obtain ⟨v₁, S₁, n₁, hu₁, hn₁, he₁, hS₁, hf₁⟩ := h₁ v S hS
  obtain ⟨v₂, S₂, n₂, hu₂, hn₂, he₂, hS₂, hf₂⟩ := h₂ v₁ S₁ hS₁
  exact ⟨v₂, S₂, n₁ + n₂, hu₂.trans hu₁, by omega, Exec.seq he₁ he₂, hS₂, hf₁.trans hf₂⟩

theorem tblRuns.mono {p : Pr P T Q A U} {ρ ρ' : TblR n → List (Fin (A + 4))} {b b' : ℕ}
    (h : tblRuns body rg p ρ ρ' b) (hb : b ≤ b') : tblRuns body rg p ρ ρ' b' := by
  intro v S hS
  obtain ⟨v', S', m, hu, hm, he, hS', hf⟩ := h v S hS
  exact ⟨v', S', m, hu, hm.trans hb, he, hS', hf⟩

theorem tblRuns.congr {p : Pr P T Q A U} {ρ ρ' ρ'' : TblR n → List (Fin (A + 4))} {b : ℕ}
    (h : tblRuns body rg p ρ ρ' b) (he : ρ' = ρ'') : tblRuns body rg p ρ ρ'' b := he ▸ h

/-! ### Register files under updates -/

lemma tbl_upd_comp (hrg : Function.Injective rg) {β : Type} (g : Fin T → β) (a : TblR n) (x : β)
    (r : TblR n) :
    Function.update g (rg a) x (rg r) = Function.update (fun r => g (rg r)) a x r := by
  by_cases h : r = a
  · subst h; simp
  · rw [Function.update_of_ne (hrg.ne h), Function.update_of_ne h]

lemma tbl_holds_upd (hrg : Function.Injective rg) {R : Fin T → List (Fin (A + 4))}
    {ρ : TblR n → List (Fin (A + 4))} (h : ∀ r, R (rg r) = ρ r) (a : TblR n)
    (x : List (Fin (A + 4))) :
    ∀ r, Function.update R (rg a) x (rg r) = Function.update ρ a x r := by
  intro r
  rw [tbl_upd_comp hrg]
  have : (fun r => R (rg r)) = ρ := funext h
  rw [this]

lemma tbl_upd_off {β : Type} (g : Fin T → β) (a : TblR n) (x : β) {k : Fin T}
    (hk : ∀ r, rg r ≠ k) : Function.update g (rg a) x k = g k :=
  Function.update_of_ne (hk a).symm _ _

lemma tbl_nodup (hrg : Function.Injective rg) {l : List (TblR n)} (h : l.Nodup) :
    (l.map rg).Nodup := h.map hrg

/-! ### Primitive contracts -/

variable (hrg : Function.Injective rg)
include hrg

theorem tbl_moveR_runs {a b : TblR n} (hab : a ≠ b) (ρ : TblR n → List (Fin (A + 4))) :
    tblRuns body rg (moveR (rg a) (rg b) id) ρ
      (Function.update (Function.update ρ a []) b ((ρ a).reverse ++ ρ b))
      (2 * (ρ a).length + 2) := by
  intro v S hS
  obtain ⟨v', hu, he⟩ := moveR_exec body (rg a) (rg b) (hrg.ne hab) id v S
  refine ⟨v', _, _, hu, by rw [hS], he, ?_, ⟨rfl, rfl, rfl, fun k hk => ?_⟩⟩
  · intro r
    simp only [movedR, List.map_id]
    rw [tbl_holds_upd hrg (tbl_holds_upd hrg hS a []) b, hS, hS]
  · simp only [movedR, tbl_upd_off _ _ _ hk]

theorem tbl_bclear_runs (a : TblR n) (ρ : TblR n → List (Fin (A + 4))) :
    tblRuns body rg (bclear (rg a)) ρ (Function.update ρ a []) (2 * (ρ a).length + 2) := by
  intro v S hS
  obtain ⟨v', hu, -, he⟩ := bclear_exec body (rg a) v S
  exact ⟨v', _, _, hu, by rw [hS], he, tbl_holds_upd hrg hS a [],
    ⟨rfl, rfl, rfl, fun k hk => tbl_upd_off _ _ _ hk⟩⟩

theorem tbl_bcopy_runs {a c t₁ t₂ : TblR n} (hd : [a, c, t₁, t₂].Nodup)
    (ρ : TblR n → List (Fin (A + 4))) (h₁ : ρ t₁ = []) (h₂ : ρ t₂ = []) :
    tblRuns body rg (bcopy (rg a) (rg c) (rg t₁) (rg t₂)) ρ (Function.update ρ c (ρ a ++ ρ c))
      (6 * (ρ a).length + 6) := by
  intro v S hS
  obtain ⟨v', hu, he⟩ := bcopy_exec body (tbl_nodup hrg hd) v S (by rw [hS, h₁])
    (by rw [hS, h₂])
  refine ⟨v', _, _, hu, by rw [hS], he, ?_, ⟨rfl, rfl, rfl, fun k hk => tbl_upd_off _ _ _ hk⟩⟩
  intro r
  dsimp only
  rw [tbl_holds_upd hrg hS c, hS, hS]

theorem tbl_bzero_runs {wR c t : TblR n} (hd : [wR, c, t].Nodup)
    (ρ : TblR n → List (Fin (A + 4))) (ht : ρ t = []) :
    tblRuns body rg (bzero (rg wR) (rg c) (rg t)) ρ
      (Function.update ρ c (binSyms (ρ wR).length 0 ++ ρ c)) (4 * (ρ wR).length + 4) := by
  intro v S hS
  obtain ⟨v', hu, he⟩ := bzero_exec body (tbl_nodup hrg hd) v S (by rw [hS, ht])
  refine ⟨v', _, _, hu, by rw [hS], he, ?_, ⟨rfl, rfl, rfl, fun k hk => tbl_upd_off _ _ _ hk⟩⟩
  intro r
  dsimp only
  rw [tbl_holds_upd hrg hS c, hS, hS]

theorem tbl_badd_runs {a b c tx ty tz : TblR n} (hd : [a, b, c, tx, ty, tz].Nodup) {cy : TblR n}
    (hca : cy ≠ a) (hcb : cy ≠ b) {L x y : ℕ} (hx : x < 2 ^ L) (hy : y < 2 ^ L)
    (ρ : TblR n → List (Fin (A + 4))) (ha : ρ a = binSyms L x) (hb : ρ b = binSyms L y)
    (htx : ρ tx = []) (hty : ρ ty = []) (htz : ρ tz = []) :
    tblRuns body rg (badd (rg a) (rg b) (rg c) (rg tx) (rg ty) (rg tz) (rg cy)) ρ
      (Function.update ρ c (binSyms L ((x + y) % 2 ^ L) ++ ρ c)) (8 * L + 8) := by
  intro v S hS
  obtain ⟨v', hu, -, -, he⟩ := badd_exec body (tbl_nodup hrg hd) (hrg.ne hca) (hrg.ne hcb) hx hy
    v S (by rw [hS, ha]) (by rw [hS, hb]) (by rw [hS, htx]) (by rw [hS, hty]) (by rw [hS, htz])
  refine ⟨v', _, _, hu, le_rfl, he, ?_, ⟨rfl, rfl, rfl, fun k hk => tbl_upd_off _ _ _ hk⟩⟩
  intro r
  dsimp only
  rw [tbl_holds_upd hrg hS c, hS]

theorem tbl_bsub_runs {a b c tx ty tz : TblR n} (hd : [a, b, c, tx, ty, tz].Nodup) {cy : TblR n}
    (hca : cy ≠ a) (hcb : cy ≠ b) {L x y : ℕ} (hx : x < 2 ^ L) (hy : y < 2 ^ L)
    (ρ : TblR n → List (Fin (A + 4))) (ha : ρ a = binSyms L x) (hb : ρ b = binSyms L y)
    (htx : ρ tx = []) (hty : ρ ty = []) (htz : ρ tz = []) :
    tblRuns body rg (bsub (rg a) (rg b) (rg c) (rg tx) (rg ty) (rg tz) (rg cy)) ρ
      (Function.update ρ c (binSyms L ((x + 2 ^ L - y) % 2 ^ L) ++ ρ c)) (8 * L + 8) := by
  intro v S hS
  obtain ⟨v', hu, -, -, he⟩ := bsub_exec body (tbl_nodup hrg hd) (hrg.ne hca) (hrg.ne hcb) hx hy
    v S (by rw [hS, ha]) (by rw [hS, hb]) (by rw [hS, htx]) (by rw [hS, hty]) (by rw [hS, htz])
  refine ⟨v', _, _, hu, le_rfl, he, ?_, ⟨rfl, rfl, rfl, fun k hk => tbl_upd_off _ _ _ hk⟩⟩
  intro r
  dsimp only
  rw [tbl_holds_upd hrg hS c, hS]

theorem tbl_bmul_runs {a b c s t tx ty tz : TblR n} (hd : [a, b, c, s, t, tx, ty, tz].Nodup)
    {cy : TblR n} (hcc : cy ≠ c) (hcs : cy ≠ s) {La Lb x y : ℕ} (hx : x < 2 ^ La)
    (hy : y < 2 ^ Lb) (ρ : TblR n → List (Fin (A + 4))) (ha : ρ a = binSyms La x)
    (hb : ρ b = binSyms Lb y) (hc : ρ c = []) (hs : ρ s = []) (ht : ρ t = []) (htx : ρ tx = [])
    (hty : ρ ty = []) (htz : ρ tz = []) :
    tblRuns body rg (bmul (rg a) (rg b) (rg c) (rg s) (rg t) (rg tx) (rg ty) (rg tz) (rg cy)) ρ
      (Function.update ρ c (binSyms (La + Lb) (x * y)))
      (La * (12 * (La + Lb) + 20) + 16 * (La + Lb) + 24) := by
  intro v S hS
  obtain ⟨v', m, hu, hm, he⟩ := bmul_exec body (tbl_nodup hrg hd) (hrg.ne hcc) (hrg.ne hcs) hx hy
    v S (by rw [hS, ha]) (by rw [hS, hb]) (by rw [hS, hc]) (by rw [hS, hs]) (by rw [hS, ht])
    (by rw [hS, htx]) (by rw [hS, hty]) (by rw [hS, htz])
  refine ⟨v', _, m, hu, hm, he, ?_, ⟨rfl, rfl, rfl, fun k hk => tbl_upd_off _ _ _ hk⟩⟩
  intro r
  dsimp only
  rw [tbl_holds_upd hrg hS c]

theorem tbl_bdivmod_runs {a b q r bw rr t tx ty tz : TblR n}
    (hd : [a, b, q, r, bw, rr, t, tx, ty, tz].Nodup) {cy : TblR n} (hcr : cy ≠ rr)
    (hcb : cy ≠ bw) {La Lb x y : ℕ} (hx : x < 2 ^ La) (hy : y < 2 ^ Lb) (hy0 : 0 < y)
    (ρ : TblR n → List (Fin (A + 4))) (ha : ρ a = binSyms La x) (hb : ρ b = binSyms Lb y)
    (hbw : ρ bw = []) (hrr : ρ rr = []) (ht : ρ t = []) (htx : ρ tx = []) (hty : ρ ty = [])
    (htz : ρ tz = []) :
    tblRuns body rg
      (bdivmod (rg a) (rg b) (rg q) (rg r) (rg bw) (rg rr) (rg t) (rg tx) (rg ty) (rg tz) (rg cy))
      ρ (Function.update (Function.update ρ q (binSyms La (x / y) ++ ρ q)) r
        (binSyms Lb (x % y) ++ ρ r))
      (La * (12 * Lb + 35) + 20 * Lb + 36) := by
  intro v S hS
  obtain ⟨v', m, hu, hm, he⟩ := bdivmod_exec body (tbl_nodup hrg hd) (hrg.ne hcr) (hrg.ne hcb)
    hx hy hy0 v S (by rw [hS, ha]) (by rw [hS, hb]) (by rw [hS, hbw]) (by rw [hS, hrr])
    (by rw [hS, ht]) (by rw [hS, htx]) (by rw [hS, hty]) (by rw [hS, htz])
  refine ⟨v', _, m, hu, hm, he, ?_, ⟨rfl, rfl, rfl, fun k hk => ?_⟩⟩
  · intro r'
    dsimp only
    rw [tbl_holds_upd hrg (tbl_holds_upd hrg hS q _) r, hS, hS]
  · dsimp only
    rw [tbl_upd_off _ _ _ hk, tbl_upd_off _ _ _ hk]

theorem tbl_countIter_runs {c tmp : TblR n} (hct : c ≠ tmp) (cy : TblR n) {W j : ℕ}
    (ρ : TblR n → List (Fin (A + 4))) (hc : ρ c = binSyms W j) (ht : ρ tmp = []) :
    tblRuns body rg (countIter (rg c) (rg tmp) (rg cy)) ρ
      (Function.update ρ c (binSyms W (j + 1))) (4 * W + 5) := by
  intro v S hS
  obtain ⟨v', hu, he⟩ := countIter_exec body (hrg.ne hct) (rg cy) (W := W) (j := j) v S
    (by rw [hS, hc]) (by rw [hS, ht])
  refine ⟨v', _, _, hu, le_rfl, he, ?_, ⟨rfl, rfl, rfl, fun k hk => tbl_upd_off _ _ _ hk⟩⟩
  intro r
  dsimp only
  rw [tbl_holds_upd hrg hS c]

end Contracts

/-! ### States and instructions -/

/-- A machine state: variable values and the emitted symbols, the latest on top. -/
structure TblSt (n A : ℕ) where
  val : Fin n → ℕ
  acc : List (Fin (A + 4))

/-- Instructions; `c` is the destination. -/
inductive TblIns (n : ℕ) where
  | add (a b c : Fin n)
  | sub (a b c : Fin n)
  | mul (a b c : Fin n)
  | div (a b c : Fin n)
  | mod (a b c : Fin n)
  | copy (a c : Fin n)
  | zero (c : Fin n)
  | inc (c : Fin n)
  | emit (a b : Fin n)

/-- The `w` pair symbols of the coefficient `(x mod 2^w, y mod 2^w)`, least significant first. -/
def tblPairs (A w x y : ℕ) : List (Fin (A + 4)) :=
  coeffSyms A w (((x : ZMod (2 ^ w))), ((y : ZMod (2 ^ w))))

/-- The effect of one instruction, with words of `W` bits and emission width `w`. -/
def TblIns.run {n : ℕ} (A W w : ℕ) : TblIns n → TblSt n A → TblSt n A
  | .add a b c, st => ⟨Function.update st.val c ((st.val a + st.val b) % 2 ^ W), st.acc⟩
  | .sub a b c, st => ⟨Function.update st.val c ((st.val a + 2 ^ W - st.val b) % 2 ^ W), st.acc⟩
  | .mul a b c, st => ⟨Function.update st.val c ((st.val a * st.val b) % 2 ^ W), st.acc⟩
  | .div a b c, st => ⟨Function.update st.val c (st.val a / st.val b), st.acc⟩
  | .mod a b c, st => ⟨Function.update st.val c (st.val a % st.val b), st.acc⟩
  | .copy a c, st => ⟨Function.update st.val c (st.val a), st.acc⟩
  | .zero c, st => ⟨Function.update st.val c 0, st.acc⟩
  | .inc c, st => ⟨Function.update st.val c ((st.val c + 1) % 2 ^ W), st.acc⟩
  | .emit a b, st => ⟨st.val, (tblPairs A w (st.val a) (st.val b)).reverse ++ st.acc⟩

/-- The register file of a state: `W`-bit numerals for the variables, the lists `wl`, `nl` on
`wr`, `wn`, the emitted symbols on `acc`, empty scratch registers. -/
def tblRho {n A : ℕ} (W : ℕ) (wl nl : List (Fin (A + 4))) (st : TblSt n A) :
    TblR n → List (Fin (A + 4))
  | .v i => binSyms W (st.val i)
  | .wr => wl
  | .wn => nl
  | .acc => st.acc
  | .z _ => []

@[simp] lemma tblRho_v {n A : ℕ} (W : ℕ) (wl nl : List (Fin (A + 4))) (st : TblSt n A) (i : Fin n) :
    tblRho W wl nl st (.v i) = binSyms W (st.val i) := rfl
@[simp] lemma tblRho_wr {n A : ℕ} (W : ℕ) (wl nl : List (Fin (A + 4))) (st : TblSt n A) :
    tblRho W wl nl st .wr = wl := rfl
@[simp] lemma tblRho_wn {n A : ℕ} (W : ℕ) (wl nl : List (Fin (A + 4))) (st : TblSt n A) :
    tblRho W wl nl st .wn = nl := rfl
@[simp] lemma tblRho_acc {n A : ℕ} (W : ℕ) (wl nl : List (Fin (A + 4))) (st : TblSt n A) :
    tblRho W wl nl st .acc = st.acc := rfl
@[simp] lemma tblRho_z {n A : ℕ} (W : ℕ) (wl nl : List (Fin (A + 4))) (st : TblSt n A) (j : Fin 12) :
    tblRho W wl nl st (.z j) = [] := rfl

/-! ### Instruction programs -/

section Progs

variable {T Q A : ℕ} {U : Type} {P : Type} {n : ℕ} (rg : TblR n → Fin T)

/-- Copy variable `a` into scratch register `z j`. -/
def tblLoad (a : Fin n) (j : Fin 12) : Pr P T Q A U :=
  bcopy (rg (.v a)) (rg (.z j)) (rg (.z 7)) (rg (.z 8))

/-- Clear the operand copies `z 0`, `z 1`. -/
def tblClr01 : Pr P T Q A U := .seq (bclear (rg (.z 0))) (bclear (rg (.z 1)))

/-- Store a numeral held in order on `z src` into variable `c`, through `z mid`. -/
def tblStoreF (src mid : Fin 12) (c : Fin n) : Pr P T Q A U :=
  .seq (bclear (rg (.v c)))
    (.seq (moveR (rg (.z src)) (rg (.z mid)) id) (moveR (rg (.z mid)) (rg (.v c)) id))

/-- Store a numeral held reversed on `z src` into variable `c`. -/
def tblStoreR (src : Fin 12) (c : Fin n) : Pr P T Q A U :=
  .seq (bclear (rg (.v c))) (moveR (rg (.z src)) (rg (.v c)) id)

/-- The test slot: scan slot of `z 10`. -/
def tblTst (v : HS T Q A U) : Bool := symBit (v.scan (rg (.z 10)))

/-- The quotient or remainder of `z 0` by `z 1` into `z 2`; `0` and `z 0` for a zero divisor. -/
def tblDivCore (isMod : Bool) : Pr P T Q A U :=
  .seq (bzero (rg .wr) (rg (.z 3)) (rg (.z 7)))
    (.seq (beq (rg (.z 1)) (rg (.z 3)) (rg (.z 7)) (rg (.z 8)) (rg (.z 9)) (rg (.z 10)))
      (.seq (bclear (rg (.z 3)))
        (.cond (tblTst rg)
          (if isMod then bcopy (rg (.z 0)) (rg (.z 2)) (rg (.z 7)) (rg (.z 8))
            else bzero (rg .wr) (rg (.z 2)) (rg (.z 7)))
          (if isMod then
            .seq (bdivmod (rg (.z 0)) (rg (.z 1)) (rg (.z 3)) (rg (.z 2)) (rg (.z 4)) (rg (.z 5))
              (rg (.z 6)) (rg (.z 7)) (rg (.z 8)) (rg (.z 9)) (rg (.z 10))) (bclear (rg (.z 3)))
          else
            .seq (bdivmod (rg (.z 0)) (rg (.z 1)) (rg (.z 2)) (rg (.z 3)) (rg (.z 4)) (rg (.z 5))
              (rg (.z 6)) (rg (.z 7)) (rg (.z 8)) (rg (.z 9)) (rg (.z 10))) (bclear (rg (.z 3)))))))

/-- One emission step: pop a bit of `z 0` and of `z 1` and push their pair symbol onto `acc`. -/
def tblEmitStep : Act T Q A U :=
  .pop (.rt (rg (.z 0))) (fun v o => { v with scan := Function.update v.scan (rg (.z 10)) (o.getD blank) })
    (.pop (.rt (rg (.z 1))) (fun v o => { v with scan := Function.update v.scan (rg (.z 11)) (o.getD blank) })
      (.push (.rt (rg .acc))
        (fun v => pairSym A (symBit (v.scan (rg (.z 10)))) (symBit (v.scan (rg (.z 11))))) .done))

/-- The host program of an instruction. -/
def tblInsProg : TblIns n → Pr P T Q A U
  | .add a b c => .seq (tblLoad rg a 0) (.seq (tblLoad rg b 1)
      (.seq (badd (rg (.z 0)) (rg (.z 1)) (rg (.z 2)) (rg (.z 7)) (rg (.z 8)) (rg (.z 9)) (rg (.z 10)))
        (.seq (tblClr01 rg) (tblStoreF rg 2 3 c))))
  | .sub a b c => .seq (tblLoad rg a 0) (.seq (tblLoad rg b 1)
      (.seq (bsub (rg (.z 0)) (rg (.z 1)) (rg (.z 2)) (rg (.z 7)) (rg (.z 8)) (rg (.z 9)) (rg (.z 10)))
        (.seq (tblClr01 rg) (tblStoreF rg 2 3 c))))
  | .mul a b c => .seq (tblLoad rg a 0) (.seq (tblLoad rg b 1)
      (.seq (bmul (rg (.z 0)) (rg (.z 1)) (rg (.z 2)) (rg (.z 4)) (rg (.z 6)) (rg (.z 7)) (rg (.z 8))
          (rg (.z 9)) (rg (.z 10)))
        (.seq (scanP (rg .wr) (rg (.z 6)) (.act (popPush (rg (.z 2)) (rg (.z 3)))))
          (.seq (bclear (rg (.z 2))) (.seq (tblClr01 rg) (tblStoreR rg 3 c))))))
  | .div a b c => .seq (tblLoad rg a 0) (.seq (tblLoad rg b 1)
      (.seq (tblDivCore rg false) (.seq (tblClr01 rg) (tblStoreF rg 2 3 c))))
  | .mod a b c => .seq (tblLoad rg a 0) (.seq (tblLoad rg b 1)
      (.seq (tblDivCore rg true) (.seq (tblClr01 rg) (tblStoreF rg 2 3 c))))
  | .copy a c => .seq (tblLoad rg a 2) (tblStoreF rg 2 3 c)
  | .zero c => .seq (bzero (rg .wr) (rg (.z 2)) (rg (.z 7))) (tblStoreF rg 2 3 c)
  | .inc c => .seq (tblLoad rg c 0) (.seq (countIter (rg (.z 0)) (rg (.z 7)) (rg (.z 10)))
      (tblStoreF rg 0 3 c))
  | .emit a b => .seq (tblLoad rg a 0) (.seq (tblLoad rg b 1)
      (.seq (scanP (rg .wn) (rg (.z 6)) (.act (tblEmitStep rg))) (tblClr01 rg)))

/-- The comparison `a < b` into the test slot. -/
def tblTest (a b : Fin n) : Pr P T Q A U :=
  .seq (tblLoad rg a 0) (.seq (tblLoad rg b 1)
    (.seq (blt (rg (.z 0)) (rg (.z 1)) (rg (.z 7)) (rg (.z 8)) (rg (.z 9)) (rg (.z 10)))
      (tblClr01 rg)))

end Progs

section Machines

lemma tbl_take_binSyms {A : ℕ} (W e x : ℕ) :
    ((binSyms (W + e) x : List (Fin (A + 4)))).take W = binSyms W x := by
  rw [binSyms_append, List.take_left' (by simp)]

/-- Close a register-file equation after an instruction writing variable `c`. -/
macro "tbl_fin " c:term:max h:term:max : tactic => `(tactic| (
  funext r
  rcases r with i | _ | _ | _ | j
  · by_cases hi : i = $c
    · subst hi; simp [TblIns.run, binSyms_mod, tbl_take_binSyms, $h:term]
    · simp [TblIns.run, hi]
  · simp
  · simp
  · simp [TblIns.run]
  · fin_cases j <;> simp))

variable {T Q A : ℕ} {U : Type} {P : Type} {body : P → Pr P T Q A U} {n : ℕ}
  {rg : TblR n → Fin T} (hrg : Function.Injective rg)
include hrg

/-- A counted transfer: `|cnt|` symbols move from `src` onto `dst` (reversed). -/
theorem tbl_xfer_runs {cnt t src dst : TblR n} (hd : [cnt, t, src, dst].Nodup)
    (ρ : TblR n → List (Fin (A + 4))) (ht : ρ t = []) (hN : (ρ cnt).length ≤ (ρ src).length) :
    tblRuns body rg (scanP (rg cnt) (rg t) (.act (popPush (rg src) (rg dst)))) ρ
      (Function.update (Function.update ρ src ((ρ src).drop (ρ cnt).length)) dst
        (((ρ src).take (ρ cnt).length).reverse ++ ρ dst)) (6 * (ρ cnt).length + 4) := by
  have hd' := tbl_nodup hrg hd
  simp only [List.map_cons, List.map_nil] at hd'
  regs_ne hd'
  intro v S hS
  set l := ρ src with hl
  set N := (ρ cnt).length with hNd
  let Ψ : ℕ → Regs T A := fun j => Function.update (Function.update S.R (rg src) (l.drop j))
    (rg dst) ((l.take j).reverse ++ ρ dst)
  have hp : IterSpec body (.act (popPush (rg src) (rg dst))) (rg cnt) (rg t) Ψ (fun _ => 1) N := by
    intro j hj w S' hS'
    have hsrc : S'.R (rg src) = l[j]'(by omega) :: l.drop (j + 1) := by
      rw [hS' _ ‹rg cnt ≠ rg src›.symm ‹rg t ≠ rg src›.symm]
      simp only [Ψ, Function.update_of_ne ‹rg src ≠ rg dst›, Function.update_self]
      exact List.drop_eq_getElem_cons (show j < l.length by omega)
    have hdst : S'.R (rg dst) = (l.take j).reverse ++ ρ dst := by
      rw [hS' _ ‹rg cnt ≠ rg dst›.symm ‹rg t ≠ rg dst›.symm]
      simp [Ψ]
    refine ⟨{ w with sym := some (l[j]'(by omega)) }, Function.update (Function.update S'.R (rg src) (l.drop (j + 1))) (rg dst)
      (l[j]'(by omega) :: S'.R (rg dst)), 1, rfl, le_rfl, ?_, ?_, ?_, ?_⟩
    · have := Exec.act (body := body) (popPush (rg src) (rg dst)) (mk w S')
      simp only [popPush, Action.run, mk_var, mk_stk, get_rt, hsrc, List.head?_cons,
        List.tail_cons, Option.getD_some, update_rt, store_mk] at this
      rw [Function.update_of_ne ‹rg src ≠ rg dst›.symm] at this
      exact this
    · simp [Function.update_of_ne ‹rg cnt ≠ rg src›, Function.update_of_ne ‹rg cnt ≠ rg dst›]
    · simp [Function.update_of_ne ‹rg t ≠ rg src›, Function.update_of_ne ‹rg t ≠ rg dst›]
    · intro k hk1 hk2
      by_cases hk3 : k = rg dst
      · subst hk3
        have e : (List.take (j + 1) l).reverse = l[j]'(by omega) :: (List.take j l).reverse := by
          rw [List.take_succ_eq_append_getElem (show j < l.length by omega)]; simp
        simp only [Ψ, Function.update_self, hdst, e, List.cons_append]
      by_cases hk4 : k = rg src
      · subst hk4
        simp [Ψ, Function.update_of_ne hk3]
      simp [Ψ, Function.update_of_ne hk3, Function.update_of_ne hk4, hS' k hk1 hk2]
  have hlen : (S.R (rg cnt)).length = N := by rw [hS]
  obtain ⟨v', R', m, hu, hm, he, hcnt, ht', hΨ⟩ := scanP_exec body ‹rg cnt ≠ rg t› hp 0 v S
    (by rw [hlen]; omega) (fun k h1 h2 => by
      simp only [Ψ, List.drop_zero, List.take_zero, List.reverse_nil, List.nil_append, hl,
        ← hS src, ← hS dst, Function.update_eq_self])
  have hSt : S.R (rg t) = [] := by rw [hS, ht]
  refine ⟨v', _, m, hu, ?_, he, ?_, ⟨rfl, rfl, rfl, fun k hk => ?_⟩⟩
  · simp only [hlen, hSt, Finset.sum_const, Finset.card_range, smul_eq_mul, List.length_nil] at hm
    omega
  · have hcs : cnt ≠ src := by rintro rfl; simp at hd
    have hcd : cnt ≠ dst := by rintro rfl; simp at hd
    have hts : t ≠ src := by rintro rfl; simp at hd
    have htd : t ≠ dst := by rintro rfl; simp at hd
    intro r
    dsimp only
    by_cases h1 : r = cnt
    · subst h1
      rw [hcnt, hSt, Function.update_of_ne hcd, Function.update_of_ne hcs, hS]
      simp
    by_cases h2 : r = t
    · subst h2
      rw [ht', Function.update_of_ne htd, Function.update_of_ne hts, ht]
    rw [hΨ _ (hrg.ne h1) (hrg.ne h2), Nat.zero_add, hlen]
    simp only [Ψ]
    rw [tbl_holds_upd hrg (tbl_holds_upd hrg hS src _) dst]
  · dsimp only
    rw [hΨ k (fun h => (hk cnt) h.symm) (fun h => (hk t) h.symm)]
    simp [Ψ, tbl_upd_off _ _ _ hk]

omit hrg in
@[simp] lemma length_tblPairs (A N x y : ℕ) : (tblPairs A N x y).length = N := by
  simp [tblPairs]

omit hrg in
lemma tbl_pairs_getElem (A N x y j : ℕ) (hj : j < N) :
    (tblPairs A N x y)[j]'(by simp; omega) = pairSym A (x.testBit j) (y.testBit j) := by
  simp [tblPairs, coeffSyms, ZMod.val_natCast, Nat.testBit_mod_two_pow]

omit hrg in
lemma tbl_drop_binSyms (W x j : ℕ) (hj : j < W) :
    ((binSyms W x : List (Fin (A + 4)))).drop j = bitSymbol (x.testBit j) :: (binSyms W x).drop (j + 1) := by
  rw [List.drop_eq_getElem_cons (by simp; omega), getElem_binSyms]

/-- The emission loop: one pair symbol per symbol of `wn`. -/
theorem tbl_emitScan_runs {W x y : ℕ} (ρ : TblR n → List (Fin (A + 4)))
    (hx : ρ (.z 0) = binSyms W x) (hy : ρ (.z 1) = binSyms W y) (h6 : ρ (.z 6) = [])
    (hw : (ρ .wn).length ≤ W) :
    tblRuns body rg (scanP (rg .wn) (rg (.z 6)) (.act (tblEmitStep rg))) ρ
      (Function.update (Function.update (Function.update ρ (.z 0) ((binSyms W x).drop (ρ .wn).length))
        (.z 1) ((binSyms W y).drop (ρ .wn).length)) .acc
        ((tblPairs A (ρ .wn).length x y).reverse ++ ρ .acc)) (6 * (ρ .wn).length + 4) := by
  have hd' := tbl_nodup hrg (l := [.wn, .z 6, .z 0, .z 1, .acc]) (by simp)
  simp only [List.map_cons, List.map_nil] at hd'
  regs_ne hd'
  have h1011 : rg (.z 10) ≠ rg (.z 11) := hrg.ne (by simp)
  intro v S hS
  set N := (ρ .wn).length with hNd
  set lx : List (Fin (A + 4)) := binSyms W x
  set ly : List (Fin (A + 4)) := binSyms W y
  set pr := tblPairs A N x y
  let Ψ : ℕ → Regs T A := fun j => Function.update (Function.update (Function.update S.R
    (rg (.z 0)) (lx.drop j)) (rg (.z 1)) (ly.drop j)) (rg .acc) ((pr.take j).reverse ++ ρ .acc)
  have hp : IterSpec body (.act (tblEmitStep rg)) (rg .wn) (rg (.z 6)) Ψ (fun _ => 1) N := by
    intro j hj w S' hS'
    have hjW : j < W := by omega
    have h0 : S'.R (rg (.z 0)) = bitSymbol (x.testBit j) :: lx.drop (j + 1) := by
      rw [hS' _ ‹rg .wn ≠ rg (.z 0)›.symm ‹rg (.z 6) ≠ rg (.z 0)›.symm]
      simp only [Ψ, Function.update_of_ne ‹rg (.z 0) ≠ rg .acc›, Function.update_of_ne ‹rg (.z 0) ≠ rg (.z 1)›,
        Function.update_self]
      exact tbl_drop_binSyms W x j hjW
    have h1 : S'.R (rg (.z 1)) = bitSymbol (y.testBit j) :: ly.drop (j + 1) := by
      rw [hS' _ ‹rg .wn ≠ rg (.z 1)›.symm ‹rg (.z 6) ≠ rg (.z 1)›.symm]
      simp only [Ψ, Function.update_of_ne ‹rg (.z 1) ≠ rg .acc›, Function.update_self]
      exact tbl_drop_binSyms W y j hjW
    have hac : S'.R (rg .acc) = (pr.take j).reverse ++ ρ .acc := by
      rw [hS' _ ‹rg .wn ≠ rg .acc›.symm ‹rg (.z 6) ≠ rg .acc›.symm]
      simp [Ψ]
    refine ⟨{ w with scan := Function.update (Function.update w.scan (rg (.z 10))
        (bitSymbol (x.testBit j))) (rg (.z 11)) (bitSymbol (y.testBit j)) },
      Function.update (Function.update (Function.update S'.R (rg (.z 0)) (lx.drop (j + 1)))
        (rg (.z 1)) (ly.drop (j + 1))) (rg .acc)
        (pairSym A (x.testBit j) (y.testBit j) :: S'.R (rg .acc)), 1, rfl, le_rfl, ?_, ?_, ?_, ?_⟩
    · have := Exec.act (body := body) (tblEmitStep rg) (mk w S')
      simp only [tblEmitStep, Action.run, mk_var, mk_stk, get_rt, h0, List.head?_cons,
        List.tail_cons, Option.getD_some, update_rt, store_mk] at this
      rw [Function.update_of_ne ‹rg (.z 0) ≠ rg (.z 1)›.symm, h1] at this
      simp only [List.head?_cons, List.tail_cons, Option.getD_some, 
        Function.update_self, Function.update_of_ne h1011, symBit_bitSymbol] at this
      rw [Function.update_of_ne ‹rg (.z 1) ≠ rg .acc›.symm,
        Function.update_of_ne ‹rg (.z 0) ≠ rg .acc›.symm] at this
      exact this
    · simp [Function.update_of_ne ‹rg .wn ≠ rg (.z 0)›, Function.update_of_ne ‹rg .wn ≠ rg (.z 1)›,
        Function.update_of_ne ‹rg .wn ≠ rg .acc›]
    · simp [Function.update_of_ne ‹rg (.z 6) ≠ rg (.z 0)›, Function.update_of_ne ‹rg (.z 6) ≠ rg (.z 1)›,
        Function.update_of_ne ‹rg (.z 6) ≠ rg .acc›]
    · intro k hk1 hk2
      by_cases hk3 : k = rg .acc
      · subst hk3
        have e : (pr.take (j + 1)).reverse =
            pairSym A (x.testBit j) (y.testBit j) :: (pr.take j).reverse := by
          rw [List.take_succ_eq_append_getElem (show j < pr.length by simp [pr]; omega),
            tbl_pairs_getElem A N x y j hj]
          simp
        simp only [Ψ, Function.update_self, hac, e, List.cons_append]
      by_cases hk4 : k = rg (.z 1)
      · subst hk4
        simp [Ψ, Function.update_of_ne hk3]
      by_cases hk5 : k = rg (.z 0)
      · subst hk5
        simp [Ψ, Function.update_of_ne hk3, Function.update_of_ne hk4]
      simp [Ψ, Function.update_of_ne hk3, Function.update_of_ne hk4, Function.update_of_ne hk5,
        hS' k hk1 hk2]
  have hlen : (S.R (rg .wn)).length = N := by rw [hS]
  obtain ⟨v', R', m, hu, hm, he, hcnt, ht', hΨ⟩ := scanP_exec body ‹rg .wn ≠ rg (.z 6)› hp 0 v S
    (by rw [hlen]; omega) (fun k h1 h2 => by
      simp only [Ψ, List.drop_zero, List.take_zero, List.reverse_nil, List.nil_append, ← hx, ← hy,
        ← hS (.z 0), ← hS (.z 1), ← hS .acc, Function.update_eq_self])
  have hSt : S.R (rg (.z 6)) = [] := by rw [hS, h6]
  refine ⟨v', _, m, hu, ?_, he, ?_, ⟨rfl, rfl, rfl, fun k hk => ?_⟩⟩
  · simp only [hlen, hSt, Finset.sum_const, Finset.card_range, smul_eq_mul, List.length_nil] at hm
    omega
  · intro r
    dsimp only
    by_cases h1 : r = .wn
    · subst h1
      rw [hcnt, hSt, hS]
      simp
    by_cases h2 : r = .z 6
    · subst h2
      rw [ht']
      simp [h6]
    rw [hΨ _ (hrg.ne h1) (hrg.ne h2), Nat.zero_add, hlen]
    simp only [Ψ]
    rw [tbl_holds_upd hrg (tbl_holds_upd hrg (tbl_holds_upd hrg hS (.z 0) _) (.z 1) _) .acc,
      List.take_of_length_le (by simp [pr])]
  · dsimp only
    rw [hΨ k (fun h => (hk .wn) h.symm) (fun h => (hk (.z 6)) h.symm)]
    simp [Ψ, tbl_upd_off _ _ _ hk]

omit hrg in
/-- A conditional on the test slot, from contracts of both branches. -/
theorem tbl_cond_runs {pt pf : Pr P T Q A U} {ρ ρ' : TblR n → List (Fin (A + 4))} {c : ℕ}
    {b : Bool} (ht : b = true → tblRuns body rg pt ρ ρ' c)
    (hf : b = false → tblRuns body rg pf ρ ρ' c) (v : HS T Q A U) (S : Stacks T A)
    (hv : tblTst rg v = b) (hS : tblHolds rg S ρ) :
    ∃ v' S' m, v'.user = v.user ∧ m ≤ c + 1 ∧
      Exec body (.cond (tblTst rg) pt pf) (mk v S) m (mk v' S') ∧ tblHolds rg S' ρ' ∧
      tblFr rg S S' := by
  cases b with
  | true =>
    obtain ⟨v', S', m, hu, hm, he, hS', hf'⟩ := ht rfl v S hS
    exact ⟨v', S', m + 1, hu, by omega, Exec.cond_true hv he, hS', hf'⟩
  | false =>
    obtain ⟨v', S', m, hu, hm, he, hS', hf'⟩ := hf rfl v S hS
    exact ⟨v', S', m + 1, hu, by omega, Exec.cond_false hv he, hS', hf'⟩

/-- The quotient or remainder core. -/
theorem tbl_divCore_runs (isMod : Bool) {W x y : ℕ} (ρ : TblR n → List (Fin (A + 4)))
    (hx : x < 2 ^ W) (hy : y < 2 ^ W) (h0 : ρ (.z 0) = binSyms W x) (h1 : ρ (.z 1) = binSyms W y)
    (hwr : (ρ .wr).length = W) (hz : ∀ j : Fin 12, 2 ≤ j.val → ρ (.z j) = []) :
    tblRuns body rg (tblDivCore rg isMod) ρ
      (Function.update ρ (.z 2) (binSyms W (if isMod then x % y else x / y)))
      (12 * W ^ 2 + 80 * W + 60) := by
  intro v S hS
  obtain ⟨v₁, S₁, m₁, hu₁, hm₁, he₁, hS₁, hf₁⟩ := tbl_bzero_runs (body := body) hrg (wR := .wr)
    (c := .z 3) (t := .z 7) (by simp) ρ (hz 7 (by decide)) v S hS
  have hg : ∀ j : Fin 12, 4 ≤ j.val → S₁.R (rg (.z j)) = [] := by
    intro j hj; rw [hS₁]; simp only [Function.update_apply, TblR.z.injEq]
    split_ifs with h
    · subst h; simp at hj
    · exact hz _ (by omega)
  have hb1 : S₁.R (rg (.z 1)) = binSyms W y := by rw [hS₁]; simp [h1]
  have hb3 : S₁.R (rg (.z 3)) = binSyms W 0 := by rw [hS₁]; simp [hwr, hz 3 (by decide)]
  obtain ⟨v₂, hu₂, hc₂, -, he₂⟩ := beq_exec body (a := rg (.z 1)) (b := rg (.z 3)) (tx := rg (.z 7))
    (ty := rg (.z 8)) (tz := rg (.z 9)) (cy := rg (.z 10))
    (tbl_nodup hrg (l := [.z 1, .z 3, .z 7, .z 8, .z 9]) (by simp)) (hrg.ne (by simp))
    (hrg.ne (by simp)) hy (Nat.two_pow_pos W) v₁ S₁ hb1 hb3 (hg 7 (by decide)) (hg 8 (by decide))
    (hg 9 (by decide))
  obtain ⟨v₃, hu₃, hsc₃, he₃⟩ := bclear_exec body (rg (.z 3)) v₂ S₁
  have hS₃ : tblHolds rg { S₁ with R := Function.update S₁.R (rg (.z 3)) [] } ρ := by
    intro r
    dsimp only
    rw [tbl_holds_upd hrg hS₁]
    by_cases hr : r = .z 3
    · subst hr; simp [hz 3 (by decide)]
    · simp [Function.update_of_ne hr]
  have htst : tblTst rg v₃ = decide (y = 0) := by simp [tblTst, hsc₃, hc₂]
  have h7 : ρ (.z 7) = [] := hz 7 (by decide)
  have h8 : ρ (.z 8) = [] := hz 8 (by decide)
  have hbr : tblRuns body rg
      (if isMod then bcopy (rg (.z 0)) (rg (.z 2)) (rg (.z 7)) (rg (.z 8))
        else bzero (rg .wr) (rg (.z 2)) (rg (.z 7))) ρ
      (Function.update ρ (.z 2) (binSyms W (if isMod then x % y else x / y))) (6 * W + 6) ∨ y ≠ 0 := by
    by_cases hy0 : y = 0
    · left
      subst hy0
      cases isMod
      · refine ((tbl_bzero_runs hrg (wR := .wr) (c := .z 2) (t := .z 7) (by simp) ρ h7).congr ?_).mono ?_
        · simp [hwr, hz 2 (by decide)]
        · omega
      · refine ((tbl_bcopy_runs hrg (a := .z 0) (c := .z 2) (t₁ := .z 7) (t₂ := .z 8) (by simp) ρ h7
          h8).congr ?_).mono ?_
        · simp [h0, hz 2 (by decide)]
        · simp [h0]
    · exact Or.inr hy0
  have hbr' : y ≠ 0 → tblRuns body rg
      (if isMod then
        .seq (bdivmod (rg (.z 0)) (rg (.z 1)) (rg (.z 3)) (rg (.z 2)) (rg (.z 4)) (rg (.z 5))
          (rg (.z 6)) (rg (.z 7)) (rg (.z 8)) (rg (.z 9)) (rg (.z 10))) (bclear (rg (.z 3)))
      else
        .seq (bdivmod (rg (.z 0)) (rg (.z 1)) (rg (.z 2)) (rg (.z 3)) (rg (.z 4)) (rg (.z 5))
          (rg (.z 6)) (rg (.z 7)) (rg (.z 8)) (rg (.z 9)) (rg (.z 10))) (bclear (rg (.z 3)))) ρ
      (Function.update ρ (.z 2) (binSyms W (if isMod then x % y else x / y)))
      (12 * W ^ 2 + 60 * W + 40) := by
    intro hy0
    have hy0' : 0 < y := Nat.pos_of_ne_zero hy0
    cases isMod
    · refine (((tbl_bdivmod_runs hrg (a := .z 0) (b := .z 1) (q := .z 2) (r := .z 3) (bw := .z 4)
        (rr := .z 5) (t := .z 6) (tx := .z 7) (ty := .z 8) (tz := .z 9) (cy := .z 10) (by simp)
        (by simp) (by simp) hx hy hy0' ρ h0 h1 (hz 4 (by decide)) (hz 5 (by decide))
        (hz 6 (by decide)) h7 h8 (hz 9 (by decide))).seq (tbl_bclear_runs hrg (.z 3) _)).congr ?_).mono ?_
      · funext r
        by_cases h2 : r = .z 2
        · subst h2; simp [hz 2 (by decide)]
        by_cases h3 : r = .z 3
        · subst h3; simp [hz 3 (by decide)]
        simp [Function.update_of_ne h2, Function.update_of_ne h3]
      · simp [hz 3 (by decide)]; nlinarith
    · refine (((tbl_bdivmod_runs hrg (a := .z 0) (b := .z 1) (q := .z 3) (r := .z 2) (bw := .z 4)
        (rr := .z 5) (t := .z 6) (tx := .z 7) (ty := .z 8) (tz := .z 9) (cy := .z 10) (by simp)
        (by simp) (by simp) hx hy hy0' ρ h0 h1 (hz 4 (by decide)) (hz 5 (by decide))
        (hz 6 (by decide)) h7 h8 (hz 9 (by decide))).seq (tbl_bclear_runs hrg (.z 3) _)).congr ?_).mono ?_
      · funext r
        by_cases h2 : r = .z 2
        · subst h2; simp [hz 2 (by decide)]
        by_cases h3 : r = .z 3
        · subst h3; simp [hz 3 (by decide)]
        simp [Function.update_of_ne h2, Function.update_of_ne h3]
      · simp [hz 3 (by decide)]; nlinarith
  obtain ⟨v₄, S₄, m₄, hu₄, hm₄, he₄, hS₄, hf₄⟩ := tbl_cond_runs (b := decide (y = 0))
    (pt := if isMod then bcopy (rg (.z 0)) (rg (.z 2)) (rg (.z 7)) (rg (.z 8))
        else bzero (rg .wr) (rg (.z 2)) (rg (.z 7)))
    (fun h => by
      rcases hbr with h' | h'
      · exact h'.mono (by nlinarith)
      · exact absurd (of_decide_eq_true h) h')
    (fun h => hbr' (of_decide_eq_false h)) v₃ _ htst hS₃
  have hf₃ : tblFr rg S₁ { S₁ with R := Function.update S₁.R (rg (.z 3)) [] } :=
    ⟨rfl, rfl, rfl, fun k hk => tbl_upd_off _ _ _ hk⟩
  refine ⟨v₄, S₄, m₁ + ((8 * W + 8) + ((2 * (S₁.R (rg (.z 3))).length + 2) + m₄)),
    by rw [hu₄, hu₃, hu₂, hu₁], ?_, Exec.seq he₁ (Exec.seq he₂ (Exec.seq he₃ he₄)), hS₄,
    hf₁.trans (hf₃.trans hf₄)⟩
  simp only [hwr, hb3, length_binSyms] at hm₁ ⊢
  nlinarith

section Ins

variable {W w : ℕ} (wl nl : List (Fin (A + 4))) (st : TblSt n A)
  (hwl : wl.length = W) (hnl : nl.length = w) (hst : ∀ i, st.val i < 2 ^ W)
include hwl hst

omit hwl in
theorem tbl_add_runs (a b c : Fin n) :
    tblRuns body rg (tblInsProg rg (.add a b c)) (tblRho W wl nl st)
      (tblRho W wl nl ((TblIns.add a b c).run A W w st)) (30 * W + 30) := by
  have h := (tbl_bcopy_runs (body := body) hrg (a := .v a) (c := .z 0) (t₁ := .z 7) (t₂ := .z 8)
    (by simp) (tblRho W wl nl st) (by simp) (by simp)).seq
    ((tbl_bcopy_runs hrg (a := .v b) (c := .z 1) (t₁ := .z 7) (t₂ := .z 8)
    (by simp) _ (by simp) (by simp)).seq
    ((tbl_badd_runs hrg (a := .z 0) (b := .z 1) (c := .z 2) (tx := .z 7) (ty := .z 8) (tz := .z 9)
      (cy := .z 10) (by simp) (by simp) (by simp) (hst a) (hst b) _ (by simp) (by simp)
      (by simp) (by simp) (by simp)).seq
    (((tbl_bclear_runs hrg (.z 0) _).seq (tbl_bclear_runs hrg (.z 1) _)).seq
    ((tbl_bclear_runs hrg (.v c) _).seq ((tbl_moveR_runs hrg (a := .z 2) (b := .z 3) (by simp) _).seq
      (tbl_moveR_runs hrg (a := .z 3) (b := .v c) (by simp) _))))))
  refine (h.congr ?_).mono ?_
  · clear h; tbl_fin c Nat.add_zero
  · clear h; simp; omega

omit hwl in
theorem tbl_sub_runs (a b c : Fin n) :
    tblRuns body rg (tblInsProg rg (.sub a b c)) (tblRho W wl nl st)
      (tblRho W wl nl ((TblIns.sub a b c).run A W w st)) (30 * W + 30) := by
  have h := (tbl_bcopy_runs (body := body) hrg (a := .v a) (c := .z 0) (t₁ := .z 7) (t₂ := .z 8)
    (by simp) (tblRho W wl nl st) (by simp) (by simp)).seq
    ((tbl_bcopy_runs hrg (a := .v b) (c := .z 1) (t₁ := .z 7) (t₂ := .z 8)
    (by simp) _ (by simp) (by simp)).seq
    ((tbl_bsub_runs hrg (a := .z 0) (b := .z 1) (c := .z 2) (tx := .z 7) (ty := .z 8) (tz := .z 9)
      (cy := .z 10) (by simp) (by simp) (by simp) (hst a) (hst b) _ (by simp) (by simp)
      (by simp) (by simp) (by simp)).seq
    (((tbl_bclear_runs hrg (.z 0) _).seq (tbl_bclear_runs hrg (.z 1) _)).seq
    ((tbl_bclear_runs hrg (.v c) _).seq ((tbl_moveR_runs hrg (a := .z 2) (b := .z 3) (by simp) _).seq
      (tbl_moveR_runs hrg (a := .z 3) (b := .v c) (by simp) _))))))
  refine (h.congr ?_).mono ?_
  · clear h; tbl_fin c Nat.add_zero
  · clear h; simp; omega

omit hwl hst in
theorem tbl_copy_runs (a c : Fin n) :
    tblRuns body rg (tblInsProg rg (.copy a c)) (tblRho W wl nl st)
      (tblRho W wl nl ((TblIns.copy a c).run A W w st)) (12 * W + 12) := by
  have h := (tbl_bcopy_runs (body := body) hrg (a := .v a) (c := .z 2) (t₁ := .z 7) (t₂ := .z 8)
    (by simp) (tblRho W wl nl st) (by simp) (by simp)).seq
    ((tbl_bclear_runs hrg (.v c) _).seq ((tbl_moveR_runs hrg (a := .z 2) (b := .z 3) (by simp) _).seq
      (tbl_moveR_runs hrg (a := .z 3) (b := .v c) (by simp) _)))
  refine (h.congr ?_).mono ?_
  · clear h; tbl_fin c Nat.add_zero
  · clear h; simp; omega

omit hst in
theorem tbl_zero_runs (c : Fin n) :
    tblRuns body rg (tblInsProg rg (.zero c)) (tblRho W wl nl st)
      (tblRho W wl nl ((TblIns.zero c).run A W w st)) (12 * W + 12) := by
  have h := (tbl_bzero_runs (body := body) hrg (wR := .wr) (c := .z 2) (t := .z 7)
    (by simp) (tblRho W wl nl st) (by simp)).seq
    ((tbl_bclear_runs hrg (.v c) _).seq ((tbl_moveR_runs hrg (a := .z 2) (b := .z 3) (by simp) _).seq
      (tbl_moveR_runs hrg (a := .z 3) (b := .v c) (by simp) _)))
  refine (h.congr ?_).mono ?_
  · clear h; tbl_fin c hwl
  · clear h; simp; omega

omit hwl hst in
theorem tbl_inc_runs (c : Fin n) :
    tblRuns body rg (tblInsProg rg (.inc c)) (tblRho W wl nl st)
      (tblRho W wl nl ((TblIns.inc c).run A W w st)) (16 * W + 20) := by
  have h := (tbl_bcopy_runs (body := body) hrg (a := .v c) (c := .z 0) (t₁ := .z 7) (t₂ := .z 8)
    (by simp) (tblRho W wl nl st) (by simp) (by simp)).seq
    ((tbl_countIter_runs hrg (c := .z 0) (tmp := .z 7) (by simp) (.z 10) (W := W) (j := st.val c) _
      (by simp) (by simp)).seq
    ((tbl_bclear_runs hrg (.v c) _).seq ((tbl_moveR_runs hrg (a := .z 0) (b := .z 3) (by simp) _).seq
      (tbl_moveR_runs hrg (a := .z 3) (b := .v c) (by simp) _))))
  refine (h.congr ?_).mono ?_
  · clear h; tbl_fin c Nat.add_zero
  · clear h; simp; omega

theorem tbl_mul_runs (a b c : Fin n) :
    tblRuns body rg (tblInsProg rg (.mul a b c)) (tblRho W wl nl st)
      (tblRho W wl nl ((TblIns.mul a b c).run A W w st)) (24 * W ^ 2 + 100 * W + 100) := by
  have h := (tbl_bcopy_runs (body := body) hrg (a := .v a) (c := .z 0) (t₁ := .z 7) (t₂ := .z 8)
    (by simp) (tblRho W wl nl st) (by simp) (by simp)).seq
    ((tbl_bcopy_runs hrg (a := .v b) (c := .z 1) (t₁ := .z 7) (t₂ := .z 8)
    (by simp) _ (by simp) (by simp)).seq
    ((tbl_bmul_runs hrg (a := .z 0) (b := .z 1) (c := .z 2) (s := .z 4) (t := .z 6) (tx := .z 7)
      (ty := .z 8) (tz := .z 9) (cy := .z 10) (by simp) (by simp) (by simp) (hst a) (hst b) _
      (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)).seq
    ((tbl_xfer_runs hrg (cnt := .wr) (t := .z 6) (src := .z 2) (dst := .z 3) (by simp) _ (by simp)
      (by simp [hwl])).seq
    ((tbl_bclear_runs hrg (.z 2) _).seq
    (((tbl_bclear_runs hrg (.z 0) _).seq (tbl_bclear_runs hrg (.z 1) _)).seq
    ((tbl_bclear_runs hrg (.v c) _).seq (tbl_moveR_runs hrg (a := .z 3) (b := .v c) (by simp) _)))))))
  refine (h.congr ?_).mono ?_
  · clear h; tbl_fin c hwl
  · clear h; simp [hwl]; nlinarith

omit hwl hst in
theorem tbl_emit_runs (hnl : nl.length = w) (hw : w ≤ W) (a b : Fin n) :
    tblRuns body rg (tblInsProg rg (.emit a b)) (tblRho W wl nl st)
      (tblRho W wl nl ((TblIns.emit a b).run A W w st)) (16 * W + 6 * w + 30) := by
  have h := (tbl_bcopy_runs (body := body) hrg (a := .v a) (c := .z 0) (t₁ := .z 7) (t₂ := .z 8)
    (by simp) (tblRho W wl nl st) (by simp) (by simp)).seq
    ((tbl_bcopy_runs hrg (a := .v b) (c := .z 1) (t₁ := .z 7) (t₂ := .z 8)
    (by simp) _ (by simp) (by simp)).seq
    ((tbl_emitScan_runs hrg (W := W) (x := st.val a) (y := st.val b) _ (by simp) (by simp) (by simp)
      (by simp [hnl, hw])).seq
    ((tbl_bclear_runs hrg (.z 0) _).seq (tbl_bclear_runs hrg (.z 1) _))))
  refine (h.congr ?_).mono ?_
  · clear h
    funext r
    rcases r with i | _ | _ | _ | j
    · simp [TblIns.run]
    · simp
    · simp
    · simp [TblIns.run, hnl]
    · fin_cases j <;> simp
  · clear h; simp [hnl]; omega

theorem tbl_divmod_runs (isMod : Bool) (a b c : Fin n) :
    tblRuns body rg (if isMod then tblInsProg rg (.mod a b c) else tblInsProg rg (.div a b c))
      (tblRho W wl nl st)
      (tblRho W wl nl ((if isMod then TblIns.mod a b c else TblIns.div a b c).run A W w st))
      (12 * W ^ 2 + 110 * W + 90) := by
  have hd := tbl_divCore_runs (body := body) hrg isMod (W := W) (x := st.val a) (y := st.val b)
    (Function.update (Function.update (tblRho W wl nl st) (.z 0) (binSyms W (st.val a) ++ []))
      (.z 1) (binSyms W (st.val b) ++ [])) (hst a) (hst b) (by simp) (by simp) (by simp [hwl])
    (fun j hj => by fin_cases j <;> simp_all)
  have h := (tbl_bcopy_runs (body := body) hrg (a := .v a) (c := .z 0) (t₁ := .z 7) (t₂ := .z 8)
    (by simp) (tblRho W wl nl st) (by simp) (by simp)).seq
    ((tbl_bcopy_runs hrg (a := .v b) (c := .z 1) (t₁ := .z 7) (t₂ := .z 8)
    (by simp) _ (by simp) (by simp)).seq
    (hd.seq
    (((tbl_bclear_runs hrg (.z 0) _).seq (tbl_bclear_runs hrg (.z 1) _)).seq
    ((tbl_bclear_runs hrg (.v c) _).seq ((tbl_moveR_runs hrg (a := .z 2) (b := .z 3) (by simp) _).seq
      (tbl_moveR_runs hrg (a := .z 3) (b := .v c) (by simp) _))))))
  cases isMod
  · refine (h.congr ?_).mono ?_
    · clear h hd; tbl_fin c hwl
    · clear h hd; simp; nlinarith
  · refine (h.congr ?_).mono ?_
    · clear h hd; tbl_fin c hwl
    · clear h hd; simp; nlinarith

end Ins

omit hrg in
lemma tblFr.upd {S : Stacks T A} (a : TblR n) (l : List (Fin (A + 4))) :
    tblFr rg S { S with R := Function.update S.R (rg a) l } :=
  ⟨rfl, rfl, rfl, fun _ hk => tbl_upd_off _ _ _ hk⟩

/-- `tblTest`: the registers are unchanged and the test slot holds `a < b`. -/
theorem tbl_test_exec {W : ℕ} (wl nl : List (Fin (A + 4))) (st : TblSt n A)
    (hst : ∀ i, st.val i < 2 ^ W) (a b : Fin n) (v : HS T Q A U) (S : Stacks T A)
    (hS : tblHolds rg S (tblRho W wl nl st)) :
    ∃ v' S' m, v'.user = v.user ∧ tblTst rg v' = decide (st.val a < st.val b) ∧
      m ≤ 24 * W + 24 ∧ Exec body (tblTest rg a b) (mk v S) m (mk v' S') ∧
      tblHolds rg S' (tblRho W wl nl st) ∧ tblFr rg S S' := by
  obtain ⟨v₁, S₁, m₁, hu₁, hm₁, he₁, hS₁, hf₁⟩ := tbl_bcopy_runs (body := body) hrg (a := .v a)
    (c := .z 0) (t₁ := .z 7) (t₂ := .z 8) (by simp) (tblRho W wl nl st) (by simp) (by simp) v S hS
  obtain ⟨v₂, S₂, m₂, hu₂, hm₂, he₂, hS₂, hf₂⟩ := tbl_bcopy_runs (body := body) hrg (a := .v b)
    (c := .z 1) (t₁ := .z 7) (t₂ := .z 8) (by simp) _ (by simp) (by simp) v₁ S₁ hS₁
  obtain ⟨v₃, hu₃, hc₃, -, he₃⟩ := blt_exec body (a := rg (.z 0)) (b := rg (.z 1)) (tx := rg (.z 7))
    (ty := rg (.z 8)) (tz := rg (.z 9)) (cy := rg (.z 10))
    (tbl_nodup hrg (l := [.z 0, .z 1, .z 7, .z 8, .z 9]) (by simp)) (hrg.ne (by simp))
    (hrg.ne (by simp)) (hst a) (hst b) v₂ S₂ (by rw [hS₂]; simp) (by rw [hS₂]; simp)
    (by rw [hS₂]; simp) (by rw [hS₂]; simp) (by rw [hS₂]; simp)
  obtain ⟨v₄, hu₄, hsc₄, he₄⟩ := bclear_exec body (rg (.z 0)) v₃ S₂
  obtain ⟨v₅, hu₅, hsc₅, he₅⟩ := bclear_exec body (rg (.z 1)) v₄
    { S₂ with R := Function.update S₂.R (rg (.z 0)) [] }
  refine ⟨v₅, _, _, by rw [hu₅, hu₄, hu₃, hu₂, hu₁], by simp [tblTst, hsc₅, hsc₄, hc₃], ?_,
    Exec.seq he₁ (Exec.seq he₂ (Exec.seq he₃ (Exec.seq he₄ he₅))), ?_,
    hf₁.trans (hf₂.trans ((tblFr.upd _ _).trans (tblFr.upd _ _)))⟩
  · dsimp only
    rw [Function.update_of_ne (hrg.ne (show (TblR.z 1 : TblR n) ≠ .z 0 by simp)), hS₂, hS₂]
    simp at hm₁ hm₂ ⊢
    omega
  · intro r
    dsimp only
    rw [tbl_holds_upd hrg (tbl_holds_upd hrg hS₂ (.z 0) []) (.z 1)]
    rcases r with i | _ | _ | _ | j
    · simp
    · simp
    · simp
    · simp
    · fin_cases j <;> simp



end Machines

section Code

/-! ### Programs and their semantics -/

/-- Structured programs over `n` variables. -/
inductive TblCode (n : ℕ) where
  | ins (i : TblIns n)
  | seq (c d : TblCode n)
  | ite (a b : Fin n) (c d : TblCode n)
  | loop (a b : Fin n) (c : TblCode n)

/-- Big-step semantics with an atom count: one per instruction and per test, two per loop
exit. -/
inductive TblBig {n : ℕ} (A W w : ℕ) : TblCode n → TblSt n A → TblSt n A → ℕ → Prop
  | ins (i : TblIns n) (st : TblSt n A) : TblBig A W w (.ins i) st (i.run A W w st) 1
  | seq {c d : TblCode n} {st₁ st₂ st₃ : TblSt n A} {k₁ k₂ : ℕ} :
      TblBig A W w c st₁ st₂ k₁ → TblBig A W w d st₂ st₃ k₂ →
      TblBig A W w (.seq c d) st₁ st₃ (k₁ + k₂)
  | iteT {a b : Fin n} {c d : TblCode n} {st st' : TblSt n A} {k : ℕ} :
      st.val a < st.val b → TblBig A W w c st st' k → TblBig A W w (.ite a b c d) st st' (k + 1)
  | iteF {a b : Fin n} {c d : TblCode n} {st st' : TblSt n A} {k : ℕ} :
      ¬ st.val a < st.val b → TblBig A W w d st st' k → TblBig A W w (.ite a b c d) st st' (k + 1)
  | loopF {a b : Fin n} {c : TblCode n} {st : TblSt n A} :
      ¬ st.val a < st.val b → TblBig A W w (.loop a b c) st st 2
  | loopT {a b : Fin n} {c : TblCode n} {st st₁ st₂ : TblSt n A} {k₁ k₂ : ℕ} :
      st.val a < st.val b → TblBig A W w c st st₁ k₁ → TblBig A W w (.loop a b c) st₁ st₂ k₂ →
      TblBig A W w (.loop a b c) st st₂ (k₁ + k₂ + 2)

theorem TblIns.run_lt {n A W w : ℕ} (i : TblIns n) (st : TblSt n A) (hst : ∀ j, st.val j < 2 ^ W) :
    ∀ j, (i.run A W w st).val j < 2 ^ W := by
  have hp := Nat.two_pow_pos W
  intro j
  cases i with
  | add a b c => simp only [TblIns.run, Function.update_apply]; split_ifs <;> simp [Nat.mod_lt, hp, hst]
  | sub a b c => simp only [TblIns.run, Function.update_apply]; split_ifs <;> simp [Nat.mod_lt, hp, hst]
  | mul a b c => simp only [TblIns.run, Function.update_apply]; split_ifs <;> simp [Nat.mod_lt, hp, hst]
  | div a b c =>
    simp only [TblIns.run, Function.update_apply]
    split_ifs
    · exact lt_of_le_of_lt (Nat.div_le_self _ _) (hst a)
    · exact hst j
  | mod a b c =>
    simp only [TblIns.run, Function.update_apply]
    split_ifs
    · exact lt_of_le_of_lt (Nat.mod_le _ _) (hst a)
    · exact hst j
  | copy a c => simp only [TblIns.run, Function.update_apply]; split_ifs <;> simp [hst]
  | zero c => simp only [TblIns.run, Function.update_apply]; split_ifs <;> simp [hp, hst]
  | inc c => simp only [TblIns.run, Function.update_apply]; split_ifs <;> simp [Nat.mod_lt, hp, hst]
  | emit a b => exact hst j

theorem TblBig.lt {n A W w : ℕ} {c : TblCode n} {st st' : TblSt n A} {k : ℕ}
    (h : TblBig A W w c st st' k) (hst : ∀ j, st.val j < 2 ^ W) : ∀ j, st'.val j < 2 ^ W := by
  induction h with
  | ins i st => exact TblIns.run_lt i st hst
  | seq _ _ ih₁ ih₂ => exact ih₂ (ih₁ hst)
  | iteT _ _ ih => exact ih hst
  | iteF _ _ ih => exact ih hst
  | loopF _ => exact hst
  | loopT _ _ _ ih₁ ih₂ => exact ih₂ (ih₁ hst)

/-- The per-atom step bound. -/
def tblC (W w : ℕ) : ℕ := 32 * (W + 4) ^ 2 + 8 * w

section Compile

variable {T Q A : ℕ} {U : Type} {P : Type} {n : ℕ} (rg : TblR n → Fin T)

/-- The host program of a table program. -/
def tblCompile : TblCode n → Pr P T Q A U
  | .ins i => tblInsProg rg i
  | .seq c d => .seq (tblCompile c) (tblCompile d)
  | .ite a b c d => .seq (tblTest rg a b) (.cond (tblTst rg) (tblCompile c) (tblCompile d))
  | .loop a b c => .seq (tblTest rg a b) (.loop (tblTst rg) (.seq (tblCompile c) (tblTest rg a b)))

variable {body : P → Pr P T Q A U} {rg} (hrg : Function.Injective rg)
include hrg

theorem tbl_ins_runs {W w : ℕ} (wl nl : List (Fin (A + 4))) (st : TblSt n A)
    (hwl : wl.length = W) (hnl : nl.length = w) (hw : w ≤ W) (hst : ∀ i, st.val i < 2 ^ W)
    (i : TblIns n) :
    tblRuns body rg (tblInsProg rg i) (tblRho W wl nl st) (tblRho W wl nl (i.run A W w st))
      (tblC W w) := by
  unfold tblC
  cases i with
  | add a b c => exact (tbl_add_runs hrg wl nl st hst a b c).mono (by nlinarith)
  | sub a b c => exact (tbl_sub_runs hrg wl nl st hst a b c).mono (by nlinarith)
  | mul a b c => exact (tbl_mul_runs hrg wl nl st hwl hst a b c).mono (by nlinarith)
  | div a b c => exact (tbl_divmod_runs hrg wl nl st hwl hst false a b c).mono (by nlinarith)
  | mod a b c => exact (tbl_divmod_runs hrg wl nl st hwl hst true a b c).mono (by nlinarith)
  | copy a c => exact (tbl_copy_runs hrg wl nl st a c).mono (by nlinarith)
  | zero c => exact (tbl_zero_runs hrg wl nl st hwl c).mono (by nlinarith)
  | inc c => exact (tbl_inc_runs hrg wl nl st c).mono (by nlinarith)
  | emit a b => exact (tbl_emit_runs hrg wl nl st hnl hw a b).mono (by nlinarith)

theorem tblCompile_aux {W w : ℕ} (wl nl : List (Fin (A + 4))) (hwl : wl.length = W)
    (hnl : nl.length = w) (hw : w ≤ W) {c : TblCode n} {st st' : TblSt n A} {k : ℕ}
    (h : TblBig A W w c st st' k) :
    (∀ j, st.val j < 2 ^ W) →
    tblRuns body rg (tblCompile rg c) (tblRho W wl nl st) (tblRho W wl nl st') (k * tblC W w) ∧
    (∀ a b d, c = .loop a b d → ∀ v S, tblHolds rg S (tblRho W wl nl st) →
      tblTst rg v = decide (st.val a < st.val b) →
      ∃ v' S' m, v'.user = v.user ∧ m + tblC W w ≤ k * tblC W w ∧
        Exec body (.loop (tblTst rg) (.seq (tblCompile rg d) (tblTest rg a b))) (mk v S) m
          (mk v' S') ∧ tblHolds rg S' (tblRho W wl nl st') ∧ tblFr rg S S') := by
  have hC : 24 * W + 25 ≤ tblC W w := by unfold tblC; nlinarith
  induction h with
  | ins i st =>
    intro hst
    refine ⟨(tbl_ins_runs hrg wl nl st hwl hnl hw hst i).mono (by simp), ?_⟩
    intro a b d h; cases h
  | seq h₁ h₂ ih₁ ih₂ =>
    intro hst
    refine ⟨(((ih₁ hst).1).seq ((ih₂ (h₁.lt hst)).1)).mono (by rw [Nat.add_mul]), ?_⟩
    intro a b d h; cases h
  | @iteT a b c d st st' k hlt h ih =>
    intro hst
    refine ⟨fun v S hS => ?_, fun a' b' d' h => by cases h⟩
    obtain ⟨v₁, S₁, m₁, hu₁, ht₁, hm₁, he₁, hS₁, hf₁⟩ := tbl_test_exec hrg wl nl st hst a b v S hS
    obtain ⟨v₂, S₂, m₂, hu₂, hm₂, he₂, hS₂, hf₂⟩ := (ih hst).1 v₁ S₁ hS₁
    refine ⟨v₂, S₂, m₁ + (m₂ + 1), hu₂.trans hu₁, by nlinarith,
      Exec.seq he₁ (Exec.cond_true (by simpa [hlt] using ht₁) he₂), hS₂, hf₁.trans hf₂⟩
  | @iteF a b c d st st' k hlt h ih =>
    intro hst
    refine ⟨fun v S hS => ?_, fun a' b' d' h => by cases h⟩
    obtain ⟨v₁, S₁, m₁, hu₁, ht₁, hm₁, he₁, hS₁, hf₁⟩ := tbl_test_exec hrg wl nl st hst a b v S hS
    obtain ⟨v₂, S₂, m₂, hu₂, hm₂, he₂, hS₂, hf₂⟩ := (ih hst).1 v₁ S₁ hS₁
    refine ⟨v₂, S₂, m₁ + (m₂ + 1), hu₂.trans hu₁, by nlinarith,
      Exec.seq he₁ (Exec.cond_false (by simpa [hlt] using ht₁) he₂), hS₂, hf₁.trans hf₂⟩
  | @loopF a b c st hlt =>
    intro hst
    refine ⟨fun v S hS => ?_, ?_⟩
    · obtain ⟨v₁, S₁, m₁, hu₁, ht₁, hm₁, he₁, hS₁, hf₁⟩ := tbl_test_exec hrg wl nl st hst a b v S hS
      exact ⟨v₁, S₁, m₁ + 1, hu₁, by nlinarith,
        Exec.seq he₁ (Exec.loop_false (by simpa [hlt] using ht₁)), hS₁, hf₁⟩
    · intro a' b' d' h v S hS ht
      cases h
      exact ⟨v, S, 1, rfl, by nlinarith, Exec.loop_false (by simpa [hlt] using ht), hS,
        tblFr.refl S⟩
  | @loopT a b c st st₁ st₂ k₁ k₂ hlt hc hl ihc ihl =>
    intro hst
    have hst₁ := hc.lt hst
    have key : ∀ v S, tblHolds rg S (tblRho W wl nl st) →
        tblTst rg v = decide (st.val a < st.val b) →
        ∃ v' S' m, v'.user = v.user ∧ m + tblC W w ≤ (k₁ + k₂ + 2) * tblC W w ∧
          Exec body (.loop (tblTst rg) (.seq (tblCompile rg c) (tblTest rg a b))) (mk v S) m
            (mk v' S') ∧ tblHolds rg S' (tblRho W wl nl st₂) ∧ tblFr rg S S' := by
      intro v S hS ht
      obtain ⟨v₁, S₁, m₁, hu₁, hm₁, he₁, hS₁, hf₁⟩ := (ihc hst).1 v S hS
      obtain ⟨v₂, S₂, m₂, hu₂, ht₂, hm₂, he₂, hS₂, hf₂⟩ :=
        tbl_test_exec hrg wl nl st₁ hst₁ a b v₁ S₁ hS₁
      obtain ⟨v₃, S₃, m₃, hu₃, hm₃, he₃, hS₃, hf₃⟩ := (ihl hst₁).2 a b c rfl v₂ S₂ hS₂ ht₂
      refine ⟨v₃, S₃, m₁ + m₂ + m₃ + 1, hu₃.trans (hu₂.trans hu₁), by nlinarith,
        Exec.loop_true (by simpa [hlt] using ht) (Exec.seq he₁ he₂) he₃, hS₃,
        hf₁.trans (hf₂.trans hf₃)⟩
    refine ⟨fun v S hS => ?_, fun a' b' d' h => ?_⟩
    · obtain ⟨v₁, S₁, m₁, hu₁, ht₁, hm₁, he₁, hS₁, hf₁⟩ := tbl_test_exec hrg wl nl st hst a b v S hS
      obtain ⟨v₂, S₂, m₂, hu₂, hm₂, he₂, hS₂, hf₂⟩ := key v₁ S₁ hS₁ ht₁
      exact ⟨v₂, S₂, m₁ + m₂, hu₂.trans hu₁, by nlinarith, Exec.seq he₁ he₂, hS₂, hf₁.trans hf₂⟩
    · cases h
      exact key

/-- **Compilation.** A derivation of `TblBig` with `k` atoms from a state with values below
`2 ^ W` runs on the host in at most `k · tblC W w` steps between the register files of the two
states. -/
theorem tblCompile_runs {W w : ℕ} (wl nl : List (Fin (A + 4))) (hwl : wl.length = W)
    (hnl : nl.length = w) (hw : w ≤ W) {c : TblCode n} {st st' : TblSt n A} {k : ℕ}
    (h : TblBig A W w c st st' k) (hst : ∀ j, st.val j < 2 ^ W) :
    tblRuns body rg (tblCompile rg c) (tblRho W wl nl st) (tblRho W wl nl st') (k * tblC W w) :=
  (tblCompile_aux hrg wl nl hwl hnl hw h hst).1

end Compile

end Code

end IntegerMultBounds.MathlibTM2.Fast.TableVM
