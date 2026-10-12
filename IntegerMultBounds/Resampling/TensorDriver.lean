module

public import IntegerMultBounds.Resampling.TensorNumeric

/-! The tensor driver as a literal program. `driveProg S` is the compiled
driver loop; from the bank holding the rest state, the array and a script it
halts within `driveCost` steps with the script's result on the array tape
(`drive_hoare`). With expansion records the decoded result is the tensor of
the floored tabled `Ã` maps (`expand_hoare`); with compression records, the
tensor of the padded tabled `B̃₀` maps (`compress_hoare`). -/

@[expose] public section

namespace IntegerMultBounds.Resampling.TensorDriver
noncomputable section

open Machine Schoenhage AxisDriver AxisInst Script Sandwich FlatTensor TensorTape LineNumeric TensorNumeric PaddedTensor
open Networks.Shared50ModularControl (prime)
open IntegerMultBounds.NLogN (tensorZR)

variable {E : ℕ}

theorem nb_pos : 0 < NB E := by unfold NB; omega

/-- The compiled driver. -/
def driveProg (S : AxisSpec E) := (compile nb_pos (drive S)).2

theorem drive_hoare (S : AxisSpec E) (rs : List Rec) (A : List Bool) (hv : Valid S rs A) :
    HoareTime (driveProg S) (· = enc (bank S.ρ S.X A ⟨[], rs.flatMap Rec.words⟩))
      (· = enc (bank S.ρ S.X (result S rs A) ⟨(rs.flatMap Rec.words).reverse, []⟩)) (driveCost S rs A) := by
  obtain ⟨σ', k, hex, hq, hk⟩ := runs_drive S rs A [] hv
  rw [List.append_nil] at hq
  subst hq
  exact (compile_correct nb_pos hex).consequence (fun _ h => h) (fun _ h => h) hk

/-- The tensor driver with expansion records: its decoded output is the tensor of the floored tabled `Ã`
maps on the restricted input. -/
theorem expand_hoare (d : ℕ) (lg : Fin d → ℕ) (m α p w W : ℕ) (P : Fin d → EParam) [∀ i, NeZero (P i).s]
    (hlg : ∀ i j, lg i ≤ lg j + 1) (hα : 2 ≤ α) (hαp : α ^ 2 ≤ p) (hm : p * α ^ 2 ≤ m ^ 2) (hm1 : 1 ≤ m)
    (hmp : m ≤ p) (hp : 13 ≤ p) (hw : p + 2 ≤ w) (hwW : w + 1 ≤ W)
    (hW : ((2 * m + 1 : ℕ) : ℤ) * 2 ^ p < 2 ^ (W - 1))
    (hok : ∀ i, EAxisOk m w (2 ^ lg i) (P i))
    (hwt : ∀ i, (P i).wt = TabATape.tabA (P i).s (2 ^ lg i) m α p w (2 ^ lg i * (2 * m + 1)))
    (es : List (List Bool)) (hes : ∀ e ∈ es, e.length = 2 * w ∧ ‖decE w p e‖ ≤ 1)
    (hl : es.length = ∏ i, 2 ^ lg i) (u : ((i : Fin d) → ZMod (2 ^ lg i)) → ℂ)
    (hu : es.map (decE w p) = lexFlat d (fun i => 2 ^ lg i) u) :
    HoareTime (driveProg (expandSpec m p w W))
      (· = enc (bank (eRest m p w W) AxisStep.tX es.flatten
        ⟨[], (sScript (2 * w) d lg 1 (eAxis lg (∏ i, 2 ^ lg i) m w P)).flatMap Rec.words⟩))
      (fun v => ∃ out : List (List Bool), v = enc (bank (eRest m p w W) AxisStep.tX out.flatten
        ⟨((sScript (2 * w) d lg 1 (eAxis lg (∏ i, 2 ^ lg i) m w P)).flatMap Rec.words).reverse, []⟩) ∧
        out.map (decE w p) = lexFlat d (fun i => 2 ^ lg i) (tensorZR d (fun i => (P i).s) (fun i => 2 ^ lg i)
          (fun i => floorAt (P i).s (2 ^ lg i) m α p) (restrD (fun i => (P i).s) (fun i => 2 ^ lg i) u)))
      (driveCost (expandSpec m p w W) (sScript (2 * w) d lg 1 (eAxis lg (∏ i, 2 ^ lg i) m w P)) es.flatten) := by
  obtain ⟨hv, hr⟩ := expand_result d lg m p w W P es hlg (by omega) (by omega) (by omega) hok hl
    (fun e he => (hes e he).1)
  refine (drive_hoare (expandSpec m p w W) _ es.flatten hv).consequence (fun _ h => by rw [h]; unfold expandSpec; rfl)
    (fun v hv' => ?_) le_rfl
  refine ⟨_, hv'.trans (by rw [hr]; unfold expandSpec; rfl), ?_⟩
  have := expand_tensor d lg (fun i => (P i).s) m α p w W hα hαp hm hm1 hmp hp hw hwW hW
    (fun i => (hok i).2.2.2.1) es hes hl u hu
  rw [← this]
  congr 2
  funext i
  rw [hwt i]

/-- The tensor driver with compression records: its decoded output is the square tensor of the padded
tabled `B̃₀` maps. -/
theorem compress_hoare (d : ℕ) (lg : Fin d → ℕ) (m α p w W : ℕ) (P : Fin d → CParam) [∀ i, NeZero (P i).s]
    (hlg : ∀ i j, lg i ≤ lg j + 1) (hcop : ∀ i, Nat.Coprime (P i).s (2 ^ lg i)) (hα : 2 ≤ α)
    (hαp : α ^ 2 ≤ p) (hθ : ∀ i, 1 ≤ (α : ℝ) ^ 2 * (((2 ^ lg i : ℕ) : ℝ) / (P i).s - 1)) (hp : 13 ≤ p)
    (hw : p + 3 ≤ w) (hwW : w ≤ W) (hWW : ((2 * NLogN.sqrtWindow p + 1 : ℕ) : ℤ) * 2 ^ p < 2 ^ (W - 1))
    (hm : m = NLogN.sqrtWindow p) (hok : ∀ i, CAxisOk m w (2 ^ lg i) (P i))
    (htab : ∀ i, ((P i).wtE, (P i).wtH, (P i).wtD, (P i).zeros) = cTabs (P i).s (2 ^ lg i) α p w)
    (es : List (List Bool)) (hes : ∀ e ∈ es, e.length = 2 * w ∧ ‖decE w p e‖ ≤ 1)
    (hl : es.length = ∏ i, 2 ^ lg i) (u : ((i : Fin d) → ZMod (2 ^ lg i)) → ℂ)
    (hu : es.map (decE w p) = lexFlat d (fun i => 2 ^ lg i) u) :
    HoareTime (driveProg (compressSpec m p w W))
      (· = enc (bank (cRest m p w W) AxisStep.cX es.flatten
        ⟨[], (sScript (2 * w) d lg 1 (cAxis lg (∏ i, 2 ^ lg i) m w P)).flatMap Rec.words⟩))
      (fun v => ∃ out : List (List Bool), v = enc (bank (cRest m p w W) AxisStep.cX out.flatten
        ⟨((sScript (2 * w) d lg 1 (cAxis lg (∏ i, 2 ^ lg i) m w P)).flatMap Rec.words).reverse, []⟩) ∧
        out.map (decE w p) = lexFlat d (fun i => 2 ^ lg i) (tensorZR d (fun i => 2 ^ lg i) (fun i => 2 ^ lg i)
          (fun i => padB (P i).s (2 ^ lg i) α p) u))
      (driveCost (compressSpec m p w W) (sScript (2 * w) d lg 1 (cAxis lg (∏ i, 2 ^ lg i) m w P)) es.flatten) := by
  obtain ⟨hv, hr⟩ := compress_result d lg m p w W P es hlg (by omega) (by omega) hwW (by omega) hok hl
    (fun e he => (hes e he).1)
  refine (drive_hoare (compressSpec m p w W) _ es.flatten hv).consequence (fun _ h => by rw [h]; rfl)
    (fun v hv' => ?_) le_rfl
  refine ⟨_, hv'.trans (by rw [hr]; rfl), ?_⟩
  have := compress_tensor d lg (fun i => (P i).s) α p w W (fun i => (hok i).2.2.2.2.2.2.2.2.2.2.1) hcop hα hαp hθ hp
    hw hwW hWW es hes hl u hu
  rw [← this]
  congr 2
  funext i
  have h := htab i
  rw [show (P i).wtE = (cTabs (P i).s (2 ^ lg i) α p w).1 from congrArg Prod.fst h,
    show (P i).wtH = (cTabs (P i).s (2 ^ lg i) α p w).2.1 from congrArg (fun x => x.2.1) h,
    show (P i).wtD = (cTabs (P i).s (2 ^ lg i) α p w).2.2.1 from congrArg (fun x => x.2.2.1) h,
    show (P i).zeros = (cTabs (P i).s (2 ^ lg i) α p w).2.2.2 from congrArg (fun x => x.2.2.2) h, hm]

end
end IntegerMultBounds.Resampling.TensorDriver
