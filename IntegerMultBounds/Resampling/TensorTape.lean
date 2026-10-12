module

public import IntegerMultBounds.Resampling.LineMaps
public import IntegerMultBounds.Resampling.Sandwich

/-! The tensor driver's result on entries. With one expansion record per axis
(`eAxis`), the script of `Sandwich.sScript` turns the flat array of entries into
the flat pass of the line maps `lineA` (`expand_result`). -/

@[expose] public section

namespace IntegerMultBounds.Resampling.TensorTape
noncomputable section

open Machine Schoenhage AxisDriver AxisInst Script ScriptSem FlatTensor LineMaps Sandwich

variable {α : Type*}

theorem mapBlocks_single (n : ℕ) (g : List α → List α) (xs : List α) (x : α) (hl : xs.length = n) (hn : 0 < n)
    (hg : (g xs).length = n) : mapBlocks n g xs = g xs := by
  have hb : block n 0 xs = xs := by simp [block, ← hl]
  have hgb : ∀ b, b < 1 → (g (block n b xs)).length = n := fun b hb' => by
    rw [show b = 0 by omega, hb]; exact hg
  have hlen : (mapBlocks n g xs).length = n := by
    rw [length_mapBlocks n n g xs (fun b hb' => hgb b (by rw [hl, Nat.div_self hn] at hb'; exact hb')), hl,
      Nat.div_self hn, one_mul]
  apply ext_getD' x
  · rw [hlen, hg]
  · intro j hj
    rw [hlen] at hj
    have h' := getD_mapBlocks n n 1 g xs hn (by rw [hl, one_mul]) hgb (b := 0) (by omega) hj x
    rw [zero_mul, zero_add, hb] at h'
    exact h'

/-- The parameters of one expansion axis: its weight table and source length. -/
structure EParam where
  wt : List (List Bool)
  s : ℕ
  sW : List Bool
  tW : List Bool

/-- Axis `i`'s expansion record. -/
def eAxis {d : ℕ} (lg : Fin d → ℕ) (NT m w : ℕ) (P : Fin d → EParam) (i : Fin d) : List (List Bool) :=
  eWords (P i).wt (P i).s (2 ^ lg i) m w (NT / 2 ^ lg i) (P i).sW (P i).tW

theorem dvd_prod {d : ℕ} (lg : Fin d → ℕ) (i : Fin d) : 2 ^ lg i ∣ ∏ j, 2 ^ lg j :=
  Finset.dvd_prod_of_mem _ (Finset.mem_univ i)

theorem lineA_length (wt : List (List Bool)) (s t m p w W : ℕ) (l : List (List Bool)) :
    (lineA wt s t m p w W l).length = t :=
  length_pairUp t _ (by rw [List.length_map]; exact Resampling.NeumannWords.outWords_length _ _ _ _ _ _ _ _ _)

theorem lineA_width (wt : List (List Bool)) (s t m p w W : ℕ) (l : List (List Bool)) :
    ∀ e ∈ lineA wt s t m p w W l, e.length = 2 * w :=
  length_pairUp_mem w _ (fun f hf => by
    simp only [List.mem_map] at hf; obtain ⟨y, -, rfl⟩ := hf; simp [floorWord])

/-- The hypotheses on one expansion axis. -/
def EAxisOk (m w : ℕ) (t : ℕ) (P : EParam) : Prop :=
  (∀ x ∈ P.wt, x.length = w) ∧ P.wt.length = t * (2 * m + 1) ∧ m + 1 ≤ P.s ∧ P.s ≤ t ∧ 0 < P.s ∧
    Counter.value P.sW = P.s ∧ Counter.value P.tW = t ∧ P.sW.length ≤ P.tW.length + 1

theorem expand_result (d : ℕ) (lg : Fin d → ℕ) (m p w W : ℕ) (P : Fin d → EParam) (es : List (List Bool))
    (hlg : ∀ i j, lg i ≤ lg j + 1) (hw : 1 ≤ w) (hpw : p ≤ w) (hwW : w ≤ W)
    (hok : ∀ i, EAxisOk m w (2 ^ lg i) (P i)) (hl : es.length = ∏ i, 2 ^ lg i)
    (hes : ∀ e ∈ es, e.length = 2 * w) :
    Valid (expandSpec m p w W) (sScript (2 * w) d lg 1 (eAxis lg (∏ i, 2 ^ lg i) m w P)) es.flatten ∧
      result (expandSpec m p w W) (sScript (2 * w) d lg 1 (eAxis lg (∏ i, 2 ^ lg i) m w P)) es.flatten =
        (flatPass d (fun i => 2 ^ lg i) (fun i => lineA (P i).wt (P i).s (2 ^ lg i) m p w W) [] es).flatten := by
  set NT := ∏ i, 2 ^ lg i
  have hNT : 0 < NT := prod_pos_pow lg
  obtain ⟨hv, hr⟩ := sScript_spec (expandSpec m p w W) (2 * w) NT (by omega) d lg 1 (eAxis lg NT m w P)
    (fun i => lineA (P i).wt (P i).s (2 ^ lg i) m p w W) es hlg
    (fun i l _ => lineA_length _ _ _ _ _ _ _ l) (fun i l _ _ => lineA_width _ _ _ _ _ _ _ l)
    (fun i xs hxl hxw => by
      obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hok i
      have ht : 0 < 2 ^ lg i := by positivity
      have hL : NT / 2 ^ lg i * 2 ^ lg i = NT := Nat.div_mul_cancel (dvd_prod lg i)
      have hA : xs.flatten.length = NT / 2 ^ lg i * (2 * 2 ^ lg i * w) := by
        rw [length_flatten_uniform (2 * w) _ hxw, hxl]
        calc NT * (2 * w) = NT / 2 ^ lg i * 2 ^ lg i * (2 * w) := by rw [hL]
          _ = _ := by ring
      refine ⟨rfl, ⟨(P i).wt, (P i).s, 2 ^ lg i, NT / 2 ^ lg i, (P i).sW, (P i).tW, rfl,
        hw, hpw, hwW, h1, h2, h3, h4, h5, h6, h7, h8, hA⟩, ?_⟩
      show (let q := eDec w (eAxis lg NT m w P i); AxisStep.expandOut xs.flatten q.1 q.2.1 q.2.2.1 m p w W q.2.2.2.1) = _
      simp only [eAxis, eDec_eWords _ _ _ _ _ _ _ _ hw h1 h7]
      exact expandOut_eq xs (P i).wt (P i).s (2 ^ lg i) m p w W (NT / 2 ^ lg i) hw ht h4 hxw (by rw [hxl, hL]))
    one_pos (by simp [NT]) hl hes
  refine ⟨hv, hr.trans ?_⟩
  congr 1
  exact mapBlocks_single NT _ es [] hl hNT
    (flatPass_props (fun _ => True) d lg _ [] es (fun i l hl' _ => ⟨lineA_length _ _ _ _ _ _ _ l, fun _ _ => trivial⟩)
      hl (fun _ _ => trivial)).1

/-! ### Compression -/

/-- The parameters of one compression axis: its weight tables, zero words and target length. -/
structure CParam where
  wtE : List (List Bool)
  wtH : List (List Bool)
  wtD : List (List Bool)
  zeros : List (List Bool)
  s : ℕ
  sW : List Bool
  tW : List Bool

/-- Axis `i`'s compression record. -/
def cAxis {d : ℕ} (lg : Fin d → ℕ) (NT m w : ℕ) (P : Fin d → CParam) (i : Fin d) : List (List Bool) :=
  cWords (P i).wtE (P i).wtH (P i).wtD (P i).zeros (P i).s (2 ^ lg i) m w (NT / 2 ^ lg i) (P i).sW (P i).tW

/-- The hypotheses on one compression axis. -/
def CAxisOk (m w t : ℕ) (P : CParam) : Prop :=
  (∀ x ∈ P.wtE, x.length = w) ∧ P.wtE.length = P.s * (2 * m + 1) ∧ (∀ x ∈ P.wtH, x.length = w) ∧
  P.wtH.length = P.s * (2 * 0 + 1) ∧ (∀ x ∈ P.wtD, x.length = w) ∧ P.wtD.length = P.s * (2 * 0 + 1) ∧
  P.zeros.length = 2 * P.s ∧ (∀ x ∈ P.zeros, x.length = w) ∧ m + 1 ≤ P.s ∧ 0 < P.s ∧ P.s < t ∧
  Counter.value P.sW = P.s ∧ Counter.value P.tW = P.s ∧ P.sW.length ≤ P.tW.length + 1

theorem lineB_length (P : CParam) (t m p w W : ℕ) (hz : P.zeros.length = 2 * P.s) (hst : P.s ≤ t)
    (l : List (List Bool)) : (lineB P.wtE P.wtH P.wtD P.zeros P.s t m p w W l).length = t := by
  simp only [lineB, List.length_append, List.length_replicate]
  rw [length_pairUp P.s _ (by simp only [b0Word, B0Words.oneStep, Resampling.NeumannWords.nextWords_length, hz])]
  omega

theorem lineB_width (P : CParam) (t m p w W : ℕ) (hzw : ∀ x ∈ P.zeros, x.length = w) (l : List (List Bool)) :
    ∀ e ∈ lineB P.wtE P.wtH P.wtD P.zeros P.s t m p w W l, e.length = 2 * w := by
  intro e he
  simp only [lineB, List.mem_append, List.mem_replicate] at he
  rcases he with he | ⟨-, rfl⟩
  · exact length_pairUp_mem w _ (by simp only [b0Word, B0Words.oneStep]; exact NeumannStep.nextWords_shape _ _ w hzw) e he
  · simp

theorem compress_result (d : ℕ) (lg : Fin d → ℕ) (m p w W : ℕ) (P : Fin d → CParam) (es : List (List Bool))
    (hlg : ∀ i j, lg i ≤ lg j + 1) (hw : 1 ≤ w) (hpw : p ≤ w) (hwW : w ≤ W) (hp2 : 2 ≤ p)
    (hok : ∀ i, CAxisOk m w (2 ^ lg i) (P i)) (hl : es.length = ∏ i, 2 ^ lg i)
    (hes : ∀ e ∈ es, e.length = 2 * w) :
    Valid (compressSpec m p w W) (sScript (2 * w) d lg 1 (cAxis lg (∏ i, 2 ^ lg i) m w P)) es.flatten ∧
      result (compressSpec m p w W) (sScript (2 * w) d lg 1 (cAxis lg (∏ i, 2 ^ lg i) m w P)) es.flatten =
        (flatPass d (fun i => 2 ^ lg i)
          (fun i => lineB (P i).wtE (P i).wtH (P i).wtD (P i).zeros (P i).s (2 ^ lg i) m p w W) [] es).flatten := by
  set NT := ∏ i, 2 ^ lg i
  have hNT : 0 < NT := prod_pos_pow lg
  have hlen : ∀ i (l : List (List Bool)), l.length = 2 ^ lg i →
      (lineB (P i).wtE (P i).wtH (P i).wtD (P i).zeros (P i).s (2 ^ lg i) m p w W l).length = 2 ^ lg i :=
    fun i l _ => lineB_length (P i) _ m p w W (hok i).2.2.2.2.2.2.1 (hok i).2.2.2.2.2.2.2.2.2.2.1.le l
  obtain ⟨hv, hr⟩ := sScript_spec (compressSpec m p w W) (2 * w) NT (by omega) d lg 1 (cAxis lg NT m w P)
    (fun i => lineB (P i).wtE (P i).wtH (P i).wtD (P i).zeros (P i).s (2 ^ lg i) m p w W) es hlg hlen
    (fun i l _ _ => lineB_width (P i) _ m p w W (hok i).2.2.2.2.2.2.2.1 l)
    (fun i xs hxl hxw => by
      obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ := hok i
      have ht : 0 < 2 ^ lg i := by positivity
      have hL : NT / 2 ^ lg i * 2 ^ lg i = NT := Nat.div_mul_cancel (dvd_prod lg i)
      have hA : xs.flatten.length = NT / 2 ^ lg i * (2 * 2 ^ lg i * w) := by
        rw [length_flatten_uniform (2 * w) _ hxw, hxl]
        calc NT * (2 * w) = NT / 2 ^ lg i * 2 ^ lg i * (2 * w) := by rw [hL]
          _ = _ := by ring
      refine ⟨rfl, ⟨(P i).wtE, (P i).wtH, (P i).wtD, (P i).zeros, (P i).s, 2 ^ lg i, NT / 2 ^ lg i, (P i).sW,
        (P i).tW, rfl, hw, hpw, hwW, hp2, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, hA⟩, ?_⟩
      show (let q := cDec w (cAxis lg NT m w P i)
        AxisStep.compressOut xs.flatten q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2.1 q.2.2.2.2.2.1 m p w W
          q.2.2.2.2.2.2.1) = _
      simp only [cAxis, cDec_cWords _ _ _ _ _ _ _ _ _ _ _ hw h1 h3 h5 h8]
      exact compressOut_eq xs _ _ _ _ (P i).s (2 ^ lg i) m p w W (NT / 2 ^ lg i) hw ht h10 h11.le h7 h8 hxw
        (by rw [hxl, hL]))
    one_pos (by simp [NT]) hl hes
  refine ⟨hv, hr.trans ?_⟩
  congr 1
  exact mapBlocks_single NT _ es [] hl hNT
    (flatPass_props (fun _ => True) d lg _ [] es (fun i l hl' _ => ⟨hlen i l hl', fun _ _ => trivial⟩)
      hl (fun _ _ => trivial)).1

end
end IntegerMultBounds.Resampling.TensorTape
