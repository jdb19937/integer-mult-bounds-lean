module

public import IntegerMultBounds.MathlibTM2.DFT.Output
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The main procedure

`M.dftMain B σ₀ = parse ; pipeline ; clearAll ; writeOut rOut ; load σ₀`. `dftMain_exec`: on
every instance `x` it runs from `x.encode` alone on `gin` to `encodeNatList x.transform` alone
on `gout` in at most `dftBound H n w` steps, `w = Nat.size p`, for a time majorant
`M.time n ≤ (n + 1) H n` with `H` monotone.

* `clearAll r rs` (`clearAll_exec`): every register of `r :: rs` cleared.
* `pipeR_frame`, `pipeR_empty`, `pipeR_out`, `cleanup_cost`: the registers after the pipeline:
  untouched ones keep their value, the work registers outside the cleared list are empty, `rOut`
  holds the printed values, and the cleared registers hold `O(w (n + 1))` symbols.
-/

@[expose] public section

open Computability IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node

open scoped IntegerMultBounds.MathlibTM2.DFT.Reg

namespace IntegerMultBounds.MathlibTM2.DFT

section Clear

variable {T Q A : ℕ} {U P : Type} (body : P → Pr P T Q A U)

/-- Clear every register of `r :: rs`. -/
def clearAll (r : Fin T) : List (Fin T) → Pr P T Q A U
  | [] => bclear r
  | s :: rs => .seq (bclear r) (clearAll s rs)

theorem clearAll_exec : ∀ (r : Fin T) (rs : List (Fin T)), (r :: rs).Nodup →
    ∀ (v : HS T Q A U) (S : Stacks T A), ∃ v' : HS T Q A U, v'.user = v.user ∧
      Exec body (clearAll r rs) (mk v S) ((r :: rs).map fun x => 2 * (S.R x).length + 2).sum
        (mk v' { S with R := fun j => if j ∈ r :: rs then [] else S.R j })
  | r, [], _, v, S => by
      obtain ⟨v', hu, -, e⟩ := bclear_exec body r v S
      refine ⟨v', hu, e.cast (by simp) ?_⟩
      congr 2
      funext j
      by_cases h : j = r <;> simp [h, Function.update_apply]
  | r, s :: rs, hnd, v, S => by
      obtain ⟨v₁, hu₁, -, e₁⟩ := bclear_exec body r v S
      obtain ⟨v₂, hu₂, e₂⟩ := clearAll_exec s rs hnd.of_cons v₁
        { S with R := Function.update S.R r [] }
      have hmap : ((s :: rs).map fun x =>
          2 * (({ S with R := Function.update S.R r [] } : Stacks T A).R x).length + 2) =
          (s :: rs).map fun x => 2 * (S.R x).length + 2 := by
        apply List.map_congr_left
        intro x hx
        have : x ≠ r := fun h => (List.nodup_cons.1 hnd).1 (h ▸ hx)
        simp [Function.update_of_ne this]
      rw [hmap] at e₂
      refine ⟨v₂, by rw [hu₂, hu₁], Exec.cast (Exec.seq e₁ e₂) (by simp) ?_⟩
      congr 2
      funext j
      by_cases h : j = r
      · subst h; simp
      · simp [h, Function.update_of_ne h]

end Clear

theorem natSyms_length_le {A : ℕ} {w : ℕ} (l : List ℕ) (hl : ∀ x ∈ l, x < 2 ^ w) :
    (natSyms l : List (Fin (A + 4))).length ≤ l.length * (w + 1) := by
  induction l with
  | nil => simp [natSyms]
  | cons x l ih =>
    have hx := Nat.size_le.2 (hl x (List.mem_cons_self ..))
    have := ih (fun y hy => hl y (List.mem_cons_of_mem _ hy))
    have e : (natSyms (x :: l) : List (Fin (A + 4))).length =
        Nat.size x + 1 + (natSyms l : List (Fin (A + 4))).length := by
      unfold natSyms
      rw [List.flatMap_cons, List.length_append, List.length_append, length_binSyms,
        List.length_singleton]
    rw [e, List.length_cons, show (l.length + 1) * (w + 1) = l.length * (w + 1) + (w + 1) by ring]
    omega

theorem length_encodeFixedList (w : ℕ) (l : List ℕ) :
    (encodeFixedList w l).length = l.length * (w + 1) := by
  rw [← length_fieldSyms (A := 0), length_fieldSyms']

namespace HostMultiplier

variable {κ : ℝ} (M : HostMultiplier κ) (B : Type)

theorem chirpCost_mono {H : ℕ → ℕ} (hH : Monotone H) {k k' : ℕ} (h : k ≤ k') :
    chirpCost H k ≤ chirpCost H k' := by
  unfold chirpCost
  have h1 := hH (show 3 * k + 3 ≤ 3 * k' + 3 by omega)
  have : (1130 + 18 * H (3 * k + 3)) * k ≤ (1130 + 18 * H (3 * k' + 3)) * k' :=
    Nat.mul_le_mul (by omega) h
  omega

theorem inputCost_mono {H : ℕ → ℕ} (hH : Monotone H) {k k' : ℕ} (h : k ≤ k') :
    inputCost H k ≤ inputCost H k' := by
  unfold inputCost
  have h1 := hH (show 3 * k + 3 ≤ 3 * k' + 3 by omega)
  have : (1680 + 27 * H (3 * k + 3)) * k ≤ (1680 + 27 * H (3 * k' + 3)) * k' :=
    Nat.mul_le_mul (by omega) h
  omega

theorem unpackCost_mono {H : ℕ → ℕ} (hH : Monotone H) {k k' : ℕ} (h : k ≤ k') :
    unpackCost H k ≤ unpackCost H k' := by
  unfold unpackCost
  have h1 := hH (show 4 * k + 3 ≤ 4 * k' + 3 by omega)
  have : (2200 + 35 * H (4 * k + 3)) * k ≤ (2200 + 35 * H (4 * k' + 3)) * k' :=
    Nat.mul_le_mul (by omega) h
  omega

/-- The registers cleared before printing. -/
def clearList : List (Fin 50) := [rWm, rWR, rW3, rAa, rWK, rWinv, rV2, rUp, rDw, rZp, rC, rE]

/-- The pipeline and the cleanup. -/
def dftWork : DPr (Option M.P) (M.T + 50) M.Q M.A (M.U × B) :=
  .seq (M.pipeline B) (hostCode (clearAll (M.dreg 50 rPw) (clearList.map (M.dreg 50))))

/-- Everything after `parse`. -/
def dftTail (σ₀ : HS (M.T + 50) M.Q M.A (M.U × B)) : DPr (Option M.P) (M.T + 50) M.Q M.A (M.U × B) :=
  .seq (M.dftWork B) (.seq (writeOut (M.dreg 50 rOut)) (.act (.load (fun _ => σ₀) .done)))

/-- The main procedure. -/
def dftMain (σ₀ : HS (M.T + 50) M.Q M.A (M.U × B)) : DPr (Option M.P) (M.T + 50) M.Q M.A (M.U × B) :=
  .seq (parse (M.dreg 50 rIn) (M.dreg 50 rEnt) (M.dreg 50 rPw) (M.dreg 50 rWm) (M.dreg 50 rT))
    (M.dftTail B σ₀)

/-- The registers the pipeline writes. -/
def touched : List (Fin 50) := [rWR, rW3, rWK, rAa, rF, rC, rE, rWinv, rV, rV2, rEnt, rUp, rNcnt, rDw, rZp, rOut]

theorem pipeR_frame {w p ω k : ℕ} (as : List ℕ) (Kc : List (Fin (M.A + 4)))
    (R : Fin (M.T + 50) → List (Fin (M.A + 4))) (j : Fin 50) (hj : j ∉ touched) :
    M.pipeR w p ω k as Kc R (M.dreg 50 j) = R (M.dreg 50 j) := by
  simp only [touched, List.mem_cons, List.not_mem_nil, or_false, not_or] at hj
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩ := hj
  simp [pipeR, unpackR, pipeR3, inputR, pipeR2, chirpB, chirpA, pipeR1, Function.update_apply, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13,
    h14, h15, h16]

theorem pipeR_emb {w p ω k : ℕ} (as : List ℕ) (Kc : List (Fin (M.A + 4)))
    (R : Fin (M.T + 50) → List (Fin (M.A + 4))) (i : Fin M.T) :
    M.pipeR w p ω k as Kc R (M.emb 50 i) = R (M.emb 50 i) := by
  simp [pipeR, unpackR, pipeR3, inputR, pipeR2, chirpB, chirpA, pipeR1, Function.update_apply]

theorem pipeR_out {w p ω k : ℕ} (as : List ℕ) (Kc : List (Fin (M.A + 4)))
    (R : Fin (M.T + 50) → List (Fin (M.A + 4))) :
    M.pipeR w p ω k as Kc R (M.dreg 50 rOut) =
      (natSyms ((List.range as.length).map
        (unpackVal p (ω ^ (as.length - 1) % p) w (pipeZ w p ω as)))).reverse := by
  simp [pipeR, unpackR]

theorem pipeR_empty {w p ω k : ℕ} (as : List ℕ) (Kc : List (Fin (M.A + 4)))
    (R : Fin (M.T + 50) → List (Fin (M.A + 4))) (j : Fin 50) (hj : j ∈ [rF, rV, rEnt, rNcnt]) :
    M.pipeR w p ω k as Kc R (M.dreg 50 j) = [] := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
  rcases hj with rfl | rfl | rfl | rfl <;> simp [pipeR, unpackR, pipeR3, inputR, pipeR2, chirpB, chirpA, pipeR1, fieldSyms]

theorem cleanup_cost {w p ω k : ℕ} (as : List ℕ) (Kc : List (Fin (M.A + 4)))
    (R : Fin (M.T + 50) → List (Fin (M.A + 4))) (hKc : Kc.length = k) (hk : k ≤ 2 * (2 * w))
    (hPw : R (M.dreg 50 rPw) = binSyms w p) (hWm : R (M.dreg 50 rWm) = binSyms w ω) :
    ((M.dreg 50 rPw :: clearList.map (M.dreg 50)).map
      fun x => 2 * (M.pipeR w p ω k as Kc R x).length + 2).sum ≤
        100 * w * (as.length + 1) + 100 := by
  have e : 2 * as.length + 1 - as.length = as.length + 1 := by omega
  simp [clearList, pipeR, unpackR, pipeR3, inputR, pipeR2, chirpB, chirpA, pipeR1, Function.update_apply, hPw, hWm, hKc, length_binSyms, e]
  have e1 : 3 * w * (as.length + as.length) = 6 * (w * as.length) := by ring
  have e2 : 3 * w * (as.length + 1) = 3 * (w * as.length) + 3 * w := by ring
  have e3 : 3 * w * as.length = 3 * (w * as.length) := by ring
  have e4 : 100 * w * (as.length + 1) = 100 * (w * as.length) + 100 * w := by ring
  omega

theorem final_empty {w p ω k : ℕ} (as : List ℕ) (Kc : List (Fin (M.A + 4)))
    (R : Fin (M.T + 50) → List (Fin (M.A + 4))) (hR : ∀ i, R (M.emb 50 i) = [])
    (hclean : ∀ j : Fin 50, j ≠ rEnt → j ≠ rPw → j ≠ rWm → R (M.dreg 50 j) = []) :
    Function.update (fun j => if j ∈ M.dreg 50 rPw :: clearList.map (M.dreg 50) then []
      else M.pipeR w p ω k as Kc R j) (M.dreg 50 rOut) [] = fun _ => [] := by
  funext j
  refine Fin.addCases (fun i => ?_) (fun j' => ?_) j
  · have : M.emb 50 i ≠ M.dreg 50 rOut := by simp
    rw [Function.update_of_ne this]
    have hm : M.emb 50 i ∉ M.dreg 50 rPw :: clearList.map (M.dreg 50) := by simp [clearList]
    simp only [if_neg hm]
    rw [pipeR_emb]
    exact hR i
  · by_cases hO : j' = rOut
    · subst hO; exact Function.update_self _ _ _
    rw [Function.update_of_ne (by simpa using hO)]
    by_cases hm : j' ∈ rPw :: clearList
    · have : M.dreg 50 j' ∈ M.dreg 50 rPw :: clearList.map (M.dreg 50) := by
        simpa using hm
      simp only [if_pos this]
    · have hm' : M.dreg 50 j' ∉ M.dreg 50 rPw :: clearList.map (M.dreg 50) := by
        simpa using hm
      simp only [if_neg hm']
      by_cases he : j' ∈ [rF, rV, rEnt, rNcnt]
      · exact M.pipeR_empty as Kc R j' he
      · have ht : j' ∉ touched := by
          simp only [touched, clearList, List.mem_cons, List.not_mem_nil, or_false,
            not_or] at hm he ⊢
          omega
        rw [M.pipeR_frame as Kc R j' ht]
        simp only [clearList, List.mem_cons, List.not_mem_nil, or_false, not_or] at hm he
        exact hclean j' he.2.2.1 hm.1 hm.2.1

/-- The step bound of the pipeline on `n` entries of `w` bits. -/
def pipeBound (H : ℕ → ℕ) (n w : ℕ) : ℕ :=
  (7200 + 27 * H (4 * (2 * w) + 4)) * (2 * (2 * w) + 1) + 6 * (n * (w + 1)) +
    n * (chirpCost H (2 * (2 * w)) + 2) + 200 * w + 200 +
    (6 * (n * (w + 1)) + n * (chirpCost H (2 * (2 * w)) + 2) + 6 * w * (n + n) +
      n * (inputCost H (2 * (2 * w)) + 2) + 12 * w + 30) +
    ((3 * w * (3 * n + 1) + 1) * H (3 * w * (3 * n + 1)) +
      n * (unpackCost H (2 * (2 * w)) + 2) + 400 * w * (n + 1) + 100)

/-- The step bound of the main procedure on `n` entries of `w` bits. -/
def dftBound (H : ℕ → ℕ) (n w : ℕ) : ℕ :=
  4 * ((n + 2) * (w + 1)) + 8 * w + 14 + pipeBound H n w + (100 * w * (n + 1) + 100) +
    (2 * (n * (w + 1)) + 2) + 1

theorem eq_emptyStacks {T A : ℕ} (S : Stacks T A) (h1 : S.inp = []) (h2 : S.out = [])
    (h3 : S.L = fun _ => []) (h4 : S.R = fun _ => []) : S = emptyStacks := by
  cases S
  simp_all [emptyStacks]

theorem cleanup_exec (main : DPr (Option M.P) (M.T + 50) M.Q M.A (M.U × B))
    {w p ω k : ℕ} (as : List ℕ) (Kc : List (Fin (M.A + 4))) (hKc : Kc.length = k)
    (hk : k ≤ 2 * (2 * w)) (v : HS (M.T + 50) M.Q M.A (M.U × B)) (S : Stacks (M.T + 50) M.A)
    (hPw : S.R (M.dreg 50 rPw) = binSyms w p) (hWm : S.R (M.dreg 50 rWm) = binSyms w ω) :
    ∃ v' : HS (M.T + 50) M.Q M.A (M.U × B), ∃ n, n ≤ 100 * w * (as.length + 1) + 100 ∧
      Exec (M.tab 50 B main) (hostCode (clearAll (M.dreg 50 rPw) (clearList.map (M.dreg 50))))
        (dmk v { S with R := M.pipeR w p ω k as Kc S.R } [] []) n
        (dmk v' { S with R := (fun j => if j ∈ M.dreg 50 rPw :: clearList.map (M.dreg 50) then []
          else M.pipeR w p ω k as Kc S.R j) } [] []) := by
  obtain ⟨v₃, -, e₃⟩ := clearAll_exec Empty.elim (M.dreg 50 rPw) (clearList.map (M.dreg 50))
    (by simp [clearList]) v { S with R := M.pipeR w p ω k as Kc S.R }
  exact ⟨v₃, _, M.cleanup_cost as Kc S.R hKc hk hPw hWm, exec_hostCode e₃ [] []⟩

theorem dftWork_exec (main : DPr (Option M.P) (M.T + 50) M.Q M.A (M.U × B))
    (H : ℕ → ℕ) (hH : Monotone H) (hT : ∀ n, M.time n ≤ (n + 1) * H n)
    {w p ω : ℕ} (as : List ℕ) (hw : 1 ≤ w)
    (hp1 : 2 ^ (w - 1) ≤ p) (hp : p < 2 ^ w) (hp2 : 2 ≤ p) (hω : ω < p) (has : ∀ a ∈ as, a < p)
    (v : HS (M.T + 50) M.Q M.A (M.U × B)) (S : Stacks (M.T + 50) M.A)
    (hinp : S.inp = []) (hout : S.out = []) (hL : S.L = fun _ => [])
    (hR : ∀ i, S.R (M.emb 50 i) = []) (hEnt : S.R (M.dreg 50 rEnt) = fieldSyms w as)
    (hPw : S.R (M.dreg 50 rPw) = binSyms w p) (hWm : S.R (M.dreg 50 rWm) = binSyms w ω)
    (hclean : ∀ j : Fin 50, j ≠ rEnt → j ≠ rPw → j ≠ rWm → S.R (M.dreg 50 j) = []) :
    ∃ v' : HS (M.T + 50) M.Q M.A (M.U × B), ∃ (Kc : List (Fin (M.A + 4))) (k n : ℕ),
      n ≤ pipeBound H as.length w + (100 * w * (as.length + 1) + 100) ∧
      Exec (M.tab 50 B main) (M.dftWork B) (dmk v S [] []) n
        (dmk v' { S with R := (fun j => if j ∈ M.dreg 50 rPw :: clearList.map (M.dreg 50) then []
          else M.pipeR w p ω k as Kc S.R j) } [] []) := by
  obtain ⟨v₂, Kc, k, n₂, -, hKc, -, hk2, hn₂, e₂⟩ := M.pipeline_exec B main H hH hT as hw
    hp1 hp hp2 hω has v S hinp hout (by intro j; rw [hL]) hR hEnt hPw hWm hclean [] []
  obtain ⟨v₃, n₃, hn₃, e₃⟩ := M.cleanup_exec B main as Kc hKc hk2 v₂ S hPw hWm
  have hpipe : n₂ ≤ pipeBound H as.length w := by
    refine hn₂.trans ?_
    simp only [pipeBound]
    gcongr
    · exact chirpCost_mono hH hk2
    · exact chirpCost_mono hH hk2
    · exact inputCost_mono hH hk2
    · exact unpackCost_mono hH hk2
  exact ⟨v₃, Kc, k, _, Nat.add_le_add hpipe hn₃, Exec.seq e₂ e₃⟩

theorem dftTail_exec (main : DPr (Option M.P) (M.T + 50) M.Q M.A (M.U × B))
    (H : ℕ → ℕ) (hH : Monotone H) (hT : ∀ n, M.time n ≤ (n + 1) * H n)
    (σ₀ : HS (M.T + 50) M.Q M.A (M.U × B)) {w p ω : ℕ} (as : List ℕ) (hw : 1 ≤ w)
    (hp1 : 2 ^ (w - 1) ≤ p) (hp : p < 2 ^ w) (hp2 : 2 ≤ p) (hω : ω < p) (has : ∀ a ∈ as, a < p)
    (v : HS (M.T + 50) M.Q M.A (M.U × B)) (S : Stacks (M.T + 50) M.A)
    (hinp : S.inp = []) (hout : S.out = []) (hL : S.L = fun _ => [])
    (hR : ∀ i, S.R (M.emb 50 i) = []) (hEnt : S.R (M.dreg 50 rEnt) = fieldSyms w as)
    (hPw : S.R (M.dreg 50 rPw) = binSyms w p) (hWm : S.R (M.dreg 50 rWm) = binSyms w ω)
    (hclean : ∀ j : Fin 50, j ≠ rEnt → j ≠ rPw → j ≠ rWm → S.R (M.dreg 50 j) = []) :
    ∃ n, n ≤ pipeBound H as.length w + (100 * w * (as.length + 1) + 100) +
        (2 * (as.length * (w + 1)) + 2) + 1 ∧
      Exec (M.tab 50 B main) (M.dftTail B σ₀) (dmk v S [] []) n
        (dmk σ₀ emptyStacks [] (encodeNatList ((List.range as.length).map
          (unpackVal p (ω ^ (as.length - 1) % p) w (pipeZ w p ω as))))) := by
  obtain ⟨v₃, Kc, k, n₃, hn₃, e₃⟩ := M.dftWork_exec B main H hH hT as hw hp1 hp hp2 hω has v S
    hinp hout hL hR hEnt hPw hWm hclean
  have hOut : (if M.dreg 50 rOut ∈ M.dreg 50 rPw :: clearList.map (M.dreg 50) then []
      else M.pipeR w p ω k as Kc S.R (M.dreg 50 rOut)) =
        (natSyms ((List.range as.length).map
          (unpackVal p (ω ^ (as.length - 1) % p) w (pipeZ w p ω as)))).reverse := by
    rw [ite_eq_right_iff.2 (fun h => absurd h (by simp [clearList]))]
    exact M.pipeR_out _ _ _
  obtain ⟨v₄, hu₄, e₄⟩ := print_exec (M.tab 50 B main) (M.dreg 50 rOut) _ [] v₃
    { S with R := (fun j => if j ∈ M.dreg 50 rPw :: clearList.map (M.dreg 50) then []
      else M.pipeR w p ω k as Kc S.R j) } hOut
  have hX' : ∀ y ∈ (List.range as.length).map
      (unpackVal p (ω ^ (as.length - 1) % p) w (pipeZ w p ω as)), y < 2 ^ w := by
    intro y hy
    rw [List.mem_map] at hy
    obtain ⟨j, -, rfl⟩ := hy
    exact (Nat.mod_lt _ (by omega)).trans hp
  have hnat := natSyms_length_le (A := M.A) _ hX'
  rw [List.length_map, List.length_range] at hnat
  refine ⟨_, ?_, Exec.cast (Exec.seq e₃ (Exec.seq e₄ (Exec.act _ _))) rfl ?_⟩
  · omega
  · show dmk σ₀ _ [] _ = dmk σ₀ _ [] _
    congr 1
    apply eq_emptyStacks
    · exact hinp
    · exact hout
    · exact hL
    · exact M.final_empty _ Kc S.R hR hclean
/-- The main procedure on an instance. -/
theorem dftMain_exec (H : ℕ → ℕ) (hH : Monotone H) (hT : ∀ n, M.time n ≤ (n + 1) * H n)
    (σ₀ : HS (M.T + 50) M.Q M.A (M.U × B)) (x : DFTInstance) :
    ∃ m, m ≤ dftBound H x.n (Nat.size x.p) ∧
      Exec (M.tab 50 B (M.dftMain B σ₀)) (M.dftMain B σ₀)
        (Store.only σ₀ .gin x.encode) m (Store.only σ₀ .gout (encodeNatList x.transform)) := by
  haveI := x.prime
  have hp2 : 2 ≤ x.p := x.prime.out.two_le
  have hw : 1 ≤ Nat.size x.p := Nat.size_pos.2 (by omega)
  have hp : x.p < 2 ^ Nat.size x.p := Nat.lt_size_self x.p
  have hp1 : 2 ^ (Nat.size x.p - 1) ≤ x.p := Nat.lt_size.1 (by omega)
  have hω : x.ω.val < x.p := ZMod.val_lt _
  have has : ∀ a ∈ List.ofFn (fun i => (x.a i).val), a < x.p := by
    intro a ha
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 ha
    exact ZMod.val_lt _
  have hlen : (List.ofFn fun i => (x.a i).val).length = x.n := List.length_ofFn
  rw [only_gin, only_gout]
  -- parse
  obtain ⟨v₁, S₁, hu₁, e₁, hEnt, hPw, hWm, hIn, hT', hother, hinp₁, hout₁, hL₁⟩ :=
    parse_exec (M.tab 50 B (M.dftMain B σ₀)) (a := M.dreg 50 rIn) (b := M.dreg 50 rEnt)
      (pr := M.dreg 50 rPw) (wr := M.dreg 50 rWm) (t := M.dreg 50 rT) (by simp) (Nat.size x.p)
      x.p x.ω.val (List.ofFn fun i => (x.a i).val) σ₀ emptyStacks rfl rfl rfl rfl rfl
  have hclean : ∀ j : Fin 50, j ≠ rEnt → j ≠ rPw → j ≠ rWm → S₁.R (M.dreg 50 j) = [] := by
    intro j h1 h2 h3
    by_cases hja : j = rIn
    · subst hja; exact hIn
    by_cases hjt : j = rT
    · subst hjt; exact hT'
    rw [hother _ (by simpa using hja) (by simpa using h1) (by simpa using h2) (by simpa using h3)
      (by simpa using hjt)]
    rfl
  have hR₁ : ∀ i, S₁.R (M.emb 50 i) = [] := fun i => by
    rw [hother _ (by simp) (by simp) (by simp) (by simp) (by simp)]; rfl
  obtain ⟨n₂, hn₂, e₂⟩ := M.dftTail_exec B (M.dftMain B σ₀) H hH hT σ₀
    (List.ofFn fun i => (x.a i).val) hw hp1 hp hp2 hω has v₁ S₁ hinp₁ hout₁ hL₁ hR₁ hEnt hPw
    hWm hclean
  rw [hlen, pipe_output x] at e₂
  rw [hlen] at hn₂
  refine ⟨_, ?_, Exec.cast (Exec.seq e₁ e₂) rfl rfl⟩
  have hpl : (encodeFixedList (Nat.size x.p)
      (x.p :: x.ω.val :: List.ofFn fun i => (x.a i).val)).length =
      (x.n + 2) * (Nat.size x.p + 1) := by
    rw [length_encodeFixedList]; simp [hlen]
  rw [hpl]
  simp only [dftBound]
  omega

end HostMultiplier

end IntegerMultBounds.MathlibTM2.DFT
