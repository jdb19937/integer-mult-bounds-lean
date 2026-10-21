module

public import IntegerMultBounds.MathlibTM2.M8.Global.Stage

/-! Centre reads through temporaries, independently of a particular slot allocation. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M8.Global.DesignB

noncomputable section
open IntegerMultBounds IntegerMultBounds.Networks Matrix
open IntegerMultBounds.MathlibTM2.M8.Local IntegerMultBounds.MathlibTM2.M8.Frames
open Classical

def centreBlockAt (slots : Fin 23 → ℕ) (reads : Fin 23 → List ℕ) (c : Fin 23) :
    List (FGate LW 23) :=
  ⟨ReversibleFanout.add (.inr c) (.inl (.aux (slots c))), starFrame c⟩ ::
    (reads c).map fun t => ⟨ReversibleFanout.add (.inl (.y t)) (.inr c), 0⟩

def centreReadsAt (slots : Fin 23 → ℕ) (reads : Fin 23 → List ℕ) (c : Fin 23) :
    Circuit.Program Reg (ZMod 2) :=
  (reads c).map fun t => ReversibleFanout.add (.y t) (.aux (slots c))

theorem centreBlockAt_run (slots : Fin 23 → ℕ) (reads : Fin 23 → List ℕ) (c : Fin 23) (d : LW → ZMod 2) (hz : d (.inr c) = 0) :
    (fun r => Circuit.run (gatesOf (centreBlockAt slots reads c)) d (.inl r)) =
        Circuit.run (centreReadsAt slots reads c) (fun r => d (.inl r)) ∧
      ∀ c', Circuit.run (gatesOf (centreBlockAt slots reads c)) d (.inr c') =
        if c' = c then d (.inl (.aux (slots c))) else d (.inr c') := by
  obtain ⟨s, hs⟩ : ∃ s, s = slots c := ⟨_, rfl⟩
  obtain ⟨Ts, hTs⟩ : ∃ Ts, Ts = reads c := ⟨_, rfl⟩
  obtain ⟨e, he⟩ : ∃ e : LW → ZMod 2,
      e = Function.update d (.inr c) (d (.inr c) + d (.inl (.aux s))) := ⟨_, rfl⟩
  have hgates : gatesOf (centreBlockAt slots reads c) =
      ReversibleFanout.add (.inr c) (.inl (.aux s)) ::
        Ts.map fun t => ReversibleFanout.add (.inl (.y t)) (.inr c) := by
    rw [hs, hTs]
    simp only [gatesOf, centreBlockAt, List.map_cons, List.map_map]
    rfl
  have hreads : (centreReadsAt slots reads c).map gL = Ts.map fun t => ReversibleFanout.add (.inl (.y t)) (.inl (.aux s)) := by
    rw [hs, hTs]
    simp only [centreReadsAt, List.map_map]
    rfl
  have hrun : Circuit.run (gatesOf (centreBlockAt slots reads c)) d =
      Circuit.run ((centreReadsAt slots reads c).map gL) e := by
    rw [hgates, Circuit.run_cons, ReversibleFanout.add_run, ← he, hreads]
    exact scatter_eq _ (.inr c) (.inl (.aux s)) (fun t h => by cases h) (fun t h => by cases h) e
      (by rw [he]; simp [hz])
  have he' : (fun r => e (.inl r)) = fun r => d (.inl r) := by
    funext r; rw [he]; simp
  obtain ⟨h1, h2⟩ := run_gL (centreReadsAt slots reads c) e
  refine ⟨by rw [hrun, h1, he'], fun c' => ?_⟩
  rw [hrun, h2, he, ← hs]
  by_cases h : c' = c
  · subst h; simp [hz]
  · simp [h]


theorem centreBlocksAt_run (slots : Fin 23 → ℕ) (reads : Fin 23 → List ℕ) : ∀ (cs : List (Fin 23)) (d : LW → ZMod 2), cs.Nodup →
    (∀ c ∈ cs, d (.inr c) = 0) →
      (fun r => Circuit.run ((cs.map (centreBlockAt slots reads)).flatMap gatesOf) d (.inl r)) =
        Circuit.run (cs.flatMap (centreReadsAt slots reads)) (fun r => d (.inl r))
  | [], d, _, _ => rfl
  | c :: cs, d, hnd, hz => by
    rw [List.nodup_cons] at hnd
    obtain ⟨h1, h2⟩ := centreBlockAt_run slots reads c d (hz c (by simp))
    have hz' : ∀ c' ∈ cs, Circuit.run (gatesOf (centreBlockAt slots reads c)) d (.inr c') = 0 := by
      intro c' hc'
      have hne : c' ≠ c := fun h => hnd.1 (by rw [← h]; exact hc')
      rw [h2, ite_eq_right hne]
      exact hz c' (List.mem_cons_of_mem _ hc')
    simp only [List.map_cons, List.flatMap_cons, Circuit.run_append]
    rw [centreBlocksAt_run slots reads cs _ hnd.2 hz', h1]

/-- A temporary implementation can replace a block of direct centre reads in any word. -/
theorem run_with_centres (slots : Fin 23 → ℕ) (reads : Fin 23 → List ℕ)
    (cs : List (Fin 23)) (hcs : cs.Nodup)
    (pre post : Circuit.Program Reg (ZMod 2)) (d : LW → ZMod 2)
    (hz : ∀ c ∈ cs, d (.inr c) = 0) :
    regs (Circuit.run (pre.map gL ++
      (cs.map (centreBlockAt slots reads)).flatMap gatesOf ++ post.map gL) d) =
      Circuit.run (pre ++ cs.flatMap (centreReadsAt slots reads) ++ post) (regs d) := by
  have hz' : ∀ c ∈ cs, Circuit.run (pre.map gL) d (.inr c) = 0 := by
    intro c hc
    rw [run_gL_inr]
    exact hz c hc
  simp only [Circuit.run_append]
  rw [regs_run_gL, show regs (Circuit.run
      ((cs.map (centreBlockAt slots reads)).flatMap gatesOf)
      (Circuit.run (pre.map gL) d)) = _ from
        centreBlocksAt_run slots reads cs _ hcs hz']
  exact congrArg (fun x => Circuit.run post (Circuit.run
    (cs.flatMap (centreReadsAt slots reads)) x)) (regs_run_gL pre d)

end
end IntegerMultBounds.MathlibTM2.M8.Global.DesignB
