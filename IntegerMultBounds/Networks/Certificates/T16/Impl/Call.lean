module

public import IntegerMultBounds.Networks.Certificates.T16.Impl.Word

/-! Reindexing programs and per-wire primitive blocks. A program whose wires lie in a set `R`,
renamed along a map injective on `R`, acts on the renamed wires exactly as the original program
acts on the pulled-back arrays and leaves every other wire unchanged. Blocks of primitive words
on distinct wires act pointwise. These are the bookkeeping steps of one local invocation: wrap
each register, run the word on the registers' families, unwrap each register. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.T16.Impl

open BinaryWalsh FramedCircuit

variable {ι κ : Type} [DecidableEq ι] [DecidableEq κ]
variable {S : Type*} [AddCommGroup S] [Module ℂ S] [Module ℚ S]
variable (ρ : Module.End ℂ (Arrays 73) →* Module.End ℂ S)

/-- The wires an instruction reads or writes. -/
def TInstr.wires : TInstr ι → List ι
  | .gate g => g.target :: g.terms.map Prod.fst
  | .prim w _ => [w]

/-- Rename the wires of an instruction. -/
def TInstr.rename (u : ι → κ) : TInstr ι → TInstr κ
  | .gate g => .gate ⟨u g.target, g.terms.map fun t => (u t.1, t.2)⟩
  | .prim w p => .prim (u w) p

/-- The arrays `y` on the renamed wires agree with `x` on `R`. -/
def Agrees (u : ι → κ) (R : Set ι) (y : κ → S) (x : ι → S) : Prop := ∀ w ∈ R, y (u w) = x w

omit [DecidableEq ι] [DecidableEq κ] [Module ℂ S] in
theorem terms_sum_rename (u : ι → κ) (R : Set ι) {y : κ → S} {x : ι → S}
    (h : Agrees u R y x) (terms : List (ι × ℚ)) (ht : ∀ t ∈ terms, t.1 ∈ R) :
    ((terms.map fun t => (u t.1, t.2)).map fun p => p.2 • y p.1).sum =
      (terms.map fun p => p.2 • x p.1).sum := by
  induction terms with
  | nil => rfl
  | cons t ts ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [h t.1 (ht t List.mem_cons_self), ih (fun t' h' => ht t' (List.mem_cons_of_mem _ h'))]

theorem run_rename (u : ι → κ) (R : Set ι) (hu : Set.InjOn u R) (i : TInstr ι)
    (hi : ∀ w ∈ i.wires, w ∈ R) {y : κ → S} {x : ι → S} (h : Agrees u R y x) :
    Agrees u R ((i.rename u).run ρ y) (i.run ρ x) ∧
      ∀ v, (∀ w ∈ R, u w ≠ v) → (i.rename u).run ρ y v = y v := by
  cases i with
  | gate g =>
    have htR : g.target ∈ R := hi _ List.mem_cons_self
    have hterms : ∀ t ∈ g.terms, t.1 ∈ R := fun t ht =>
      hi _ (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨t, ht, rfl⟩))
    refine ⟨fun w hw => ?_, fun v hv => ?_⟩
    · simp only [TInstr.rename, TInstr.run, moduleGate]
      by_cases hwt : w = g.target
      · subst hwt
        rw [Function.update_self, Function.update_self, h _ htR,
          terms_sum_rename u R h _ hterms]
      · have hne : u w ≠ u g.target := fun e => hwt (hu hw htR e)
        rw [Function.update_of_ne hne, Function.update_of_ne hwt, h w hw]
    · simp only [TInstr.rename, TInstr.run, moduleGate]
      rw [Function.update_of_ne (fun e => hv _ htR e.symm)]
  | prim w p =>
    have hwR : w ∈ R := hi w List.mem_cons_self
    refine ⟨fun w' hw' => ?_, fun v hv => ?_⟩
    · simp only [TInstr.rename, TInstr.run]
      by_cases hww : w' = w
      · subst hww
        rw [Function.update_self, Function.update_self, h _ hwR]
      · have hne : u w' ≠ u w := fun e => hww (hu hw' hwR e)
        rw [Function.update_of_ne hne, Function.update_of_ne hww, h w' hw']
    · simp only [TInstr.rename, TInstr.run]
      rw [Function.update_of_ne (fun e => hv _ hwR e.symm)]

/-- **Renaming.** A program on `R`, renamed injectively, acts on the renamed wires as the
original program and fixes every other wire. -/
theorem runT_rename (u : ι → κ) (R : Set ι) (hu : Set.InjOn u R) (prog : List (TInstr ι))
    (hp : ∀ i ∈ prog, ∀ w ∈ i.wires, w ∈ R) {y : κ → S} {x : ι → S} (h : Agrees u R y x) :
    Agrees u R (runT ρ (prog.map (TInstr.rename u)) y) (runT ρ prog x) ∧
      ∀ v, (∀ w ∈ R, u w ≠ v) → runT ρ (prog.map (TInstr.rename u)) y v = y v := by
  induction prog generalizing y x with
  | nil => exact ⟨h, fun _ _ => rfl⟩
  | cons i prog ih =>
    obtain ⟨h1, h2⟩ := run_rename ρ u R hu i (hp i List.mem_cons_self) h
    obtain ⟨h3, h4⟩ := ih (fun i' hi' => hp i' (List.mem_cons_of_mem _ hi')) h1
    refine ⟨h3, fun v hv => ?_⟩
    change runT ρ (prog.map (TInstr.rename u)) ((i.rename u).run ρ y) v = y v
    rw [h4 v hv, h2 v hv]

/-! ### Per-wire blocks -/

/-- Apply one primitive word to each listed wire. -/
def blocks (ws : List κ) (word : κ → List Prim) : List (TInstr κ) :=
  ws.flatMap fun w => (word w).map (TInstr.prim w)

end IntegerMultBounds.Networks.Certificates.T16.Impl
