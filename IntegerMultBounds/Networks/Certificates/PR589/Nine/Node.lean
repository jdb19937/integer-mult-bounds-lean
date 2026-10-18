module

public import IntegerMultBounds.Networks.Certificates.PR589.Nine.Bank
public import IntegerMultBounds.Networks.Certificates.PR589.DirtyEndpoint
public import IntegerMultBounds.Networks.FramedCircuit

/-!
# The scalar program of the nine-stage bit node

One replica of the nine-stage node has `8 · 111 = 888` data columns, column `b · 111 + t` being
port `t` of bank `b`, followed by `9 · 439` helper columns, column `888 + s · 439 + h` being
helper `h` of stage `s` (`global_k.py`, `mapper`).
* A sweep of stage `s` on pair `p` runs the selected word on its owner columns `owner s p rev`.
  The word's sources and targets are the two sides of the pair, swapped in reverse
  orientation, and its helpers are the stage's helper columns.
* A bridge `(d, s)` adds bank `2s` to bank `2d` and then bank `2d+1` to bank `2s+1`, port by port.
* The final exchange relabels the two sides of every pair (`exchangeCols`).

`node_identity` proves that the node's gates followed by the exchange are the identity on every
column, for arbitrary dirty streams. Each sweep acts on its pair as the word's dirty endpoint
(`sweep_bank`), so the bank-level statement `recipe_runBank` applies port by port.

The sweeps of both orientations use the forward word here. The physical reverse sweep runs the
reversed record stream, which has the same scalar effect over `F₂`; that, and the frames,
belong with the physical node.
-/

@[expose] public section

namespace IntegerMultBounds.Networks.Certificates.PR589.Nine

open FramedCircuit

variable {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]

/-! ### Renaming along an injection -/

/-- Rename the wires of a gate. -/
def renameGate (u : ℕ → ℕ) (g : Circuit.Gate ℕ (ZMod 2)) : Circuit.Gate ℕ (ZMod 2) :=
  ⟨u g.target, g.terms.map fun t => (u t.1, t.2)⟩

/-- All wires of a program lie below `n`. -/
def WiresBelow (n : ℕ) (p : List (Circuit.Gate ℕ (ZMod 2))) : Prop :=
  ∀ g ∈ p, g.target < n ∧ ∀ t ∈ g.terms, t.1 < n

theorem moduleRun_local (n : ℕ) (p : List (Circuit.Gate ℕ (ZMod 2))) (hp : WiresBelow n p)
    (x y : ℕ → E) (hxy : ∀ w < n, x w = y w) : ∀ w < n, moduleRun p x w = moduleRun p y w := by
  induction p generalizing x y with
  | nil => exact hxy
  | cons g gs ih =>
    have hg := hp g List.mem_cons_self
    apply ih (fun g' hg' => hp g' (List.mem_cons_of_mem _ hg'))
    intro w hw
    have hsum : (g.terms.map fun q => q.2 • x q.1).sum = (g.terms.map fun q => q.2 • y q.1).sum := by
      congr 1
      apply List.map_congr_left
      intro q hq
      rw [hxy q.1 (hg.2 q hq)]
    simp only [moduleGate, Function.update_apply]
    split_ifs with h
    · rw [hsum, hxy _ hg.1]
    · exact hxy w hw

/-- A program renamed along a map injective below `n` acts on the image as the program acts on
the pulled-back state, and leaves every other wire unchanged. -/
theorem moduleRun_rename (u : ℕ → ℕ) (n : ℕ) (hu : ∀ i < n, ∀ j < n, u i = u j → i = j)
    (p : List (Circuit.Gate ℕ (ZMod 2))) (hp : WiresBelow n p) (y : ℕ → E) :
    (∀ w < n, moduleRun (p.map (renameGate u)) y (u w) = moduleRun p (fun j => y (u j)) w) ∧
      ∀ c, (∀ w < n, u w ≠ c) → moduleRun (p.map (renameGate u)) y c = y c := by
  induction p generalizing y with
  | nil => exact ⟨fun _ _ => rfl, fun _ _ => rfl⟩
  | cons g gs ih =>
    have hg := hp g List.mem_cons_self
    have hgs : WiresBelow n gs := fun g' hg' => hp g' (List.mem_cons_of_mem _ hg')
    simp only [List.map_cons, moduleRun_cons]
    set y' := moduleGate (renameGate u g) y
    have hsum : ((renameGate u g).terms.map fun q => q.2 • y q.1).sum =
        (g.terms.map fun q => q.2 • (fun j => y (u j)) q.1).sum := by
      simp [renameGate, List.map_map, Function.comp_def]
    have hagree : ∀ w < n, y' (u w) = moduleGate g (fun j => y (u j)) w := by
      intro w hw
      simp only [y', moduleGate, Function.update_apply, renameGate]
      by_cases hwt : w = g.target
      · subst hwt
        simp only [↓reduceIte]
        rw [← hsum]
        rfl
      · have hne : u w ≠ u g.target := fun h => hwt (hu w hw g.target hg.1 h)
        simp [hne, hwt]
    have hother : ∀ c, (∀ w < n, u w ≠ c) → y' c = y c := by
      intro c hc
      simp only [y', moduleGate, renameGate]
      rw [Function.update_of_ne (Ne.symm (hc g.target hg.1))]
    obtain ⟨ih₁, ih₂⟩ := ih hgs y'
    refine ⟨fun w hw => ?_, fun c hc => (ih₂ c hc).trans (hother c hc)⟩
    rw [ih₁ w hw]
    exact moduleRun_local n gs hgs _ _ (fun j hj => hagree j hj) w hw

/-! ### The columns -/

/-- The owner column of word register `i` in the sweep of stage `s` on pair `p`. -/
def owner (s p : ℕ) (rev : Bool) (i : ℕ) : ℕ :=
  if i < 222 then (2 * p + (if rev then 1 - i / 111 else i / 111)) * 111 + i % 111
  else 888 + s * 439 + (i - 222)

theorem owner_injective (s p : ℕ) (hp : p < 4) (rev : Bool) :
    ∀ i < 661, ∀ j < 661, owner s p rev i = owner s p rev j → i = j := by
  intro i hi j hj h
  simp only [owner] at h
  cases rev <;> simp only [Bool.false_eq_true, ↓reduceIte] at h <;> split_ifs at h <;> omega

/-- The word as a gate list, all of whose wires lie below `661`. -/
def word : List (Circuit.Gate ℕ (ZMod 2)) := program.map RawGate.toCircuit

theorem word_wires : WiresBelow 661 word := by
  intro g hg
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hg
  obtain ⟨ht, hs⟩ := register_bounds r hr
  refine ⟨ht, fun t htm => ?_⟩
  simp only [RawGate.toCircuit, List.mem_map] at htm
  obtain ⟨i, hi, rfl⟩ := htm
  exact hs i hi

def sweepGates (s p : ℕ) (rev : Bool) : List (Circuit.Gate ℕ (ZMod 2)) :=
  word.map (renameGate (owner s p rev))

theorem moduleRun_append' (p q : List (Circuit.Gate ℕ (ZMod 2))) (x : ℕ → E) :
    moduleRun (p ++ q) x = moduleRun q (moduleRun p x) := by
  induction p generalizing x with
  | nil => rfl
  | cons g gs ih => exact ih _

variable {Ω : Type*}

/-- The word's dirty endpoint on any stream state, below `661`. -/
theorem word_endpoint (z : ℕ → Ω → ZMod 2) (w : ℕ) (hw : w < 661) :
    moduleRun word z w = if 111 ≤ w ∧ w < 222 then z w + z (w - 111) else z w := by
  let z' : ℕ → Ω → ZMod 2 := fun j => if j < 661 then z j else 0
  rw [moduleRun_local 661 word word_wires z z' (fun j hj => by simp [z', hj]) w hw]
  funext ω
  rw [moduleRun_pointwise]
  have h : (fun j => z' j ω) = extendInput (fun i : Fin 661 => z i ω) := by
    funext j
    by_cases hj : j < 661 <;> simp [z', extendInput, hj]
  rw [h, show w = (⟨w, hw⟩ : Fin 661).val from rfl, word, dirty_endpoint]
  split <;> simp

theorem sweep_run (s p : ℕ) (hp : p < 4) (rev : Bool) (y : ℕ → Ω → ZMod 2) :
    (∀ w < 661, moduleRun (sweepGates s p rev) y (owner s p rev w) =
      if 111 ≤ w ∧ w < 222 then y (owner s p rev w) + y (owner s p rev (w - 111))
      else y (owner s p rev w)) ∧
    ∀ c, (∀ w < 661, owner s p rev w ≠ c) → moduleRun (sweepGates s p rev) y c = y c := by
  obtain ⟨h1, h2⟩ := moduleRun_rename (owner s p rev) 661 (owner_injective s p hp rev) word
    word_wires y
  exact ⟨fun w hw => (h1 w hw).trans (word_endpoint _ w hw), h2⟩

/-- A sweep leaves every column that is not one of its targets unchanged. -/
theorem sweep_other (s p : ℕ) (hp : p < 4) (rev : Bool) (y : ℕ → Ω → ZMod 2) (c : ℕ)
    (hc : ∀ w, 111 ≤ w → w < 222 → owner s p rev w ≠ c) :
    moduleRun (sweepGates s p rev) y c = y c := by
  obtain ⟨h1, h2⟩ := sweep_run s p hp rev y
  by_cases hex : ∃ w < 661, owner s p rev w = c
  · obtain ⟨w, hw, rfl⟩ := hex
    rw [h1 w hw, ite_eq_right (fun h => hc w h.1 h.2 rfl)]
  · push_neg at hex
    exact h2 c hex

/-- A sweep adds the source port to the target port. -/
theorem sweep_target (s p : ℕ) (hp : p < 4) (rev : Bool) (y : ℕ → Ω → ZMod 2) (t : ℕ)
    (ht : t < 111) :
    moduleRun (sweepGates s p rev) y (owner s p rev (111 + t)) =
      y (owner s p rev (111 + t)) + y (owner s p rev t) := by
  obtain ⟨h1, _⟩ := sweep_run s p hp rev y
  rw [h1 (111 + t) (by omega), if_pos ⟨by omega, by omega⟩, Nat.add_sub_cancel_left]

theorem owner_target (s p : ℕ) (rev : Bool) (t : ℕ) (ht : t < 111) :
    owner s p rev (111 + t) = (2 * p + (if rev then 0 else 1)) * 111 + t := by
  simp only [owner]
  cases rev <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> split_ifs <;> omega

theorem owner_source (s p : ℕ) (rev : Bool) (t : ℕ) (ht : t < 111) :
    owner s p rev t = (2 * p + (if rev then 1 else 0)) * 111 + t := by
  simp only [owner]
  cases rev <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> split_ifs <;> omega

/-! ### Banks of one port -/

/-- The eight banks seen at port `t`. -/
def bankView (t : ℕ) (x : ℕ → Ω → ZMod 2) : ℕ → Ω → ZMod 2 := fun b => x (b * 111 + t)

theorem sweep_bank (s p : ℕ) (hp : p < 4) (rev : Bool) (x : ℕ → Ω → ZMod 2) (t : ℕ)
    (ht : t < 111) :
    bankView t (moduleRun (sweepGates s p rev) x) = stepBank 4 (bankView t x) (.sweep s p rev) := by
  funext b
  simp only [bankView]
  have hnot : ∀ c, c = b * 111 + t → (b ≠ 2 * p + (if rev then 0 else 1)) →
      ∀ w, 111 ≤ w → w < 222 → owner s p rev w ≠ c := by
    intro c hc hb w hw1 hw2 heq
    have := owner_target s p rev (w - 111) (by omega)
    rw [show 111 + (w - 111) = w by omega] at this
    rw [this] at heq
    cases rev <;> simp only [Bool.false_eq_true, ↓reduceIte] at hb heq <;> omega
  cases rev
  · simp only [stepBank, Bool.false_eq_true, ↓reduceIte, Function.update_apply]
    split_ifs with hb
    · subst hb
      have h := sweep_target s p hp false x t ht
      rw [owner_target s p false t ht, owner_source s p false t ht] at h
      simpa [bankView] using h
    · exact sweep_other s p hp false x _ (hnot _ rfl (by simpa using hb))
  · simp only [stepBank, ↓reduceIte, Function.update_apply]
    split_ifs with hb
    · subst hb
      have h := sweep_target s p hp true x t ht
      rw [owner_target s p true t ht, owner_source s p true t ht] at h
      simpa [bankView] using h
    · exact sweep_other s p hp true x _ (hnot _ rfl (by simpa using hb))

/-- Sweeps leave the helper columns and everything above them unchanged. -/
theorem sweep_high (s p : ℕ) (hp : p < 4) (rev : Bool) (x : ℕ → Ω → ZMod 2) (c : ℕ)
    (hc : 888 ≤ c) : moduleRun (sweepGates s p rev) x c = x c := by
  apply sweep_other s p hp rev x c
  intro w hw1 hw2 heq
  have := owner_target s p rev (w - 111) (by omega)
  rw [show 111 + (w - 111) = w by omega] at this
  rw [this] at heq
  cases rev <;> simp only [Bool.false_eq_true, ↓reduceIte] at heq <;> omega

/-! ### Bridges -/

def addGate (dst src : ℕ) : Circuit.Gate ℕ (ZMod 2) := ⟨dst, [(src, 1)]⟩

/-- Port by port, bank `a` += bank `b`, for the first `n` ports. -/
def shearBlock (a b n : ℕ) : List (Circuit.Gate ℕ (ZMod 2)) :=
  (List.range n).map fun t => addGate (a * 111 + t) (b * 111 + t)

theorem moduleGate_addGate (dst src : ℕ) (z : ℕ → E) :
    moduleGate (addGate dst src) z = Function.update z dst (z dst + z src) := by
  simp [moduleGate, addGate]

theorem shearBlock_succ (a b n : ℕ) (x : ℕ → E) :
    moduleRun (shearBlock a b (n + 1)) x =
      moduleGate (addGate (a * 111 + n) (b * 111 + n)) (moduleRun (shearBlock a b n) x) := by
  rw [shearBlock, List.range_succ, List.map_append, moduleRun_append']
  rfl

theorem shearBlock_run (a b : ℕ) (hab : a ≠ b) (n : ℕ) (hn : n ≤ 111) (x : ℕ → E) (c : ℕ) :
    moduleRun (shearBlock a b n) x c =
      if a * 111 ≤ c ∧ c < a * 111 + n then x c + x (c - a * 111 + b * 111) else x c := by
  induction n generalizing c with
  | zero => simp [shearBlock]
  | succ n ih =>
    rw [shearBlock_succ, moduleGate_addGate]
    have e1 := ih (by omega) (a * 111 + n)
    have e2 := ih (by omega) (b * 111 + n)
    have e3 := ih (by omega) c
    rw [ite_eq_right (show ¬(a * 111 ≤ a * 111 + n ∧ a * 111 + n < a * 111 + n) by omega)] at e1
    rw [ite_eq_right (show ¬(a * 111 ≤ b * 111 + n ∧ b * 111 + n < a * 111 + n) by omega)] at e2
    simp only [Function.update_apply]
    by_cases hc : c = a * 111 + n
    · subst hc
      rw [if_pos rfl, e1, e2, if_pos (show a * 111 ≤ a * 111 + n ∧ a * 111 + n < a * 111 + (n + 1)
        from ⟨by omega, by omega⟩), show a * 111 + n - a * 111 + b * 111 = b * 111 + n by omega]
    · rw [ite_eq_right hc, e3]
      by_cases h₁ : a * 111 ≤ c ∧ c < a * 111 + n
      · rw [if_pos h₁, if_pos (show a * 111 ≤ c ∧ c < a * 111 + (n + 1) from ⟨h₁.1, by omega⟩)]
      · rw [ite_eq_right h₁, ite_eq_right (show ¬(a * 111 ≤ c ∧ c < a * 111 + (n + 1)) by omega)]

def bridgeGates (d s : ℕ) : List (Circuit.Gate ℕ (ZMod 2)) :=
  shearBlock (2 * d) (2 * s) 111 ++ shearBlock (2 * s + 1) (2 * d + 1) 111

theorem bridge_bank (d s : ℕ) (c : ℤ) (hds : d ≠ s) (x : ℕ → Ω → ZMod 2) (t : ℕ) (ht : t < 111) :
    bankView t (moduleRun (bridgeGates d s) x) = stepBank 4 (bankView t x) (.bridge d s c) := by
  funext b
  have hY : ∀ b', moduleRun (shearBlock (2 * d) (2 * s) 111) x (b' * 111 + t) =
      if b' = 2 * d then x (b' * 111 + t) + x (2 * s * 111 + t) else x (b' * 111 + t) := by
    intro b'
    rw [shearBlock_run (2 * d) (2 * s) (by omega) 111 le_rfl]
    by_cases hb : b' = 2 * d
    · subst hb
      rw [if_pos (show 2 * d * 111 ≤ 2 * d * 111 + t ∧ 2 * d * 111 + t < 2 * d * 111 + 111 from
          ⟨by omega, by omega⟩), if_pos rfl,
        show 2 * d * 111 + t - 2 * d * 111 + 2 * s * 111 = 2 * s * 111 + t by omega]
    · rw [ite_eq_right (show ¬(2 * d * 111 ≤ b' * 111 + t ∧ b' * 111 + t < 2 * d * 111 + 111) by omega),
        ite_eq_right hb]
  simp only [bankView, bridgeGates, moduleRun_append', stepBank, Function.update_apply]
  rw [shearBlock_run (2 * s + 1) (2 * d + 1) (by omega) 111 le_rfl]
  by_cases h₁ : b = 2 * s + 1
  · subst h₁
    rw [if_pos (show (2 * s + 1) * 111 ≤ (2 * s + 1) * 111 + t ∧
        (2 * s + 1) * 111 + t < (2 * s + 1) * 111 + 111 from ⟨by omega, by omega⟩),
      show (2 * s + 1) * 111 + t - (2 * s + 1) * 111 + (2 * d + 1) * 111 = (2 * d + 1) * 111 + t by
        omega, hY, hY]
    simp only [show ¬(2 * s + 1 = 2 * d) by omega, show ¬(2 * d + 1 = 2 * d) by omega, ↓reduceIte]
  · rw [ite_eq_right (show ¬((2 * s + 1) * 111 ≤ b * 111 + t ∧ b * 111 + t < (2 * s + 1) * 111 + 111) by
        omega), hY, ite_eq_right h₁]
    by_cases h₂ : b = 2 * d
    · subst h₂
      rw [if_pos rfl]
    · simp only [h₂, ↓reduceIte]

theorem bridge_high (d s : ℕ) (hd : d < 4) (hs : s < 4) (hds : d ≠ s) (x : ℕ → Ω → ZMod 2) (c : ℕ)
    (hc : 888 ≤ c) : moduleRun (bridgeGates d s) x c = x c := by
  simp only [bridgeGates, moduleRun_append']
  rw [shearBlock_run (2 * s + 1) (2 * d + 1) (by omega) 111 le_rfl,
    shearBlock_run (2 * d) (2 * s) (by omega) 111 le_rfl,
    ite_eq_right (show ¬((2 * d) * 111 ≤ c ∧ c < (2 * d) * 111 + 111) by omega),
    ite_eq_right (show ¬((2 * s + 1) * 111 ≤ c ∧ c < (2 * s + 1) * 111 + 111) by omega)]

/-! ### The node -/

def eventGates : Event → List (Circuit.Gate ℕ (ZMod 2))
  | .sweep s p rev => sweepGates s p rev
  | .bridge d s _ => bridgeGates d s
  | .exchange => []

/-- The recipe without its final exchange. -/
def recipeBody : List Event := (recipe 4).dropLast

theorem recipe_split : recipe 4 = recipeBody ++ [.exchange] := by
  decide +kernel

/-- A sweep on a pair below four, or a bridge between two distinct pairs below four. -/
def bodyEvent : Event → Bool
  | .sweep _ p _ => decide (p < 4)
  | .bridge d s _ => decide (d < 4 ∧ s < 4 ∧ d ≠ s)
  | .exchange => false

theorem recipeBody_events : recipeBody.all bodyEvent = true := by
  decide +kernel

/-- The gates of one replica of the node: its sweeps and bridges, in recipe order. -/
def nodeGates : List (Circuit.Gate ℕ (ZMod 2)) := recipeBody.flatMap eventGates

/-- The final exchange relabels the two sides of every pair. -/
def exchangeCols (y : ℕ → Ω → ZMod 2) (c : ℕ) : Ω → ZMod 2 :=
  if c < 888 then y ((if c / 111 % 2 = 0 then c / 111 + 1 else c / 111 - 1) * 111 + c % 111)
  else y c

theorem event_bank (e : Event) (he : bodyEvent e = true) (x : ℕ → Ω → ZMod 2) (t : ℕ)
    (ht : t < 111) : bankView t (moduleRun (eventGates e) x) = stepBank 4 (bankView t x) e := by
  cases e with
  | sweep st p rev =>
      simp only [bodyEvent, decide_eq_true_eq] at he
      exact sweep_bank st p he rev x t ht
  | bridge d s c =>
      simp only [bodyEvent, decide_eq_true_eq] at he
      exact bridge_bank d s c he.2.2 x t ht
  | exchange => simp [bodyEvent] at he

theorem event_high (e : Event) (he : bodyEvent e = true) (x : ℕ → Ω → ZMod 2) (c : ℕ)
    (hc : 888 ≤ c) : moduleRun (eventGates e) x c = x c := by
  cases e with
  | sweep st p rev =>
      simp only [bodyEvent, decide_eq_true_eq] at he
      exact sweep_high st p he rev x c hc
  | bridge d s c' =>
      simp only [bodyEvent, decide_eq_true_eq] at he
      exact bridge_high d s he.1 he.2.1 he.2.2 x c hc
  | exchange => simp [bodyEvent] at he

theorem body_bank (es : List Event) (hes : es.all bodyEvent = true) (x : ℕ → Ω → ZMod 2) (t : ℕ)
    (ht : t < 111) : bankView t (moduleRun (es.flatMap eventGates) x) = runBank 4 es (bankView t x) := by
  induction es generalizing x with
  | nil => rfl
  | cons e es ih =>
    simp only [List.all_cons, Bool.and_eq_true] at hes
    rw [List.flatMap_cons, moduleRun_append', ih hes.2, event_bank e hes.1 x t ht]
    rfl

theorem body_high (es : List Event) (hes : es.all bodyEvent = true) (x : ℕ → Ω → ZMod 2) (c : ℕ)
    (hc : 888 ≤ c) : moduleRun (es.flatMap eventGates) x c = x c := by
  induction es generalizing x with
  | nil => rfl
  | cons e es ih =>
    simp only [List.all_cons, Bool.and_eq_true] at hes
    rw [List.flatMap_cons, moduleRun_append', ih hes.2, event_high e hes.1 x c hc]

/-- **The nine-stage node.** On arbitrary dirty streams, the node's sweeps and bridges followed
by the exchange relabeling are the identity on every column. -/
theorem node_identity (x : ℕ → Ω → ZMod 2) : exchangeCols (moduleRun nodeGates x) = x := by
  funext c
  by_cases hc : c < 888
  · have hb : c / 111 < 8 := by omega
    have ht : c % 111 < 111 := Nat.mod_lt _ (by norm_num)
    have hrun := congrFun (recipe_runBank (bankView (c % 111) x)) (c / 111)
    rw [recipe_split, runBank, List.foldl_append, List.foldl_cons, List.foldl_nil] at hrun
    simp only [stepBank, show c / 111 < 2 * 4 by omega, ↓reduceIte] at hrun
    rw [← runBank, ← body_bank recipeBody recipeBody_events x (c % 111) ht] at hrun
    simp only [exchangeCols, hc, ↓reduceIte]
    simp only [bankView] at hrun
    rw [nodeGates, hrun, Nat.div_add_mod' c 111]
  · simp only [exchangeCols, hc, ↓reduceIte]
    exact body_high recipeBody recipeBody_events x c (by omega)

end IntegerMultBounds.Networks.Certificates.PR589.Nine
