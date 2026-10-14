module

public import IntegerMultBounds.Machine.CountedSymbolCopy
public import IntegerMultBounds.Machine.NativeZeroStream
public import IntegerMultBounds.Machine.PlacementBankEndpoint
public import IntegerMultBounds.Machine.RecoverWorkspace
public import IntegerMultBounds.Machine.RecursiveChildQuotientsConstant

@[expose] public section
namespace IntegerMultBounds.Machine.NativePolynomialPadding
noncomputable section
open RecursiveChildQuotientsConstant (bits)

def bank (source destination : ℤ → Fin 6) (sourceHead destinationHead : ℤ)
    (span width deficit : ℕ) : Tapes 9 2 :=
  ⟨![sourceHead,destinationHead,1,1,1,0,0,0,0],
    ![source,destination,RadixZeroFill.encodedBinary (bits span),RadixZeroFill.encodedBinary (bits width),
      RadixZeroFill.encodedBinary (bits deficit),fun _ => blank,fun _ => blank,fun _ => blank,fun _ => blank]⟩

def copyMap : Fin 5 → Fin 9 := ![0,1,2,5,6]
theorem copyMap_injective : Function.Injective copyMap := by decide
def copySlots := InjectivePlacement.placement copyMap copyMap_injective (by decide : 5+4=9)
def zeroMap : Fin 7 → Fin 9 := ![1,3,5,6,4,7,8]
theorem zeroMap_injective : Function.Injective zeroMap := by decide
def zeroSlots := InjectivePlacement.placement zeroMap zeroMap_injective (by decide : 7+2=9)
def blockProgram := seq (Placement.placed (CountedSymbolCopy.program (alphabet := 2)) copySlots)
  (Placement.placed NativeZeroStream.program zeroSlots)
def blockCost (span width deficit : ℕ) :=
  7*span+11*(bits span).length+35+
    deficit*(14*width+22*(bits width).length+81)+11*(bits deficit).length+36

theorem runs_block (background destination : ℤ → Fin 6) (sourceHead destinationHead : ℤ)
    (symbols : List (Fin 6)) (span width deficit : ℕ) (spanLength : symbols.length = span) :
    HoareTime blockProgram
      (· = bank (putWord background sourceHead symbols) destination sourceHead destinationHead span width deficit)
      (· = bank (putWord background sourceHead symbols)
        (putWord destination destinationHead (symbols++NativeZeroStream.records width deficit))
        (sourceHead+span) (destinationHead+(symbols++NativeZeroStream.records width deficit).length) span width deficit)
      (blockCost span width deficit) := by
  let source := putWord background sourceHead symbols
  let before := bank source destination sourceHead destinationHead span width deficit
  let copied := bank source (putWord destination destinationHead symbols)
    (sourceHead+span) (destinationHead+span) span width deficit
  let finished := bank source (putWord destination destinationHead (symbols++NativeZeroStream.records width deficit))
    (sourceHead+span) (destinationHead+(symbols++NativeZeroStream.records width deficit).length) span width deficit
  have copyReady : Placement.active copySlots before = CountedSymbolCopy.bank source destination sourceHead destinationHead (bits span) := by
    rw [copySlots, InjectivePlacement.active_bank]
    unfold copyMap before bank CountedSymbolCopy.bank CountedSymbolCopy.payload CountedLoopHeaderClean.bank SharedBank.empty Tapes.append
    apply congrArg₂ Tapes.mk
    all_goals funext slot; fin_cases slot <;> rfl
  have copyEndpoint : Placement.replace copySlots before
      (CountedSymbolCopy.bank source (putWord destination destinationHead symbols)
        (sourceHead+symbols.length) (destinationHead+symbols.length) (bits span)) = copied := by
    apply InjectivePlacement.replace_eq copyMap copyMap_injective (by decide : 5+4=9) before copied
    · rw [InjectivePlacement.active_bank]
      unfold copyMap copied bank CountedSymbolCopy.bank CountedSymbolCopy.payload CountedLoopHeaderClean.bank SharedBank.empty Tapes.append
      apply congrArg₂ Tapes.mk
      all_goals funext slot; fin_cases slot <;> simp only [spanLength] <;> rfl
    · intro slot outside
      fin_cases slot <;> first | exact ⟨rfl,rfl⟩ | exact False.elim (outside 0 rfl) | exact False.elim (outside 1 rfl)
  have copiedRun := Placement.hoare_at (CountedSymbolCopy.runs background destination sourceHead destinationHead symbols (bits span)
    (by rw [RecursiveChildQuotientsConstant.bits_value, spanLength])) copySlots before copyReady
  have copyExact : HoareTime (Placement.placed (CountedSymbolCopy.program (alphabet := 2)) copySlots)
      (· = before) (· = copied) (7*span+11*(bits span).length+35) := by
    apply copiedRun.consequence (fun _ ready => ready) _ (by rw [spanLength])
    rintro current ⟨localBank, rfl, ready⟩
    exact ready.trans copyEndpoint
  have zeroReady : Placement.active zeroSlots copied = NativeZeroStream.bank
      (putWord destination destinationHead symbols) (destinationHead+span) (bits width) (bits deficit) := by
    rw [zeroSlots, InjectivePlacement.active_bank]
    unfold zeroMap copied bank NativeZeroStream.bank NativeZeroStream.bodyBank NativeZeroRecord.bank NativeZeroRecord.core
      CountedLoopHeaderClean.bank CountedLoopReuseAlphabet.one SharedBank.empty Tapes.append
    apply congrArg₂ Tapes.mk
    all_goals funext slot; fin_cases slot <;> rfl
  have zeroEndpoint : Placement.replace zeroSlots copied (NativeZeroStream.bank
      (putWord destination destinationHead (symbols++NativeZeroStream.records width deficit))
      (destinationHead+(symbols++NativeZeroStream.records width deficit).length) (bits width) (bits deficit)) = finished := by
    apply InjectivePlacement.replace_eq zeroMap zeroMap_injective (by decide : 7+2=9) copied finished
    · rw [InjectivePlacement.active_bank]
      unfold zeroMap finished bank NativeZeroStream.bank NativeZeroStream.bodyBank NativeZeroRecord.bank NativeZeroRecord.core
        CountedLoopHeaderClean.bank CountedLoopReuseAlphabet.one SharedBank.empty Tapes.append
      apply congrArg₂ Tapes.mk
      all_goals funext slot; fin_cases slot <;> rfl
    · intro slot outside
      fin_cases slot <;> first | exact ⟨rfl,rfl⟩ | exact False.elim (outside 0 rfl)
  have localZero := NativeZeroStream.append_runs destination destinationHead symbols (bits width) (bits deficit)
    width deficit (RecursiveChildQuotientsConstant.bits_value _) (RecursiveChildQuotientsConstant.bits_value _)
  rw [spanLength] at localZero
  have zeroPlaced := Placement.hoare_at localZero zeroSlots copied zeroReady
  have zeroExact : HoareTime (Placement.placed NativeZeroStream.program zeroSlots) (· = copied) (· = finished)
      (deficit*(14*width+22*(bits width).length+81)+11*(bits deficit).length+35) := by
    apply zeroPlaced.consequence (fun _ ready => ready) _ le_rfl
    rintro current ⟨localBank, rfl, ready⟩
    exact ready.trans zeroEndpoint
  unfold blockProgram blockCost
  exact (copyExact.seq zeroExact).consequence (fun _ ready => ready) (fun _ ready => ready) (by omega)

def padded (groups : List (List (Fin 6))) (width deficit : ℕ) :=
  groups.map (fun group => group++NativeZeroStream.records width deficit)
def word (symbols : List (Fin 6)) := putWord (fun _ => blank) 0 symbols
def test (symbols : Fin 9 → Fin 6) := decide (symbols 0 ≠ blank)
def streamProgram := whileLoop blockProgram test

private theorem test_end (done : List (Fin 6)) (destination : ℤ → Fin 6) (destinationHead : ℤ)
    (span width deficit : ℕ) :
    test (bank (word done) destination done.length destinationHead span width deficit).reads = false := by
  change decide (word done done.length ≠ blank) = false
  rw [word, putWord_outside _ _ _ _ (Or.inr (by simp))]
  rfl

private theorem test_group (done group : List (Fin 6)) (rest : List (List (Fin 6)))
    (destination : ℤ → Fin 6) (destinationHead : ℤ) (span width deficit : ℕ)
    (groupNonempty : group ≠ []) (nonblank : ∀ symbol ∈ group, symbol ≠ blank) :
    test (bank (word (done++(group::rest).flatten)) destination done.length destinationHead span width deficit).reads = true := by
  have view := congrFun (WordSegments.middle (fun _ => (blank : Fin 6)) 0 done group rest.flatten) (done.length : ℤ)
  cases group with
  | nil => exact False.elim (groupNonempty rfl)
  | cons symbol remaining =>
    simp only [zero_add, putWord_head] at view
    change decide (word (done++((symbol::remaining)::rest).flatten) done.length ≠ blank) = true
    apply decide_eq_true
    intro empty
    apply nonblank symbol (by simp)
    apply view.trans
    simpa [word, List.append_assoc] using empty

theorem runs_stream (groups : List (List (Fin 6))) (done : List (Fin 6))
    (destination : ℤ → Fin 6) (destinationHead : ℤ) (span width deficit : ℕ) (spanPositive : 0 < span)
    (groupLengths : ∀ group ∈ groups, group.length = span)
    (nonblank : ∀ group ∈ groups, ∀ symbol ∈ group, symbol ≠ blank) :
    HoareTime streamProgram
      (· = bank (word (done++groups.flatten)) destination done.length destinationHead span width deficit)
      (· = bank (word (done++groups.flatten)) (putWord destination destinationHead (padded groups width deficit).flatten)
        (done++groups.flatten).length (destinationHead+(padded groups width deficit).flatten.length) span width deficit)
      ((blockCost span width deficit+2)*groups.length) := by
  induction groups generalizing done destination destinationHead with
  | nil =>
    intro current equal
    subst current
    refine ⟨0, _, by simp, rfl, ?_, ?_⟩
    · exact while_step_exit blockProgram test _ (by simpa using test_end done destination destinationHead span width deficit)
    · simp [padded, putWord, Config.tapes, Tapes.start]
  | cons group rest inductionHypothesis =>
    have groupLength := groupLengths group (by simp)
    let source := word (done++(group::rest).flatten)
    have sourceView : putWord source done.length group = source := by
      simpa [source, word] using WordSegments.middle (fun _ => (blank : Fin 6)) 0 done group rest.flatten
    have bodyRun := runs_block source destination done.length destinationHead group span width deficit groupLength
    rw [sourceView] at bodyRun
    have sourceSame : word ((done++group)++rest.flatten) = source := by simp [source, List.append_assoc]
    have sourcePosition : ((done++group).length : ℤ) = done.length+span := by simp [groupLength]
    have tailRun := inductionHypothesis (done++group)
      (putWord destination destinationHead (group++NativeZeroStream.records width deficit))
      (destinationHead+(group++NativeZeroStream.records width deficit).length)
      (fun next member => groupLengths next (List.mem_cons_of_mem group member))
      (fun next member => nonblank next (List.mem_cons_of_mem group member))
    rw [sourceSame, sourcePosition] at tailRun
    intro current equal
    subst current
    obtain ⟨bodyElapsed, bodyConfig, bodyBound, bodyExecuted, bodyHalted, bodyEndpoint⟩ := bodyRun _ rfl
    obtain ⟨tailElapsed, finalConfig, tailBound, tailExecuted, finalHalted, finalEndpoint⟩ := tailRun _ bodyEndpoint
    have firstIteration := while_run_iteration blockProgram test _
      (test_group done group rest destination destinationHead span width deficit
        (by intro empty; rw [empty] at groupLength; simp at groupLength; omega) (nonblank group (by simp)))
      bodyExecuted bodyHalted
    refine ⟨bodyElapsed+2+tailElapsed, finalConfig, ?_, ?_, finalHalted, ?_⟩
    · simp only [List.length_cons]
      nlinarith
    · unfold streamProgram
      rw [run_add, firstIteration]
      exact tailExecuted
    · rw [putWord_append_forward] at finalEndpoint
      simpa only [source, padded, List.map_cons, List.flatten_cons, List.append_assoc,
        List.length_append, Nat.cast_add, add_assoc] using finalEndpoint

def program := seq (seq streamProgram (RecoverWorkspace.atProgram ReturnOrigin.program (0 : Fin 9)))
  (RecoverWorkspace.atProgram ReturnOrigin.program (1 : Fin 9))

theorem padded_nonblank (groups : List (List (Fin 6))) (width deficit : ℕ)
    (nonblank : ∀ group ∈ groups, ∀ symbol ∈ group, symbol ≠ blank) :
    ∀ symbol ∈ (padded groups width deficit).flatten, symbol ≠ blank := by
  intro symbol member
  obtain ⟨group, groupMember, symbolMember⟩ := List.mem_flatten.mp member
  obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp groupMember
  rcases List.mem_append.mp symbolMember with originalSymbol | zeroSymbol
  · exact nonblank original originalMember symbol originalSymbol
  · exact NativeZeroStream.nonblank width deficit symbol zeroSymbol

theorem runs (groups : List (List (Fin 6))) (span width deficit : ℕ) (spanPositive : 0 < span)
    (groupLengths : ∀ group ∈ groups, group.length = span)
    (nonblank : ∀ group ∈ groups, ∀ symbol ∈ group, symbol ≠ blank) :
    HoareTime program
      (· = bank (word groups.flatten) (fun _ => blank) 0 0 span width deficit)
      (· = bank (word groups.flatten) (word (padded groups width deficit).flatten) 0 0 span width deficit)
      ((blockCost span width deficit+2)*groups.length+groups.flatten.length+(padded groups width deficit).flatten.length+6) := by
  have streamRun := runs_stream groups [] (fun _ => blank) 0 span width deficit spanPositive groupLengths nonblank
  simp only [List.nil_append, List.length_nil, Nat.cast_zero, zero_add] at streamRun
  let streamed := bank (word groups.flatten) (word (padded groups width deficit).flatten)
    groups.flatten.length (padded groups width deficit).flatten.length span width deficit
  let sourceReturned := RecoverWorkspace.restored streamed (0 : Fin 9)
  have returnSource := RecoverWorkspace.return_at (0 : Fin 9) streamed groups.flatten
    (by intro symbol member; obtain ⟨group, groupMember, symbolMember⟩ := List.mem_flatten.mp member
        exact nonblank group groupMember symbol symbolMember) rfl rfl
  have returnDestination := RecoverWorkspace.return_at (1 : Fin 9) sourceReturned (padded groups width deficit).flatten
    (padded_nonblank groups width deficit nonblank)
    (by simp [sourceReturned, RecoverWorkspace.restored, SharedPlacementAlphabet.setTape, streamed, bank])
    (by simp [sourceReturned, RecoverWorkspace.restored, SharedPlacementAlphabet.setTape, streamed, bank, word])
  have endpoint : RecoverWorkspace.restored sourceReturned (1 : Fin 9) =
      bank (word groups.flatten) (word (padded groups width deficit).flatten) 0 0 span width deficit := by
    unfold sourceReturned RecoverWorkspace.restored SharedPlacementAlphabet.setTape streamed bank
    apply congrArg₂ Tapes.mk
    all_goals funext slot; fin_cases slot <;> rfl
  unfold program
  exact ((streamRun.seq returnSource).seq returnDestination).consequence
    (fun _ ready => ready) (fun _ ready => ready.trans endpoint) (by omega)

end
end IntegerMultBounds.Machine.NativePolynomialPadding
