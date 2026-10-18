module

public import IntegerMultBounds.Networks.Certificates.T16.Impl.Lowering
public import IntegerMultBounds.Networks.Certificates.T16.Trace.Framed
public import IntegerMultBounds.Networks.Certificates.T16.TableauNative

/-! The native local words as programs of rational gates and primitives. Programs run on
arrays of any module `S` carrying a representation `ρ` of the 73-bit operators, such as the
column tensor powers of the layer machine; a primitive acts on its wire by `ρ` of its operator.
Every native label is framed by `ρ` of the lift of its exact canonical realization; every climb
or centre edge becomes the primitive word of its exact frame transition
(`Realization.exists_prims`), with as many child calls as its certified rank. The resulting
programs act on arbitrary register arrays by the framed execution of `Trace.forward_run` and
`Trace.backward_run`. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.T16.Impl

open BinaryWalsh BinaryPhase Streams Pauli FramedCircuit

/-! ### Primitive operators -/

/-- The operator of a primitive, as a linear map. -/
noncomputable def Prim.lin : Prim → Module.End ℂ (Arrays 73)
  | .kernel q v => BinaryWalsh.kernel q v
  | .perm G => permOp G
  | .diag φ => (phaseDiagonal φ).toLinearMap
  | .scale c => c • LinearMap.id

theorem Prim.lin_apply (p : Prim) (f : Arrays 73) : p.lin f = p.op f := by
  cases p <;> rfl

/-- The operator of a word, applied head first. -/
noncomputable def wordLin : List Prim → Module.End ℂ (Arrays 73)
  | [] => 1
  | p :: ps => wordLin ps * p.lin

theorem wordLin_apply (ps : List Prim) (f : Arrays 73) : wordLin ps f = wordOp ps f := by
  induction ps generalizing f with
  | nil => rfl
  | cons p ps ih =>
    change wordLin ps (p.lin f) = wordOp ps (p.op f)
    rw [ih, Prim.lin_apply]

theorem Lowers.lin {K : Realization} {ws : List Prim} (h : Lowers K ws) :
    lift9 K.scalar.toLinearMap = wordLin ws :=
  LinearMap.ext fun f => (h f).trans (wordLin_apply ws f).symm

/-! ### Programs -/

/-- One instruction: a rational gate or a primitive on one wire. -/
inductive TInstr (ι : Type) where
  | gate (g : Circuit.Gate ι ℚ)
  | prim (w : ι) (p : Prim)

variable {ι : Type} [DecidableEq ι]
variable {S : Type*} [AddCommGroup S] [Module ℂ S] [Module ℚ S]
variable (ρ : Module.End ℂ (Arrays 73) →* Module.End ℂ S)

noncomputable def TInstr.run : TInstr ι → (ι → S) → (ι → S)
  | .gate g, x => moduleGate g x
  | .prim w p, x => Function.update x w (ρ p.lin (x w))

/-- Run a program, head first. -/
noncomputable def runT : List (TInstr ι) → (ι → S) → (ι → S)
  | [], x => x
  | i :: is, x => runT is (i.run ρ x)

theorem runT_append (p q : List (TInstr ι)) (x : ι → S) :
    runT ρ (p ++ q) x = runT ρ q (runT ρ p x) := by
  induction p generalizing x with
  | nil => rfl
  | cons i p ih => exact ih _

theorem runT_prims (w : ι) (ps : List Prim) (x : ι → S) :
    runT ρ (ps.map (TInstr.prim w)) x = Function.update x w (ρ (wordLin ps) (x w)) := by
  induction ps generalizing x with
  | nil =>
    change x = Function.update x w (ρ 1 (x w))
    rw [map_one, Module.End.one_apply, Function.update_eq_self]
  | cons p ps ih =>
    simp only [List.map_cons, runT, TInstr.run]
    rw [ih, Function.update_self, Function.update_idem, wordLin, map_mul, Module.End.mul_apply]

/-- The number of child calls of a program. -/
def TInstr.isChild : TInstr ι → Bool
  | .gate _ => false
  | .prim _ p => p.isChild

def programChildren (p : List (TInstr ι)) : ℕ := (p.filter TInstr.isChild).length

omit [DecidableEq ι] in
theorem programChildren_append (p q : List (TInstr ι)) :
    programChildren (p ++ q) = programChildren p + programChildren q := by
  simp [programChildren, List.filter_append]

omit [DecidableEq ι] in
theorem programChildren_prims (w : ι) (ps : List Prim) :
    programChildren (ps.map (TInstr.prim w)) = childCount ps := by
  simp only [programChildren, childCount, ← List.countP_eq_length_filter, List.countP_map]
  rfl

/-! ### Frames and edges -/

/-- `ρ` of an equivalence, as an equivalence. -/
noncomputable def repEquiv (T : Arrays 73 ≃ₗ[ℂ] Arrays 73) : S ≃ₗ[ℂ] S :=
  LinearEquiv.ofLinearMap (ρ T.toLinearMap) (ρ T.symm.toLinearMap)
    (by
      rw [← Module.End.mul_eq_comp, ← map_mul,
        show T.toLinearMap * T.symm.toLinearMap = 1 from by ext f; simp, map_one]
      rfl)
    (by
      rw [← Module.End.mul_eq_comp, ← map_mul,
        show T.symm.toLinearMap * T.toLinearMap = 1 from by ext f; simp, map_one]
      rfl)

variable [IsScalarTower ℚ ℂ S]

/-- The frame of a native label: `ρ` of the lift of its exact canonical realization. -/
noncomputable def labelFrame (i : ℕ) : Frame ℚ S :=
  (repEquiv ρ (lift9Equiv (nativeRealization i).scalar)).restrictScalars ℚ

/-- The primitive word of the transition from label `a` to label `b`. -/
noncomputable def edgePrims (a b : ℕ) : List Prim :=
  Classical.choose (Realization.exists_prims (edgeRealization a b))

theorem edgePrims_lowers (a b : ℕ) : Lowers (edgeRealization a b) (edgePrims a b) :=
  (Classical.choose_spec (Realization.exists_prims (edgeRealization a b))).1

theorem childCount_edgePrims (a b : ℕ) :
    childCount (edgePrims a b) = Module.finrank Geometry.F (LinearMap.range
      (Tableau.bBlock (Tableau.nativeTableau a) (Tableau.nativeTableau b))) := by
  rw [edgePrims, (Classical.choose_spec (Realization.exists_prims (edgeRealization a b))).2.1,
    edgeRealization_width]

theorem edge_apply (a b : ℕ) (y : S) :
    labelFrame ρ b ((labelFrame ρ a).symm y) = ρ (wordLin (edgePrims a b)) y := by
  rw [← (edgePrims_lowers a b).lin]
  change ρ (lift9 (nativeRealization b).scalar.toLinearMap)
    (ρ (lift9 (nativeRealization a).scalar.symm.toLinearMap) y) = _
  have e : lift9 (nativeRealization b).scalar.toLinearMap *
      lift9 (nativeRealization a).scalar.symm.toLinearMap =
        lift9 (edgeRealization a b).scalar.toLinearMap :=
    LinearMap.ext fun f => lift9_comp _ _ f
  rw [← Module.End.mul_apply, ← map_mul, e]

/-- The program of one framed event. -/
noncomputable def implEvent : FramedEventTrace.Event ℕ ℕ ℚ → List (TInstr ℕ)
  | .edge i old next => (edgePrims old next).map (TInstr.prim i)
  | .gate g _ => [.gate g]
  | .clear i _ => [.gate (FramedEventTrace.clearGate i)]
  | .copy s t _ => [.gate (FramedEventTrace.copyGate s t)]

theorem implEvent_run (e : FramedEventTrace.Event ℕ ℕ ℚ) (x : ℕ → S) :
    runT ρ (implEvent e) x = execute (FramedEventTrace.instruction (labelFrame ρ) e) x := by
  cases e with
  | edge i old next =>
    rw [implEvent, runT_prims, ← edge_apply]
    rfl
  | gate g _ => rfl
  | clear i _ => rfl
  | copy s t _ => rfl

theorem impl_run (es : List (FramedEventTrace.Event ℕ ℕ ℚ)) (x : ℕ → S) :
    runT ρ (es.flatMap implEvent) x =
      FramedCircuit.run (FramedEventTrace.lower (labelFrame ρ) es) x := by
  induction es generalizing x with
  | nil => rfl
  | cons e es ih =>
    rw [List.flatMap_cons, runT_append, implEvent_run, ih]
    rfl

/-! ### The two local words -/

/-- The forward local word as a program. -/
noncomputable def forwardWord : List (TInstr ℕ) := (Trace.framed Trace.forwardEvents).flatMap implEvent

/-- The backward local word as a program. -/
noncomputable def backwardWord : List (TInstr ℕ) :=
  (Trace.framed Trace.backwardEvents).flatMap implEvent

theorem forwardWord_run (x : ℕ → S) :
    runT ρ forwardWord x = encode (fun i => labelFrame ρ (Trace.forwardFinal.label i))
      (moduleRun Trace.forwardProgram
        (decode (fun i => labelFrame ρ (Trace.forwardInitial.label i)) x)) := by
  rw [forwardWord, impl_run, Trace.forward_run]

theorem backwardWord_run (x : ℕ → S) :
    runT ρ backwardWord x = encode (fun i => labelFrame ρ (Trace.backwardFinal.label i))
      (moduleRun Trace.backwardProgram
        (decode (fun i => labelFrame ρ (Trace.backwardInitial.label i)) x)) := by
  rw [backwardWord, impl_run, Trace.backward_run]

/-! ### Child calls -/

/-- The certified rank of a native event: its climb or centre rank, else zero. -/
def eventRank : Trace.Event → ℕ
  | .climb _ _ _ _ r => r
  | .center _ _ _ r => r
  | _ => 0

theorem children_framed (es : List Trace.Event) (h : ∀ e ∈ es, Tableau.NativeRankGood e) :
    programChildren ((Trace.framed es).flatMap implEvent) = (es.map eventRank).sum := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    have ht := ih (fun e' he' => h e' (List.mem_cons_of_mem _ he'))
    have he := h e List.mem_cons_self
    simp only [List.map_cons, List.sum_cons]
    cases e with
    | scalar g =>
      cases g <;>
        simp only [Trace.framed, List.filterMap_cons, Trace.Event.framed, List.flatMap_cons,
          programChildren_append] at ht ⊢ <;>
        rw [ht] <;> rfl
    | climb ph r old next rank =>
      simp only [Trace.framed, List.filterMap_cons, Trace.Event.framed, List.flatMap_cons,
        programChildren_append, implEvent, programChildren_prims, childCount_edgePrims] at ht ⊢
      rw [ht, he]
      rfl
    | center i old next rank =>
      simp only [Trace.framed, List.filterMap_cons, Trace.Event.framed, List.flatMap_cons,
        programChildren_append, implEvent, programChildren_prims, childCount_edgePrims] at ht ⊢
      rw [ht, he]
      rfl
    | adapter _ _ _ =>
      simpa [Trace.framed, List.filterMap_cons, Trace.Event.framed, eventRank] using ht
    | residual _ _ _ _ =>
      simpa [Trace.framed, List.filterMap_cons, Trace.Event.framed, eventRank] using ht
    | phase _ =>
      simpa [Trace.framed, List.filterMap_cons, Trace.Event.framed, eventRank] using ht

theorem forward_rank_sum : (Trace.forwardEvents.map eventRank).sum = 5586 := by decide +kernel

theorem backward_rank_sum : (Trace.backwardEvents.map eventRank).sum = 5586 := by decide +kernel

/-- The forward word makes 5,586 child calls. -/
theorem forwardWord_children : programChildren forwardWord = 5586 := by
  rw [forwardWord, children_framed _ Tableau.native_forward_ranks, forward_rank_sum]

/-- The backward word makes 5,586 child calls. -/
theorem backwardWord_children : programChildren backwardWord = 5586 := by
  rw [backwardWord, children_framed _ Tableau.native_backward_ranks, backward_rank_sum]

end IntegerMultBounds.Networks.Certificates.T16.Impl
