module

public import IntegerMultBounds.MathlibTM2.Routing.SelectivePasses
public import IntegerMultBounds.MathlibTM2.Routing.MetadataClean

/-!
# Input configuration and fixed jobs for selective routing setup

The uniform caller supplies descriptors, binary dimensions and raw canonical
header bits on configuration tapes. These are input data, not installed host
counters or headers. The fixed 27-job installer copies descriptors, constructs
zero and unary counters, and installs the header separators. No program is
unrolled over a source list, address width, record count or record length.
-/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.MathlibTM2.Layer.CompactDigits
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget
open IntegerMultBounds.Networks.Shared50ModularControl (prime)

inductive SetupKey where
  | field (f : Fin 5)
  | desc (off : Off) (k : Fin 2)
  | block | records
  | header (c : Fin 2) (k : Fin 5)
  deriving DecidableEq

def setupKeys : List SetupKey :=
  (List.finRange 5).map .field ++
    ([Off.A, .Z, .Y, .YZ, .X].flatMap fun off => (List.finRange 2).map (.desc off)) ++
    [.block, .records] ++
    ((List.finRange 2).flatMap fun c => (List.finRange 5).map (.header c))

theorem setupKeys_nodup : setupKeys.Nodup := by decide +kernel

theorem setupKeys_mem (key : SetupKey) : key ∈ setupKeys := by
  cases key with
  | field f => simp [setupKeys]
  | desc off k => cases off <;> simp [setupKeys]
  | block => simp [setupKeys]
  | records => simp [setupKeys]
  | header c k => simp [setupKeys]

variable {T Q A : ℕ} {P U : Type}

noncomputable def SetupKey.target (H : SelectiveHost T) : SetupKey → Fin T
  | .field f => H.cf f
  | .desc off k => H.cb off (.desc k)
  | .block => H.ctr
  | .records => H.cnt
  | .header c k => H.swaps c (reg (selectiveSwapHd k))

/-- Binary widths/values annotate correctness and cost; the program ignores them. -/
noncomputable def setupJob (H : SelectiveHost T) (cfg : SetupKey → Fin T) (wb wm B M : ℕ) :
    SetupKey → MetadataJob T
  | .field f => .zero (cfg (.field f)) (H.cf f)
  | .desc off k => .copy (cfg (.desc off k)) (H.cb off (.desc k)) false
  | .block => .unary (cfg .block) H.ctr wb B
  | .records => .unary (cfg .records) H.cnt wm M
  | .header c k => .copy (cfg (.header c k)) (H.swaps c (reg (selectiveSwapHd k))) true

noncomputable def setupJobs (H : SelectiveHost T) (cfg : SetupKey → Fin T) (wb wm B M : ℕ) : List (MetadataJob T) :=
  setupKeys.map (setupJob H cfg wb wm B M)

theorem setupJob_src (H : SelectiveHost T) (cfg : SetupKey → Fin T) (wb wm B M : ℕ) (key : SetupKey) :
    (setupJob H cfg wb wm B M key).src = cfg key := by cases key <;> rfl

theorem setupJob_dst (H : SelectiveHost T) (cfg : SetupKey → Fin T) (wb wm B M : ℕ) (key : SetupKey) :
    (setupJob H cfg wb wm B M key).dst = key.target H := by cases key <;> rfl

/-- The setup program has fixed structure, independent of all numerical annotations. -/
noncomputable def selectiveSetup (H : SelectiveHost T) (cfg : SetupKey → Fin T) : Pr P T Q A U :=
  metadataInstall H.out H.tmp H.ctmp (setupJobs H cfg 0 0 0 0)

theorem selectiveSetup_eq (H : SelectiveHost T) (cfg : SetupKey → Fin T) (wb wm B M : ℕ) :
    (selectiveSetup H cfg : Pr P T Q A U) =
      metadataInstall H.out H.tmp H.ctmp (setupJobs H cfg wb wm B M) := by
  have he : ∀ keys : List SetupKey,
      (metadataInstall H.out H.tmp H.ctmp (keys.map (setupJob H cfg 0 0 0 0)) : Pr P T Q A U) =
        metadataInstall H.out H.tmp H.ctmp (keys.map (setupJob H cfg wb wm B M)) := by
    intro keys
    induction keys with
    | nil => rfl
    | cons key keys ih =>
      simp only [List.map_cons, metadataInstall]
      rw [ih]
      congr 1
      cases key <;> rfl
  exact he setupKeys

variable (p : Par) (X : ℕ) (hG : 0 < p.G) (hK : 0 < p.K)
  (active : Fin p.n → Bool) (s : Fin p.n → SlotSource p X)

def setupPayload (B M : ℕ) (hs : Fin 2 → Fin 5 → List Bool) : SetupKey → List (Fin (A + 4))
  | .field f => binSyms (selectiveLen p X f) 0
  | .desc off k => (patternTable (selectivePatterns p X hG hK active s off k)).flatten.map bitSymbol
  | .block => List.replicate B tick
  | .records => List.replicate M tick
  | .header c k => separator :: (hs c k).map bitSymbol

/-- Exact input configuration data, before any host metadata is installed. -/
structure SetupData (cfg : SetupKey → Fin T) (wb wm B M : ℕ) (hs : Fin 2 → Fin 5 → List Bool)
    (R : Fin T → List (Fin (A + 4))) : Prop where
  widths : ∀ f, (R (cfg (.field f))).length = selectiveLen p X f
  desc : ∀ off k, R (cfg (.desc off k)) =
    (patternTable (selectivePatterns p X hG hK active s off k)).flatten.map bitSymbol
  block : R (cfg .block) = binSyms wb B
  records : R (cfg .records) = binSyms wm M
  block_lt : B < 2 ^ wb
  records_lt : M < 2 ^ wm
  headers : ∀ c k, R (cfg (.header c k)) = (hs c k).map bitSymbol

/-- Each raw input word produces the exact installed payload. -/
theorem SetupData.contents (H : SelectiveHost T) {cfg : SetupKey → Fin T} {wb wm B M : ℕ}
    {hs : Fin 2 → Fin 5 → List Bool} {R : Fin T → List (Fin (A + 4))}
    (h : SetupData p X hG hK active s cfg wb wm B M hs R) (key : SetupKey) :
    (setupJob H cfg wb wm B M key).contents R = setupPayload p X hG hK active s B M hs key := by
  cases key with
  | field f => simpa [setupJob, MetadataJob.contents, setupPayload] using congrArg (fun n => binSyms n 0) (h.widths f)
  | desc off k => simpa [setupJob, MetadataJob.contents, setupPayload] using h.desc off k
  | block => rfl
  | records => rfl
  | header c k => simpa [setupJob, MetadataJob.contents, setupPayload] using congrArg (List.cons separator) (h.headers c k)

theorem SetupData.jobData (H : SelectiveHost T) {cfg : SetupKey → Fin T} {wb wm B M : ℕ}
    {hs : Fin 2 → Fin 5 → List Bool} {R : Fin T → List (Fin (A + 4))}
    (h : SetupData p X hG hK active s cfg wb wm B M hs R) (key : SetupKey) :
    (setupJob H cfg wb wm B M key).Data R := by
  cases key with
  | block => exact ⟨h.block_lt, h.block⟩
  | records => exact ⟨h.records_lt, h.records⟩
  | _ => trivial

end IntegerMultBounds.MathlibTM2.Routing
