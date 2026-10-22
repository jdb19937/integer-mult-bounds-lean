module

public import IntegerMultBounds.MathlibTM2.Routing.HeaderOperands
public import IntegerMultBounds.MathlibTM2.Routing.HeaderValue

/-!
# Header callbacks on the actual live field bank

The target is an actual index counter. The metadata header and all callback
scratch are disjoint from the physical field bank. Counter increments therefore
preserve the callback invariant; each callback constructs and clears its own
header, with both operations charged.
-/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host

variable {T Q A nf W L : ℕ} {P U : Type}

/-- The only callback register shared with the actual counter bank is its target. -/
structure HeaderBank (cf : Fin nf → Fin T) (ι : PatternReg 2 → Fin T) (ft : Fin nf) : Prop where
  fields_inj : Function.Injective cf
  callback_inj : Function.Injective ι
  target : ι (.fld 1) = cf ft
  separate : ∀ r, r ≠ .fld 1 → ∀ f, ι r ≠ cf f

/-- Actual live counters, empty header, static descriptors and empty scratch. -/
def HeaderInv (len : Fin nf → ℕ) (cf : Fin nf → Fin T) (ι : PatternReg 2 → Fin T)
    (s : Fin 2 → Fin L → Option (Fin W))
    (R : Fin T → List (Fin (A + 4))) (i : ℕ) : Prop :=
  (∀ f, R (cf f) = binSyms (len f) (digit len f i)) ∧
  R (ι (.fld 0)) = [] ∧
  ∀ r : PatternReg 2, (∀ f, r ≠ .fld f) → r ≠ .st →
    R (ι r) = patternStatic A s r

def headerCodeCost (L W count : ℕ) : ℕ :=
  (6 * W + 6 * count + 1) + (patternCodeCost L W + (2 * W + 2))

private theorem sourceHeaderCost_fields (len : Fin nf → ℕ) (cf : Fin nf → Fin T)
    (fields : List (Fin nf)) (R : Fin T → List (Fin (A + 4)))
    (hlen : ∀ f ∈ fields, (R (cf f)).length = len f) :
    sourceHeaderCost R (fields.map cf) =
      6 * (fields.map len).sum + 6 * fields.length + 1 := by
  induction fields with
  | nil => simp [sourceHeaderCost]
  | cons f fs ih =>
    rw [List.map_cons, sourceHeaderCost, ih (fun g hg => hlen g (by simp [hg])),
      hlen f (by simp)]
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    omega

/-- Complete live-index callback contract on an unchanged physical field bank. -/
theorem headerCode_spec (body : P → Pr P T Q A U)
    {len : Fin nf → ℕ} {cf : Fin nf → Fin T} {ι : PatternReg 2 → Fin T} {ft : Fin nf}
    (bank : HeaderBank cf ι ft) (fields : List (Fin nf)) (o : ℕ)
    (hchain : HeaderChain len o fields) (hwidth : (fields.map len).sum = W)
    (ht : len ft = L) (s : Fin 2 → Fin L → Option (Fin W))
    {nd : ℕ} (C : CAuto A 3 nd) :
    CodeSpec body (headerPatternCode (fields.map cf) ι C) cf len (ι .st)
      (fun k => (∃ f, cf f = k) ∨ (∃ r, ι r = k)) (HeaderInv len cf ι s)
      (codeSel C)
      (fun i => C.eval L ![digit len ft i,
        patternValue (s 0) ((i / 2 ^ o) % 2 ^ W),
        patternValue (s 1) ((i / 2 ^ o) % 2 ^ W)])
      (headerCodeCost L W fields.length) where
  runs i v S hI := by
    have hword : (fields.map cf).flatMap S.R =
        binSyms W ((i / 2 ^ o) % 2 ^ W) := by
      rw [List.flatMap_map]
      have heq : (fun f => S.R (cf f)) =
          (fun f => binSyms (A := A) (len f) (digit len f i)) := funext hI.1
      change fields.flatMap (fun f => S.R (cf f)) = _
      rw [heq, headerValue len fields o i hchain, hwidth, binSyms_mod]
    have hfields : ∀ f ∈ fields.map cf,
        f ≠ ι (.fld 0) ∧ f ≠ ι .ts ∧ f ≠ ι .tm := by
      intro f hf
      obtain ⟨g, _, rfl⟩ := List.mem_map.mp hf
      exact ⟨(bank.separate _ (by simp) g).symm,
        (bank.separate _ (by simp) g).symm, (bank.separate _ (by simp) g).symm⟩
    obtain ⟨v', m, hu, hm, hc, he⟩ := headerPatternCode_exec body (fields.map cf) ι
      bank.callback_inj hfields s C _ (digit len ft i)
      (Nat.mod_lt _ (by positivity))
      (by rw [← ht]; exact Nat.mod_lt _ (by positivity)) v S hI.2.1 hword
      (by rw [bank.target, hI.1 ft, ht]) hI.2.2
    refine ⟨v', m, hu, ?_, hc, he⟩
    have hcost := sourceHeaderCost_fields len cf fields S.R
      (fun f _ => by rw [hI.1 f]; simp)
    simpa only [hcost, hwidth, headerCodeCost] using hm
  cf_inj := bank.fields_inj
  cf_Y := fun f => Or.inl ⟨f, rfl⟩
  digits := fun _ _ hI => hI.1
  frame := by
    intro R R' i hI hR
    refine ⟨fun f => ?_, ?_, fun r hr hs => ?_⟩
    · rw [hR _ (Or.inl ⟨f, rfl⟩)]; exact hI.1 f
    · rw [hR _ (Or.inr ⟨.fld 0, rfl⟩)]; exact hI.2.1
    · rw [hR _ (Or.inr ⟨r, rfl⟩)]; exact hI.2.2 r hr hs
  reidx := by
    intro R R' i j hI hfields hother
    refine ⟨hfields, ?_, fun r hr hs => ?_⟩
    · rw [hother _ (bank.separate _ (by simp))]; exact hI.2.1
    · rw [hother _ (bank.separate _ (hr 1))]; exact hI.2.2 r hr hs

end IntegerMultBounds.MathlibTM2.Routing
