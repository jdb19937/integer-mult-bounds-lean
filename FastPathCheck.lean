module

import IntegerMultBounds.MathlibTM2
import IntegerMultBounds.MathlibTM2.Fast.Glue
import IntegerMultBounds.MathlibTM2.Fast.Input
import IntegerMultBounds.MathlibTM2.Fast.Output
import IntegerMultBounds.MathlibTM2.Host.SSMul
import IntegerMultBounds.MathlibTM2.Layer.LayerZ
import IntegerMultBounds.MathlibTM2.Layer.NodeZ
import IntegerMultBounds.MathlibTM2.Layer.Recurrence
import IntegerMultBounds.MathlibTM2.Layer.TopZ
import IntegerMultBounds.MathlibTM2.Mult.Moduli
import IntegerMultBounds.MathlibTM2.Mult.Pipeline
import IntegerMultBounds.MathlibTM2.Mult.Rounds
import IntegerMultBounds.MathlibTM2.Mult.SourceErr
import IntegerMultBounds.MathlibTM2.Mult.SynthErr
import IntegerMultBounds.MathlibTM2.Node.Body
import IntegerMultBounds.MathlibTM2.Theorem

/-! The theorem and the main intermediate results depend only on Lean's three standard axioms. -/

/-- info: 'IntegerMultBounds.MathlibTM2.statement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms IntegerMultBounds.MathlibTM2.statement

/-- info: 'IntegerMultBounds.MathlibTM2.Fast.statement_of_dispatch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms IntegerMultBounds.MathlibTM2.Fast.statement_of_dispatch

/-- info: 'IntegerMultBounds.MathlibTM2.Mult.Pipeline.pipeline_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms IntegerMultBounds.MathlibTM2.Mult.Pipeline.pipeline_correct

/-- info: 'IntegerMultBounds.MathlibTM2.Mult.Moduli.src_good' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms IntegerMultBounds.MathlibTM2.Mult.Moduli.src_good

/-- info: 'IntegerMultBounds.MathlibTM2.Mult.SourceErr.exact_product_of_components' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms IntegerMultBounds.MathlibTM2.Mult.SourceErr.exact_product_of_components

/-- info: 'IntegerMultBounds.MathlibTM2.Mult.SynthErr.synthMr_ringApprox' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms IntegerMultBounds.MathlibTM2.Mult.SynthErr.synthMr_ringApprox

/-- info: 'IntegerMultBounds.MathlibTM2.Mult.Rounds.fwd_rounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms IntegerMultBounds.MathlibTM2.Mult.Rounds.fwd_rounds

/-- info: 'IntegerMultBounds.MathlibTM2.Mult.Rounds.opp_rounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms IntegerMultBounds.MathlibTM2.Mult.Rounds.opp_rounds

/-- info: 'IntegerMultBounds.MathlibTM2.Layer.nodeM_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms IntegerMultBounds.MathlibTM2.Layer.nodeM_correct

/-- info: 'IntegerMultBounds.MathlibTM2.Layer.layerZ_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms IntegerMultBounds.MathlibTM2.Layer.layerZ_correct

/-- info: 'IntegerMultBounds.MathlibTM2.Layer.topZ_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms IntegerMultBounds.MathlibTM2.Layer.topZ_correct

/-- info: 'IntegerMultBounds.MathlibTM2.Layer.Recurrence.layer_cost_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms IntegerMultBounds.MathlibTM2.Layer.Recurrence.layer_cost_bound

/-- info: 'IntegerMultBounds.MathlibTM2.LayerMachine.nodeBody_exec_layerZ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms IntegerMultBounds.MathlibTM2.LayerMachine.nodeBody_exec_layerZ

/-- info: 'IntegerMultBounds.MathlibTM2.Host.ssMul_exec_log' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms IntegerMultBounds.MathlibTM2.Host.ssMul_exec_log

/-- info: 'IntegerMultBounds.MathlibTM2.Fast.digitRecords_exec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms IntegerMultBounds.MathlibTM2.Fast.digitRecords_exec

/-- info: 'IntegerMultBounds.MathlibTM2.Fast.carryOut_exec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms IntegerMultBounds.MathlibTM2.Fast.carryOut_exec
