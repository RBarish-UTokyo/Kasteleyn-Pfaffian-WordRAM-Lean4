module

import KasteleynSolution
import WordRAM
import Kasteleyn

/-!
# Axiom audit

Prints the axioms of the 5 compared theorems (stated in `KasteleynChallenge.lean`, proved by
`KasteleynSolution.lean`) and of 35 further theorems of the libraries. Every report must name only
`propext`, `Classical.choice` and `Quot.sound`. Run it with

    lake build && lake env lean Audit.lean
-/

-- The compared theorems
#print axioms Kasteleyn.orientation_exists
#print axioms Kasteleyn.pfaffian_formula
#print axioms Kasteleyn.matching_count
#print axioms Kasteleyn.linear_time_orientation
#print axioms Kasteleyn.edgeless_case

-- Further theorems of the libraries
#print axioms Kasteleyn.pf_sq
#print axioms Kasteleyn.pf_eq_sum_of_adj
#print axioms Kasteleyn.pf_signedAdj_eq
#print axioms Kasteleyn.pf_signedAdj_one_eq
#print axioms Kasteleyn.det_signedAdj_eq
#print axioms Kasteleyn.exists_det_signedAdj_eq
#print axioms Kasteleyn.RotationSystem.isKasteleyn_kasteleynOrientation
#print axioms Kasteleyn.RotationSystem.exists_isKasteleyn
#print axioms Kasteleyn.Orient.orient_runsWithin
#print axioms Kasteleyn.Orient.orient_rotationSystem
#print axioms WordRAM.Machine.Exec.mono_W
#print axioms WordRAM.Machine.Exec.embed
#print axioms WordRAM.Machine.Exec.lift
#print axioms WordRAM.Machine.Exec.lift_trunc
#print axioms WordRAM.Machine.Stmt.exec_realsToNat
#print axioms WordRAM.Machine.Stmt.runsWithin_realsToNat
#print axioms WordRAM.Machine.Stmt.compile_realsToNat_noReal
#print axioms WordRAM.Program.isWord_of_all
#print axioms WordRAM.Machine.Stmt.compile_wordOnly
#print axioms WordRAM.Machine.Stmt.isWord_compile_halt
#print axioms WordRAM.Machine.Exec.det
#print axioms WordRAM.Machine.Exec.toExecI_linLoopFree
#print axioms WordRAM.Machine.Exec.toExecI_whileLtR
#print axioms WordRAM.Machine.Exec.toExecI_stepInv
#print axioms WordRAM.Machine.Exec.toExecI_arithFree
#print axioms WordRAM.Machine.Exec.toExecI_whileLtN
#print axioms WordRAM.Machine.ModNat.ExecCmp.toNat
#print axioms WordRAM.Machine.ModNat.ExecCmp.toNat_consts
#print axioms WordRAM.Machine.ModNat.CmpOK.toNat
#print axioms WordRAM.Machine.ModNat.CmpOK.whileLtN
#print axioms WordRAM.Machine.ModNat.CmpOK.whileLtR
#print axioms WordRAM.Machine.ModNat.res_cmp
#print axioms WordRAM.Machine.Exec.hoist
#print axioms WordRAM.Machine.FixIter.exit
#print axioms WordRAM.Machine.Exec.liftSame
