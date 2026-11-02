(** Federer (1969), 2.2.12, p. 69: continuity from above for the closures of
    the decreasing pruned projections. The finite total measure makes that
    limit theorem applicable. Source context: RegularProjectionLoss.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology.
From Federer Require Import SequenceSpace CoordinatePruningUP CoordinatePruningBasic
  MeasurePruningUP PruningFiniteLoss PruningClosedProjectionLimit MeasureUP
  MeasureBasic MeasureContinuityAbove ExtendedRealLimitBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [pruned_closed_limit_measure_lower_bound]: direct
    lower estimate for gamma(C) in Federer 2.2.12, p. 69.
    Closures are measurable by hypothesis. The finite-stage loss
    estimate passes to their decreasing intersection by 2.1.3(5).
    The half-error convention gives gamma(S)-delta/2 as lower bound. *)
Theorem pruned_closed_limit_measure_lower_bound (R : realType) (X : topologicalType)
    (gamma : set X -> \bar R) (hm : is_measure gamma)
    (Z : set (X * positive_sequence_space R)) delta b F :
  (forall C : set X, closed C -> measure_measurable gamma C) ->
  gamma setT < +oo -> is_measure_coordinate_pruning gamma Z delta b F ->
  gamma (fst @` Z) - (delta / 2)%:E <= gamma (pruned_projection_closed_limit F).
Proof.
move=> hclosed htotal hF.
pose C k := closure (fst @` F k).
have hC k : measure_measurable gamma (C k) := hclosed _ (@closed_closure X (fst @` F k)).
have hmono n m : (n <= m)%N -> C m `<=` C n.
  move=> hnm; apply: closureS=> x [p hp <-]; exists p=> //.
  exact: (@coordinate_pruning_decreasing R X Z b F (measure_pruning_recursion hF) n m hnm p hp).
have hfin : gamma (C 0%N) < +oo.
  apply: le_lt_trans (_ : gamma (C 0%N) <= gamma setT) htotal.
  apply: (@measure_mono R X gamma hm)=> x hx; exact Logic.I.
have hlim := @measure_continuity_above R X gamma hm C hC hmono hfin.
apply: extended_order_limit_lower_bound hlim.2 _=> k.
apply: le_trans (pruning_projection_uniform_lower_bound hF k) _.
apply: (@measure_mono R X gamma hm); exact: subset_closure.
Qed.
