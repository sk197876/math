(** Federer (1969), 2.2.12, p. 69: summing the successive losses gives a
    uniform bound for the measures of the pruned projections. We retain the
    printed telescoping argument with the half-error budget specified in
    MeasurePruningUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology.
From Federer Require Import SequenceSpace CoordinatePruningUP MeasurePruningUP
  GeometricErrorBudget.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [pruning_projection_prefix_loss]: supporting
    finite sum of the loss inequalities in Federer 2.2.12,
    p. 69. Consecutive geometric-tail differences telescope;
    the initial stage is included. *)
Lemma pruning_projection_prefix_loss (R : realType) (X : topologicalType)
    (gamma : set X -> \bar R) (Z : set (X * positive_sequence_space R))
    delta b F : is_measure_coordinate_pruning gamma Z delta b F -> forall k,
  gamma (fst @` Z) <= gamma (fst @` F k) +
    (geometric_error_tail delta 0 - geometric_error_tail delta k)%:E.
Proof.
move=> hF k; elim: k=> [|k ih].
- rewrite (coordinate_pruning_initial (measure_pruning_recursion hF)) subrr adde0.
  exact: lexx.
- have hs := ltW (measure_pruning_step_loss hF k).
  apply: le_trans ih _.
  have hh := leeD hs (lexx (geometric_error_tail delta 0 - geometric_error_tail delta k)%:E).
  rewrite -addeA -EFinD /geometric_error_budget in hh.
  have he : (geometric_error_tail delta k - geometric_error_tail delta k.+1 +
    (geometric_error_tail delta 0 - geometric_error_tail delta k) =
    geometric_error_tail delta 0 - geometric_error_tail delta k.+1)%R.
    by rewrite addrAC [(geometric_error_tail delta k + _)%R]addrC subrK.
  by rewrite he in hh.
Qed.

(** Source for [pruning_projection_uniform_lower_bound]: the
    uniform lower estimate for the pruned projections in Federer
    2.2.12, p. 69. Our half-error convention gives the
    stronger bound gamma(S)-delta/2. No measurability of S or
    of its pruned projections is assumed. *)
Lemma pruning_projection_uniform_lower_bound (R : realType) (X : topologicalType)
    (gamma : set X -> \bar R) (Z : set (X * positive_sequence_space R))
    delta b F : is_measure_coordinate_pruning gamma Z delta b F -> forall k,
  gamma (fst @` Z) - (delta / 2)%:E <= gamma (fst @` F k).
Proof.
move=> hF k; rewrite leeBlDr //.
apply: le_trans (pruning_projection_prefix_loss hF k) _.
apply: leeD; first exact: lexx.
rewrite lee_fin /geometric_error_tail expr0 mulr1 lerBlDr lerDl.
exact: geometric_error_tail_nonnegative k (ltW (measure_pruning_positive_error hF)).
Qed.
