(** Federer (1969), 2.3.9, p. 79: outside X-A_n the successive distance is
    at most its measure gauge. The explicit common domain follows Federer's
    partial-function convention. Source context:
    PartialFunctionPointwiseLimitUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionUP PartialNormedArithmetic
  MeasureGauge MeasureConvergenceUP MeasureSummableIncrementExceptions.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_increment_good_point]: direct pointwise
    bound on A_n in Federer 2.3.9, p. 79. *)
Lemma measure_increment_good_point (R : realType) (X : choiceType)
    (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
    (mu : set X -> \bar R) (f : nat -> partial_function X (real_norm_metric_space hN)) n x :
  ~ measure_increment_exception mu N f n x ->
  (forall k, partial_function_domain (f k) x) /\ forall y z,
    partial_function_graph (f n.+1) x y -> partial_function_graph (f n) x z ->
    (mdist y z)%:E <= measure_normed_distance mu N (f n.+1) (f n).
Proof.
move=> hx; split.
- have hd : partial_sequence_common_domain f x.
    apply: contrapT=> hn; apply: hx; by left.
  move=> k; exact: hd k Logic.I.
- move=> y z hy hz; rewrite real_norm_metric_distanceE leNgt; apply/negP=> hn.
  apply: hx; right; exists (y-z)%R; split=> //.
  apply: (proj2 (partial_vector_subtract_graph _ _ _ _)); exists y,z; by split=> //; split.
Qed.
