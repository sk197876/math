(** Reuse the existing binary-cylinder probability measure for the
    project test of Federer 2.10.11, p. 176. A positive-radius ball
    has mass at most its radius, by its exact finite-prefix geometry. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import BinarySequenceCylinders BinaryCylinderPrefixLaws
  BinaryCylinderCost BinaryCylinderEnvelope BinaryPrefixMetric BinaryPrefixBalls
  MeasureUP MeasureBasic MetricClosedBalls.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [binary_prefix_probability]: the already proved
    binary-cylinder probability on the actual metric carrier; supporting
    the project test of Federer 2.10.11, p. 176. No probability
    or measure law is added as an assumption. *)
Definition binary_prefix_probability (R:realType):
    set (binary_prefix_metric R)->\bar R:=@binary_cylinder_measure R.

(** Source for [binary_prefix_probability_measure]: the existing
    covering measure supplies the measure laws for the project test
    of Federer 2.10.11, p. 176. *)
Lemma binary_prefix_probability_measure (R:realType):
  is_measure (@binary_prefix_probability R).
Proof. exact:binary_cylinder_measure_is_measure. Qed.

(** Source for [binary_prefix_probability_whole]: actual total
    mass one in the project test of Federer 2.10.11, p. 176,
    reusing the earlier compact finite-cylinder cover proof. *)
Lemma binary_prefix_probability_whole (R:realType):
  @binary_prefix_probability R setT= 1%E.
Proof. exact:binary_cylinder_measure_whole. Qed.

(** Source for [binary_prefix_probability_ball]: every positive
    radius ball has probability at most its radius. This bound
    supports the project test of the spherical variant in Federer
    2.10.11, p. 176; it is proved from actual cylinder geometry. *)
Lemma binary_prefix_probability_ball (R:realType)
    (a:binary_prefix_metric R) (r:R):0<r ->
  (@binary_prefix_probability R (metric_closed_ball a r)<=r%:E)%E.
Proof.
move=> hr;have [n [hn hsub]]:=binary_prefix_ball_small_cylinder a hr.
apply:le_trans (@measure_mono R (binary_prefix_metric R)
  (@binary_prefix_probability R) (binary_prefix_probability_measure R)
  _ _ hsub) _.
apply:le_trans (binary_cylinder_measure_bound R (binary_sequence_prefix n a)) _.
by rewrite /binary_cylinder_cost size_tuple -natrX lee_fin.
Qed.
