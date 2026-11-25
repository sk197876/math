(** Degree-zero consequence of the comparisons in Federer (1969),
    2.10.2(1)–(2), p. 171. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import HausdorffMeasure HausdorffCountingMeasure
  HausdorffSphericalComparison CountingMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [spherical_zero_counting_measure]: supporting degree-zero
    corollary of Federer 2.10.2, p. 171 The factor 2^0=1 forces equality,
    with positive-radius generators throughout. *)
Theorem spherical_zero_counting_measure (R : realType) (X : metricType R) (A : set X) :
  @spherical_measure R X 0 A=@counting_measure R X A.
Proof.
have hlo := @hausdorff_measure_le_spherical_measure R X 0 A.
have hup := @spherical_measure_le_double_hausdorff_measure R X 0 A.
rewrite expr0 mul1e hausdorff_zero_counting_measure in hup.
rewrite hausdorff_zero_counting_measure in hlo.
by apply/eqP; rewrite eq_le hup hlo.
Qed.
