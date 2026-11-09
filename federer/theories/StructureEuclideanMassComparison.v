(** Federer (1969), 3.3.7, p. 294: apply the actual
    Euclidean differentiation context to local original-image ball bounds. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanLebesgueDimensions
  EuclideanApproximateContext EuclideanNoncenteredVitali EuclideanMetricSeparability
  EuclideanDirectionalLimitation DirectionalLimitationUP CenteredDensityGeometry
  StructureCenteredMassComparison MetricClosedBalls MeasureDerivationContext NullBallLocus.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [structure_euclidean_local_mass_comparison]: the
    exact measure comparison at the end of Federer 3.3.7, p. 294.
    The actual Euclidean Lebesgue measure has the required Vitali
    context and original directional geometry; every positive-radius
    ball has positive mass, including the positive R^0 atom. All
    reference hypotheses of 2.9.15 are derived, rather than assumed.
    The original E remains arbitrary and its outer mass may be infinite. *)
Theorem structure_euclidean_local_mass_comparison (R:realType) m
    (psi:set (inner_metric_space (@euclidean_inner_productP R m))-> \bar R)
    (E:set (inner_metric_space (@euclidean_inner_productP R m))) (C:R):
  is_derivation_measure psi ->0<C ->
  (forall x,E x ->exists delta:R,0<delta /\forall r:R,0<r ->r<delta ->
    (psi (metric_closed_ball x r)<=C%:E*euclidean_lebesgue_measure m (metric_closed_ball x r))%E) ->
  (psi E<=C%:E*euclidean_lebesgue_measure m E)%E.
Proof.
move=>hPsi hC hLocal.
have hThird:(0:R)<1/3 by rewrite divr_gt0 // ltr0n.
have hThirdRange : (0 < ((1:R)/3)%R <= 1/3)%R.
  apply/andP; split; [exact:hThird|exact:lexx].
have [zeta hDirectional]:=euclidean_directional_limitation m hThirdRange.
have hGeometry:is_centered_density_geometry (@euclidean_lebesgue_measure R m).
  right; split; first exact:euclidean_metric_separable R m.
  exists [set (@setT (inner_metric_space (@euclidean_inner_productP R m)))].
  split; first exact:countable1.
  split.
  - apply/seteqP; split; first by move=>x _.
    move=>x _; exists setT; first reflexivity; exact:I.
  - move=>A hA; change (A=setT) in hA; rewrite hA.
    by exists +oo%E,(1/3),zeta.
have hNotNull x:E x ->~measure_null_ball_points (@euclidean_lebesgue_measure R m) x.
  move=>_ [r [hr hZero]].
  have hPositive:=@euclidean_closed_ball_positive R m x r hr.
  by rewrite hZero ltxx in hPositive.
exact:(@structure_centered_local_mass_comparison R
  (inner_metric_space (@euclidean_inner_productP R m))
  (@euclidean_lebesgue_measure R m) psi _ E C
  (euclidean_approximate_context R m) hPsi hGeometry hC hNotNull hLocal).
Qed.
