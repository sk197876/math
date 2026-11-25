(** Federer (1969), 3.2.13, p. 250: the
    unit-ball radial integral is sphere mass
    divided by m. The calculation retains
    infinite sphere mass until the finite source
    ball volume forces its finiteness. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric HausdorffMeasure
  BallCharacteristicSphereIntegral PolarUnitSphereIntegral PositiveRadialPowerIntegral CharacteristicFunctionUP
  PartialFunctionUP PartialFunctionBasic PartialZeroExtension PartialDensityProduct MeasureUP LebesgueScalarMeasure
  MeasureIntegralUP MeasureSubsetIntegral MeasureIntegralGraphEquivalence TotalNonnegativeExtendedScaleIntegral
  SummableRealFunctionUP ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [unit_ball_weighted_sphere_value]: exact
    radial value for the unit-ball test,
    supporting sphere normalization in Federer 3.2.13,
    p. 250. No finite sphere mass
    or inner-integrability premise is added. *)
Lemma unit_ball_weighted_sphere_value (R:realType) m (g:R_n R m->R) (r:R):
  is_characteristic_function [set x|(inner_norm (@euclidean_inner_productP R m) x<1)%R] g ->
  (0<r)%R ->partial_function_graph (weighted_unit_sphere_integral (real_total_integrand g)) r
    (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R m)) (m-1)
      [set x|inner_norm (@euclidean_inner_productP R m) x= 1%R]*
      (positive_unit_radial_power (m-1) r)%:E).
Proof.
move=>hg hr.
have hInner:=unit_ball_characteristic_unit_sphere_integral hg hr.
apply/partial_density_product_graph.
exists ((if (r<1)%R then 1%R else 0%R)%:E*
  @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R m)) (m-1)
    [set x|inner_norm (@euclidean_inner_productP R m) x= 1%R]), (r^+(m-1))%R%:E.
split=>//; split; first by [].
rewrite /positive_unit_radial_power hr /=.
case:ifP=>h; by rewrite ?mul1e ?mul0e ?mule0.
Qed.

(** Source for [unit_ball_polar_mass_integral]: the
    unit-ball test in the second polar
    identity, Federer 3.2.13, p. 250,
    has outer integral H^(m-1)(S)/m.
    The theorem permits infinite sphere mass and
    thus does not assume the conclusion it supports. *)
Lemma unit_ball_polar_mass_integral (R:realType) m (g:R_n R m->R):
  is_characteristic_function [set x|(inner_norm (@euclidean_inner_productP R m) x<1)%R] g ->
  is_measure_subset_integral (@lebesgue_scalar_measure R) [set r:R|(0<r)%R]
    (weighted_unit_sphere_integral (real_total_integrand g))
    (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R m)) (m-1)
      [set x|inner_norm (@euclidean_inner_productP R m) x= 1%R]*
      ((m-1).+1%:R^-1)%R%:E).
Proof.
move=>hg.
pose X:=inner_metric_space (@euclidean_inner_productP R m).
pose C:=@hausdorff_measure R X (m-1)
  [set x|inner_norm (@euclidean_inner_productP R m) x= 1%R].
pose f:=fun r:R=>((positive_unit_radial_power (m-1) r)%:E:extended_real_line R).
have hC:0<=C:=@measure_nonnegative R X _ (@hausdorff_measure_is_measure R X (m-1)) _.
have hf r:0<=f r by rewrite /f lee_fin; exact:positive_unit_radial_power_nonnegative.
have hI:=@total_nonnegative_extended_scale_integral R R (@lebesgue_scalar_measure R)
  (lebesgue_scalar_is_measure R) f _ C hf (@positive_unit_radial_power_integral R (m-1)) hC.
apply:measure_integral_graph_equivalent _ hI=>r z.
rewrite partial_function_zero_extension_graph.
change (C*f r=z <->((0<r)%R /\partial_function_graph
  (weighted_unit_sphere_integral (real_total_integrand g)) r z) \/(~(0<r)%R /\z= 0)).
case:(pselect ((0<r)%R))=>hr.
- have hValue:=@unit_ball_weighted_sphere_value R m g r hg hr.
  split=>hz.
  + left; split=>//; by rewrite -hz.
  + case:hz=>[[_ hz]|[hn _]]; last by exfalso; exact:hn hr.
    exact (partial_function_single_valued hValue hz).
- have hNot:~(0<r)%R:=hr.
  have hF:f r= 0.
    rewrite /f /positive_unit_radial_power.
    have h0:(0<r)%R=false by apply/negP.
    by rewrite h0.
  rewrite hF mule0; split=>hz.
  + right; split=>//; by symmetry.
  + case:hz=>[[h _]|[_ hz]]; first by exfalso; exact:hNot h.
    by symmetry.
Qed.
