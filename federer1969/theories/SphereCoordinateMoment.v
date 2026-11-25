(** Federer (1969), 3.2.13, p. 251: the exact
    coordinate moment of Hausdorff measure on the unit sphere,
    for every real t>-1 and every coordinate. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology lra.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric HausdorffMeasure
  EulerGamma EulerGammaHalfParameters GaussianProductIntegrand GammaAngularEvaluation
  SphereCoordinateParameters SphereCoordinateIntegrand PartialFunctionUP PartialFunctionBasic PartialZeroExtension
  RealPower MeasureSubsetIntegral MeasureIntegralGraphEquivalence SummableRealFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [positive_coordinate_moment_denominator]: positivity
    of (t+m)/2 under the full coordinate-moment hypotheses,
    Federer 3.2.13, p. 251. *)
Lemma positive_coordinate_moment_denominator (R:realType) m (t:R):
  (0<m)%N ->-1<t ->0<(t+m%:R)/2.
Proof.
move=>hm ht; have hM:(1<=(m%:R:R)) by rewrite ler1n.
apply:divr_gt0; lra.
Qed.

(** Source for [hausdorff_unit_sphere_coordinate_moment]: the
    displayed integral of |u_1|^t, Federer 3.2.13, p. 251,
    with the same Gamma quotient for any coordinate i and every
    real t>-1, including singular powers under the recorded zero convention. *)
Theorem hausdorff_unit_sphere_coordinate_moment (R:realType) m (hm:(0<m)%N)
    (i:'I_m) (t:R) (ht:-1<t):
  is_measure_subset_integral
    (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R m)) (m-1))
    [set u|inner_norm (@euclidean_inner_productP R m) u= 1]
    (real_total_integrand (fun u:R_n R m=>real_power `|u i| t))
    (2*euler_gamma (positive_coordinate_moment_parameter ht)*(euler_gamma_half R)^+(m-1)/
      euler_gamma (@positive_coordinate_moment_denominator R m t hm ht))%:E.
Proof.
pose z:=sphere_coordinate_parameters i t.
pose hz:=sphere_coordinate_parameters_positive i ht.
have hAng:=@gamma_angular_integral_evaluation R m z hz hm.
have hSum:(\sum_j z j)=(t+m%:R)/2:=sphere_coordinate_parameter_sum i t hm.
have hGamma:euler_gamma (positive_coordinate_sum hm hz)=
    euler_gamma (@positive_coordinate_moment_denominator R m t hm ht).
  move:(positive_coordinate_sum hm hz); rewrite hSum=>hP.
  exact:euler_gamma_proof_irrelevant.
have hProd:=@sphere_coordinate_gamma_product R m i t ht hz.
rewrite hGamma hProd mulrA in hAng.
apply:(measure_integral_graph_equivalent _ hAng)=>u v.
by rewrite !partial_function_zero_extension_graph !real_total_integrand_graph sphere_coordinate_angular_integrand.
Qed.
