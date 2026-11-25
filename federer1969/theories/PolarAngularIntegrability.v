(** Federer (1969), 3.2.13, p. 250: a finite polar
    integral with a strictly positive separated radial factor
    gives a finite angular integral. This supplies, rather than
    assumes, angular integrability for the Gamma product. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  EuclideanLebesgueDimensions HausdorffMeasure LebesgueScalarMeasure PolarUnitSphereFormula
  PolarUnitSphereIntegral PositiveRayFiniteValue RealSubsetFiniteScale MeasureUP MeasureIntegralUP
  MeasureIntegralUniqueness MeasureSubsetIntegral MeasureIntegralGraphEquivalence
  PartialFunctionUP PartialFunctionBasic PartialFunctionPrecomposition PartialZeroExtension PartialDensityProduct
  SummableRealFunctionUP ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [polar_angular_finite_integral]: the finite
    angular integral occurring in the separated polar evaluation,
    Federer 3.2.13, p. 250. The hypotheses specify actual
    radial separation; angular measurability or finiteness is not assumed. *)
Theorem polar_angular_finite_integral (R:realType) m
    (g h:R_n R m->R) (c:R->R) (a:R):
  (0<m)%N ->
  (forall r,(0<r)%R ->(0<c r)%R) ->
  (forall r u,(0<r)%R ->inner_norm (@euclidean_inner_productP R m) u= 1%R ->g (r*:u)=(c r*h u)%R) ->
  is_measure_integral (@euclidean_lebesgue_measure R m) (real_total_integrand g) a%:E ->
  exists b:R,is_measure_subset_integral
    (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R m)) (m-1))
    [set u|inner_norm (@euclidean_inner_productP R m) u= 1%R] (real_total_integrand h) b%:E.
Proof.
move=>hm hc hSep hI.
have [v [hSource hPolar]]:=polar_unit_sphere_integral_formula hm (ex_intro _ a%:E hI).
have hValue:=measure_integral_unique hSource hI.
rewrite hValue in hPolar.
have [r [w [hr [hw hFin]]]]:=positive_ray_summable_finite_value (ex_intro _ a hPolar).
have hWeighted:partial_function_graph (weighted_unit_sphere_integral (real_total_integrand g)) r w.
  exact:((@partial_function_zero_extension_on R (extended_real_line R) 0
    [set r:R|(0<r)%R] (weighted_unit_sphere_integral (real_total_integrand g)) r w hr).1 hw).
have [b [d [hb [hd hbd]]]]:=(partial_density_product_graph _ _ r w).1 hWeighted.
change ((r^+(m-1))%R%:E=d) in hd.
have hrp:(0<r^+(m-1))%R:=exprn_gt0 (m-1)%N hr.
have hrNe:(r^+(m-1)!= 0)%R:=lt0r_neq0 hrp.
have hProduct:(r^+(m-1))%R%:E*b=w by rewrite muleC hd.
have hInv:((r^+(m-1))^-1)%R%:E*w=b.
  by rewrite -hProduct muleA -EFinM mulVf // mul1e.
have hB:b=((r^+(m-1))^-1*fine w)%R%:E.
  by rewrite -hInv -(fineK hFin) -EFinM.
have hUnit:=(unit_sphere_dilation_integral_graph _ _ _).1 hb.
rewrite hB in hUnit.
have hReal:is_measure_subset_integral
    (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R m)) (m-1))
    [set u|inner_norm (@euclidean_inner_productP R m) u= 1%R]
    (real_total_integrand (fun u=>g (r*:u))) ((r^+(m-1))^-1*fine w)%R%:E.
  apply:(measure_integral_graph_equivalent _ hUnit)=>u z.
  rewrite !partial_function_zero_extension_graph.
  by [].
exists ((c r)^-1*((r^+(m-1))^-1*fine w))%R.
apply:(real_subset_integral_cancel_finite_scale
  (@hausdorff_measure_is_measure R (inner_metric_space (@euclidean_inner_productP R m)) (m-1))
  (lt0r_neq0 (hc r hr)) _ hReal)=>u hu.
exact:hSep r u hr hu.
Qed.
