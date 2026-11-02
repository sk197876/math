(** Federer (1969), 3.2.13, p. 250: actual finite
    angular integral and the corresponding weighted sphere value. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology ring.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  EuclideanLebesgueDimensions HausdorffMeasure EulerGamma GaussianProductIntegrand GammaGaussianProductIntegral
  GaussianPolarSeparation GaussianRadialExponent GammaSquareIntegrand PolarAngularIntegrability
  PolarUnitSphereIntegral RealSubsetFiniteScale PartialFunctionUP PartialFunctionBasic
  PartialFunctionPrecomposition PartialDensityProduct MeasureIntegralUP MeasureSubsetIntegral
  MeasureIntegralGraphEquivalence SummableRealFunctionUP ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [gaussian_angular_integral_finite]: finite
    integrability of the angular coordinate product defining 2B(z),
    Federer 3.2.13, p. 250. It follows from Cartesian
    Fubini and the actual polar theorem; it is not a hypothesis. *)
Lemma gaussian_angular_integral_finite (R:realType) m (z:'I_m->R)
    (hz:forall j,(0<z j)%R):
  (0<m)%N ->exists b:R,is_measure_subset_integral
    (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R m)) (m-1))
    [set u|inner_norm (@euclidean_inner_productP R m) u= 1%R]
    (real_total_integrand (gaussian_angular_integrand z)) b%:E.
Proof.
move=>hm.
exact:(@polar_angular_finite_integral R m (gaussian_product_integrand z)
  (gaussian_angular_integrand z) (gaussian_radial_factor z) (\prod_j euler_gamma (hz j))
  hm (fun r hr=>gaussian_radial_factor_positive z hr)
  (fun r u hr hu=>gaussian_polar_separation z hr hu) (gamma_gaussian_product_integral hz)).
Qed.

(** Source for [gaussian_weighted_sphere_value]: the middle
    radial integrand in the Gamma product computation, Federer
    3.2.13, p. 250, using the actual angular integral b. *)
Lemma gaussian_weighted_sphere_value (R:realType) m (z:'I_m->R) (r b:R):
  (0<m)%N ->(0<r)%R ->
  is_measure_subset_integral
    (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R m)) (m-1))
    [set u|inner_norm (@euclidean_inner_productP R m) u= 1%R]
    (real_total_integrand (gaussian_angular_integrand z)) b%:E ->
  partial_function_graph (weighted_unit_sphere_integral (real_total_integrand (gaussian_product_integrand z)))
    r (b*gamma_square_integrand (\sum_j z j) r)%R%:E.
Proof.
move=>hm hr hA.
pose H:=@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R m)) (m-1).
pose c:=gaussian_radial_factor z r.
have hc:(c!= 0)%R:=lt0r_neq0 (gaussian_radial_factor_positive z hr).
have hMul:=@real_subset_integral_multiply_finite_scale R
  [the choiceType of inner_metric_space (@euclidean_inner_productP R m)] H
  (@hausdorff_measure_is_measure R _ (m-1))
  [set u|inner_norm (@euclidean_inner_productP R m) u= 1%R]
  (fun u=>gaussian_product_integrand z (r*:u)) (gaussian_angular_integrand z) b c hc
  (fun u hu=>gaussian_polar_separation z hr hu) hA.
have hUnit:partial_function_graph (unit_sphere_dilation_integral (real_total_integrand (gaussian_product_integrand z)))
    r (c*b)%R%:E.
  apply/unit_sphere_dilation_integral_graph.
  apply:(measure_integral_graph_equivalent _ hMul)=>u v.
  by [].
apply/partial_density_product_graph; exists (c*b)%R%:E,(r^+(m-1))%R%:E.
split=>//; split; first by [].
rewrite -EFinM.
have hEq:((c*b)*r^+(m-1))%R=(b*(c*r^+(m-1)))%R by ring.
by rewrite hEq /c gaussian_weighted_radial_factor.
Qed.
