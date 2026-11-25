(** Federer (1969), 3.2.13, p. 250: evaluate the angular
    coordinate integral by Cartesian Fubini followed by polar integration. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology lra ring.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric HausdorffMeasure
  EuclideanLebesgueDimensions EulerGamma EulerGammaGaussianPositive GammaSquareIntegrand GaussianProductIntegrand
  GammaGaussianProductIntegral GaussianAngularIntegral PolarUnitSphereFormula PolarUnitSphereIntegral
  LebesgueScalarMeasure RealSubsetIntegralGraph PartialFunctionUP PartialFunctionBasic PartialZeroExtension
  SummableRealFunctionUP SummableRealArithmetic MeasureIntegralUP MeasureSubsetIntegral
  MeasureIntegralGraphEquivalence MeasureIntegralUniqueness ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [positive_coordinate_sum]: positivity of sum(z)
    for positive coordinate parameters in Federer 3.2.13, p. 250. *)
Lemma positive_coordinate_sum (R:realType) m (z:'I_m->R):
  (0<m)%N ->(forall j,(0<z j)%R) ->(0<\sum_j z j)%R.
Proof.
move=>hm hz.
rewrite (bigD1 (Ordinal hm)) //= .
apply:lt_le_trans (hz (Ordinal hm)) _.
rewrite lerDl; apply:sumr_ge0=>j _; exact:ltW (hz j).
Qed.

(** Source for [gaussian_polar_angular_outer_integral]: the
    middle radial integral in Federer 3.2.13, p. 250,
    equals one half Gamma(sum(z)) times the actual angular integral. *)
Lemma gaussian_polar_angular_outer_integral (R:realType) m (z:'I_m->R)
    (hSum:(0<\sum_j z j)%R) (b:R):
  (0<m)%N ->
  is_measure_subset_integral
    (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R m)) (m-1))
    [set u|inner_norm (@euclidean_inner_productP R m) u= 1%R]
    (real_total_integrand (gaussian_angular_integrand z)) b%:E ->
  is_measure_subset_integral (@lebesgue_scalar_measure R) [set r:R|(0<r)%R]
    (weighted_unit_sphere_integral (real_total_integrand (gaussian_product_integrand z)))
    (b*(euler_gamma hSum/2))%R%:E.
Proof.
move=>hm hA.
pose q r:=if (0<r)%R then gamma_square_integrand (\sum_j z j) r else 0%R.
have hOn r:(0<r)%R ->q r=gamma_square_integrand (\sum_j z j) r.
  by move=>hr; rewrite /q hr.
have hOff r:~(0<r)%R ->q r= 0%R.
  move=>hr; have hNot:(0<r)%R=false by apply/negP.
  by rewrite /q hNot.
have hRad:=(@real_subset_integral_total R R (@lebesgue_scalar_measure R) [set r:R|(0<r)%R]
  (gamma_square_integrand (\sum_j z j)) q (euler_gamma hSum/2)%R%:E hOn hOff).1
  (euler_gamma_gaussian_positive_integral hSum).
have hScaled:=@real_total_integral_scale R R (@lebesgue_scalar_measure R) (lebesgue_scalar_is_measure R)
  q (euler_gamma hSum/2)%R b hRad.
apply:(measure_integral_graph_equivalent _ hScaled)=>r v.
rewrite real_total_integrand_graph partial_function_zero_extension_graph.
case:(pselect ((0<r)%R))=>hr.
- rewrite (hOn r hr).
  have hValue:=@gaussian_weighted_sphere_value R m z r b hm hr hA.
  split=>hv.
  + left; split=>//; by rewrite -hv.
  + case:hv=>[[_ hv]|[hn _]]; last by exfalso; exact:hn hr.
    exact:partial_function_single_valued hValue hv.
- rewrite (hOff r hr) mulr0.
  split=>hv.
  + right; split=>//; by symmetry.
  + case:hv=>[[h _]|[_ hv]]; first by exfalso; exact:hr h.
    by symmetry.
Qed.

(** Source for [gamma_angular_integral_evaluation]: the conclusion
    2B(z)= 2 product(Gamma(z_j))/Gamma(sum(z)), Federer 3.2.13,
    pp. 250–251, expressed as an actual finite sphere integral. *)
Theorem gamma_angular_integral_evaluation (R:realType) m (z:'I_m->R)
    (hz:forall j,(0<z j)%R) (hm:(0<m)%N):
  is_measure_subset_integral
    (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R m)) (m-1))
    [set u|inner_norm (@euclidean_inner_productP R m) u= 1%R]
    (real_total_integrand (gaussian_angular_integrand z))
    (2*(\prod_j euler_gamma (hz j))/euler_gamma (positive_coordinate_sum hm hz))%R%:E.
Proof.
have hSum:=positive_coordinate_sum hm hz.
have [b hA]:=gaussian_angular_integral_finite hz hm.
have hOuter:=gaussian_polar_angular_outer_integral hSum hm hA.
have hCartesian:=gamma_gaussian_product_integral hz.
have [a [hSource hPolar]]:=polar_unit_sphere_integral_formula hm
  (ex_intro _ (\prod_j euler_gamma (hz j))%:E hCartesian).
have hSame:=measure_integral_unique hSource hCartesian; rewrite hSame in hPolar.
have hEval:=EFin_inj (measure_integral_unique hOuter hPolar).
have hGamma:(0<euler_gamma hSum)%R:=euler_gamma_positive hSum.
have hB:b=(2*(\prod_j euler_gamma (hz j))/euler_gamma hSum)%R.
  have hMul:(b*euler_gamma hSum)%R=(2*(\prod_j euler_gamma (hz j)))%R by nra.
  have hQuot:=congr1 (fun v:R=>(v/euler_gamma hSum)%R) hMul.
  by rewrite mulfK ?gt_eqF in hQuot.
have hProof:hSum=positive_coordinate_sum hm hz:=Prop_irrelevance _ _.
rewrite hProof in hB; by rewrite -hB.
Qed.
