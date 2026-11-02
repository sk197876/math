(** Federer (1969), 3.2.13, p. 251: the unit sphere
    has Hausdorff mass 2 Gamma(1/2)^m / Gamma(m/2),
    obtained from the angular integral at z_j= 1/2. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology lra ring.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  HausdorffMeasure SphereConstantIntegral GaussianProductIntegrand GammaAngularEvaluation EulerGamma
  EulerGammaHalfParameters RealPower MeasureUP MeasureIntegralUP MeasureSubsetIntegral MeasureIntegralUniqueness
  MeasureIntegralGraphEquivalence SummableRealFunctionUP ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Close Scope ereal_scope.

(** Source for [gaussian_half_angular_constant]: all coordinate
    exponents vanish at z_j= 1/2, so the angular integrand
    is one, Federer 3.2.13, p. 251. *)
Lemma gaussian_half_angular_constant (R:realType) m (u:R_n R m):
  gaussian_angular_integrand (fun _:'I_m=>(1/2:R)) u= 1%R.
Proof.
rewrite /gaussian_angular_integrand; apply:big1=>j _.
have hTwo:((2:R)!=0)%R by apply/eqP; lra.
have hExp:(2*(1/2:R)-1= 0)%R by rewrite div1r mulfV // subrr.
by rewrite hExp real_power_zero_exponent.
Qed.

(** Source for [gaussian_half_parameter_sum]: the parameter sum
    at z_j= 1/2 is m/2 in the first specialization of
    the Gamma quotient, Federer 3.2.13, p. 251. *)
Lemma gaussian_half_parameter_sum (R:realType) m:
  (\sum_(j:'I_m) (1/2:R))=(m%:R/2)%R.
Proof. by rewrite sumr_const card_ord -(mulr_natl (1/2:R) m) div1r. Qed.

(** Source for [hausdorff_unit_sphere_gamma_mass]: the displayed
    Gamma formula for H^(m-1)(S^(m-1)), Federer 3.2.13,
    p. 251, in every positive integer dimension. *)
Theorem hausdorff_unit_sphere_gamma_mass (R:realType) m (hm:(0<m)%N):
  @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R m)) (m-1)
    [set u|inner_norm (@euclidean_inner_productP R m) u= 1%R]=
    (2*(euler_gamma_half R)^+m/euler_gamma (@positive_dimension_half R m hm))%R%:E.
Proof.
pose z:=fun _:'I_m=>(1/2:R).
pose hz:=fun _:'I_m=>positive_real_half R.
have hAng:=@gamma_angular_integral_evaluation R m z hz hm.
have hSum:(\sum_j z j)=(m%:R/2)%R:=gaussian_half_parameter_sum R m.
have hGamma:euler_gamma (positive_coordinate_sum hm hz)=euler_gamma (@positive_dimension_half R m hm).
  move:(positive_coordinate_sum hm hz); rewrite hSum=>hP.
  exact:euler_gamma_proof_irrelevant.
have hProd:(\prod_j euler_gamma (hz j))=(euler_gamma_half R)^+m.
  by rewrite /hz /euler_gamma_half prodr_const card_ord.
rewrite hGamma hProd in hAng.
have hConst:=@sphere_constant_subset_integral R m (m-1) 1 1
  (gaussian_angular_integrand z) ltac:(by rewrite ler01) (fun u _=>gaussian_half_angular_constant u).
rewrite mul1e in hConst.
exact:measure_integral_unique hConst hAng.
Qed.
