(** Federer (1969), 3.2.13, p. 251: the Gamma
    formula for beta_t(m,1)^t, derived from the actual
    sphere moment and normalized Haar projection integral. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology lra ring.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  UnitSphereSpace UnitSphereOrthogonalAction UnitSphereCoordinatePower UnitSphereHaarIntegral
  ProjectionMomentCancellation ProjectionBetaOneHaarIntegral ProjectionBeta RealPower EulerGamma EulerGammaHalfParameters
  SphereCoordinateParameters SphereCoordinateMoment OrthogonalGroupTopology OrthogonalGroupHaarMeasure
  MeasureIntegralUniqueness.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [projection_moment_range]: the printed finite
    exponent range t>=1 implies the coordinate-moment condition t>-1,
    Federer 3.2.13, p. 251. *)
Lemma projection_moment_range (R:realType) (t:R):
  1<=t ->-1<t.
Proof. move=>ht; lra. Qed.

(** Source for [projection_beta_one_gamma_formula]: the printed
    Gamma quotient for beta_t(m,1)^t in Federer 3.2.13,
    p. 251, with only m>=1 and finite t>=1. *)
Theorem projection_beta_one_gamma_formula (R:realType) m (hm:(0<m)%N) (t:R)
    (ht:1<=t):
  real_power (@projection_beta R m 1 hm t%:E) t=
    euler_gamma (positive_coordinate_moment_parameter (projection_moment_range ht))*euler_gamma (@positive_dimension_half R m hm)/
    (euler_gamma (@positive_coordinate_moment_denominator R m t hm (projection_moment_range ht))*euler_gamma_half R).
Proof.
pose htm:=projection_moment_range ht.
have [mulS [invS [eS hS]]]:=orthogonal_group_restriction_exists (@euclidean_inner_productP R m) (@coordinate_basisP R m).
have [theta hTheta]:=orthogonal_normalised_haar_measure_exists hS.
pose x:=@euclidean_unit_sphere_point R m hm.
have ht0:0<t:=lt_le_trans ltr01 ht.
have hOrbit:=projection_beta_one_haar_integral hm hS x ht hTheta.
have hU:=unit_sphere_coordinate_power_compact (Ordinal hm) ht0.
have hCompare:=@unit_sphere_haar_integral R m hm mulS invS eS hS theta x
  (unit_sphere_coordinate_power (Ordinal hm) t) (real_power (@projection_beta R m 1 hm t%:E) t)
  hTheta hU hOrbit.
have hMoment:=@unit_sphere_coordinate_power_integral R m hm (Ordinal hm) t htm.
have hEq:=EFin_inj (measure_integral_unique hCompare hMoment).
have hHalf:0<euler_gamma_half R:=euler_gamma_positive (positive_real_half R).
have hDim:=euler_gamma_positive (@positive_dimension_half R m hm).
have hSum:=euler_gamma_positive (@positive_coordinate_moment_denominator R m t hm htm).
have hHalfNe:euler_gamma_half R!=0:=lt0r_neq0 hHalf.
have hDimNe:euler_gamma (@positive_dimension_half R m hm)!=0:=lt0r_neq0 hDim.
have hSumNe:euler_gamma (@positive_coordinate_moment_denominator R m t hm htm)!=0:=lt0r_neq0 hSum.
have hPred:(euler_gamma_half R)^+m=euler_gamma_half R*(euler_gamma_half R)^+(m-1).
  have hNat:m=(m-1).+1 by rewrite subn1 prednK.
  by rewrite {1}hNat exprS.
rewrite hPred mulrA in hEq.
have hPow:0<(euler_gamma_half R)^+(m-1):=exprn_gt0 (m-1)%N hHalf.
exact (projection_moment_quotient_cancel hHalf hPow hDim hSum hEq).
Qed.
