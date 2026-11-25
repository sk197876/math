(** Federer (1969), 3.4.5, p. 321: the actual
    analytic axis coordinate z/a(z) in the real cubic-cone
    proof of the example cited to Cartan (1957), pp. 97–99.
    Its first derivative at zero is proved directly. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormHigherCurveDerivativeUP NormedPrimitiveCell
  NormClassOneUP NormRegularity NormRegularityOperations NormAnalyticUP NormAnalyticLocal
  NormAnalyticDomain NormAnalyticOperations NormAnalyticScalarProducts ScalarAffineAnalytic
  ScalarReciprocalAnalytic FlatExponentialSealed FlatExponentialOrder CartanCoefficientAnalytic
  CartanRationalArcAnalytic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section AxisCoordinate.
Variable R:realType.
Local Notation N:=(fun t:R^o=>`|t|).
Local Notation hN:=(@scalar_absolute_value_norm R).
Local Notation A:=([set z:R^o|z<1]).
Local Notation AN f:=(@norm_analytic R R^o R^o N N hN hN A f).

(** Source for [cartan_axis_coordinate]: the actual
    axis coordinate that makes the adapted cubic equation
    homogeneous, supporting 3.4.5, p. 321. *)
Definition cartan_axis_coordinate (z:R):R:=z/FlatExponential.value (1-z).

(** Source for [cartan_axis_inverse_coefficient_analytic]:
    the reciprocal of the original positive coefficient
    is analytic throughout z<1, supporting the local
    coordinate change in 3.4.5, p. 321. *)
Lemma cartan_axis_inverse_coefficient_analytic:
  AN (fun z=>(FlatExponential.value (1-z))^-1).
Proof.
have hCoefficient:AN (fun z=>FlatExponential.value (1-z)).
  apply:(norm_analytic_open_restriction _ (@cartan_arc_domain_interior R)
    (@cartan_coefficient_off_endpoint_analytic R)).
  move=>z hz;change (is_true (z!=1));by rewrite lt_eqF.
apply:(norm_analytic_compose_on _ hCoefficient (@scalar_reciprocal_analytic R)).
move=>z hz;change (is_true (FlatExponential.value (1-z)!=0)).
have hp:0<FlatExponential.value (1-z) by rewrite flat_exponential_positive subr_gt0.
by rewrite gt_eqF.
Qed.

(** Source for [cartan_axis_coordinate_analytic]: the
    actual axis normalization is analytic on its
    original domain, supporting 3.4.5, p. 321. *)
Theorem cartan_axis_coordinate_analytic:AN cartan_axis_coordinate.
Proof.
have hIdWhole:@norm_analytic R R^o R^o N N hN hN setT (fun z=>z).
  move=>z _;have hAffine:=@scalar_affine_analytic_at R 1 0 z.
  apply:(norm_analytic_at_domain_agreement _ hAffine)=>y _;by rewrite mul1r addr0.
have hId:=norm_analytic_open_restriction (fun z (_:A z)=>Logic.I)
  (@cartan_arc_domain_interior R) hIdWhole.
exact:(norm_analytic_scalar_product hId cartan_axis_inverse_coefficient_analytic).
Qed.

(** Source for [cartan_axis_coordinate_origin]: the
    actual coordinate preserves the origin, supporting
    the cubic-cone argument in 3.4.5, p. 321. *)
Lemma cartan_axis_coordinate_origin:cartan_axis_coordinate 0=0.
Proof. by rewrite /cartan_axis_coordinate mul0r. Qed.

(** Source for [cartan_axis_coordinate_positive_slope]: its
    original linear coefficient at zero is positive,
    supporting the actual inverse change in 3.4.5, p. 321. *)
Lemma cartan_axis_coordinate_positive_slope:0<(FlatExponential.value (1:R))^-1.
Proof. by rewrite invr_gt0 flat_exponential_positive ltr01. Qed.

(** Source for [cartan_axis_coordinate_differential_origin]:
    the actual differential at zero multiplies by a(0)^-1,
    supporting the coordinate change in 3.4.5, p. 321.
    Continuity of the reciprocal proves the exact remainder. *)
Theorem cartan_axis_coordinate_differential_origin:
  has_norm_differential N N A cartan_axis_coordinate 0
    (@scalar_coefficient_linear_map R R^o ((FlatExponential.value (1:R))^-1:R^o)).
Proof.
pose g:=fun z:R=>(FlatExponential.value (1-z))^-1.
have hg:=norm_class_continuous (norm_analytic_class_all_orders
  cartan_axis_inverse_coefficient_analytic 0%N).
split;first exact:(@cartan_arc_domain_interior R 0 ltr01).
- exact:(scalar_coefficient_linear_bound hN _).
- move=>epsilon hEpsilon.
  have [r [hr hBound]]:=(hg 0 ltr01).2 epsilon hEpsilon.
  exists r;split;first exact:hr.
  move=>h hA hSmall.
  have hEstimate:=hBound h hA hSmall.
  rewrite add0r subr0 in hEstimate.
  change (is_true (`|(0+h)/FlatExponential.value (1-(0+h))-
    0/FlatExponential.value (1-0)-h*(FlatExponential.value 1)^-1|<=epsilon*`|h|)).
  rewrite add0r mul0r subr0 -mulrBr normrM mulrC.
  exact:(ler_wpM2r (normr_ge0 h) (ltW hEstimate)).
Qed.
End AxisCoordinate.
