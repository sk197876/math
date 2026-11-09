(** Federer (1969), 3.4.5, p. 321: actual analytic
    functions on the original lower axis of the example. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets.
From Federer Require Import RealNormUP GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerNorm
  HilbertFormCompactness NormAnalyticUP NormAnalyticDomain NormAnalyticOperations
  ScalarAffineAnalytic ScalarVectorLineAnalytic FlatExponentialSealed CartanCoefficientAnalytic
  CartanRationalArcAnalytic CartanCoordinateGeometry.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section LowerAxis.
Variable R:realType.
Local Notation X:=(R_n R 3).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R 3)).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R 3)).
Local Notation N:=(fun t:R^o=>`|t|).
Local Notation hN:=(@scalar_absolute_value_norm R).
Local Notation U:=([set v:X|v ord_max<1]).
Local Notation J:=([set z:R^o|z<1]).
Local Notation AN f:=(@norm_analytic R R^o R^o N N hN hN J f).

(** Source for [cartan_lower_axis_identity_analytic]: the
    original scalar coordinate is analytic on the lower
    axis, supporting 3.4.5, p. 321. *)
Lemma cartan_lower_axis_identity_analytic:AN (fun z=>z).
Proof.
have hWhole:@norm_analytic R R^o R^o N N hN hN setT (fun z=>z).
  move=>z _;have hh:=@scalar_affine_analytic_at R 1 0 z.
  apply:(norm_analytic_at_domain_agreement _ hh)=>y _;by rewrite mul1r addr0.
exact:(norm_analytic_open_restriction (fun z (_:J z)=>Logic.I) (@cartan_arc_domain_interior R) hWhole).
Qed.

(** Source for [cartan_lower_axis_coefficient_analytic]: the
    actual flat coefficient is analytic below its endpoint,
    supporting 3.4.5, p. 321. *)
Lemma cartan_lower_axis_coefficient_analytic:AN (fun z=>FlatExponential.value (1-z)).
Proof.
apply:(norm_analytic_open_restriction _ (@cartan_arc_domain_interior R)
  (@cartan_coefficient_off_endpoint_analytic R)).
move=>z hz;change (is_true (z!=1));by rewrite lt_eqF.
Qed.

(** Source for [cartan_lower_axis_restriction_analytic]: actual
    analytic functions on the original lower ambient domain
    have analytic restrictions to the original axis,
    supporting 3.4.5, p. 321. *)
Lemma cartan_lower_axis_restriction_analytic (P:X->R):
  @norm_analytic R X R^o NX N hNX hN U P ->AN (fun z=>P (cartan_axis_point z)).
Proof.
move=>hP.
have hWhole:=@scalar_vector_line_analytic R X NX hNX (@coordinate_basis R 3 ord_max).
have hAxis:=norm_analytic_open_restriction (fun z (_:J z)=>Logic.I) (@cartan_arc_domain_interior R) hWhole.
apply:(norm_analytic_compose_on _ hAxis hP)=>z hz.
by rewrite /= (cartan_axis_point_coordinates z).2.2.
Qed.
End LowerAxis.
