(** Federer (1969), 3.4.8(10), p. 331:
    an original polynomial has an actual
    representative analytic on a full prefix
    cylinder. Select local coefficient witnesses
    and apply the existing polynomial-witness theorem. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormBoundedLinearTopology
  NormAnalyticUP AnalyticGermRepresentatives AnalyticGermUP AnalyticGermRing AnalyticGermRingLaws
  PointedAnalyticPullbackUP CommutativePolynomialUP CommutativePolynomialEvaluationUP
  FormalPolynomialDerivativeSealed AnalyticPrefixPolynomialWitnesses.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [pointed_polynomial_analytic_representative]:
    t_(m+1), s_(m+1) and the remaining
    polynomial numerators may be represented on
    p_m inverse(Y), 3.4.8(10), p. 331.
    Finite support, coefficient representatives and
    the neighbourhood are proved existence witnesses. *)
Theorem pointed_polynomial_analytic_representative (R:realType) (X Y:lmodType R)
  (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
  (projection:Hom X Y)
  (E:{rmorphism [the comNzRingType of (@analytic_germ_ring R Y NY hNY 0)]->
    [the comNzRingType of (@analytic_germ_ring R X NX hNX 0)]})
  (xi:Hom X R^o) (fXi:@analytic_representative_type R X NX hNX 0)
  (P:comNzRingType)
  (embed:{rmorphism [the comNzRingType of (@analytic_germ_ring R Y NY hNY 0)]->P})
  (variable:P) (coefficient:P->nat->@analytic_germ_ring R Y NY hNY 0)
  (hP:is_commutative_polynomial_ring embed variable coefficient)
  (J:{rmorphism P->[the comNzRingType of (@analytic_germ_ring R X NX hNX 0)]}) (W:P):
  is_pointed_analytic_germ_pullback projection E ->
  norm_bounded_linear NX NY projection ->norm_bounded_linear NX (fun t:R^o=>`|t|) xi ->
  (forall x,analytic_representative_value fXi x = xi x) ->
  is_commutative_polynomial_evaluation embed variable E (analytic_germ fXi) J ->
  exists (U:set Y) (f:@analytic_representative_type R X NX hNX 0),
    U 0 /\@open (real_norm_metric_space hNY) U /\
    (analytic_germ f:@analytic_germ_ring R X NX hNX 0) = J W /\
    @norm_analytic R X R^o NX (fun t:R^o=>`|t|) hNX (@scalar_absolute_value_norm R)
      (fun x=>U (projection x)) (analytic_representative_value f).
Proof.
move=>hE hProjection hXi hValues hJ.
have [N hSupport]:=polynomial_coefficients_finite hP W.
have hExists (i:'I_N):exists b:@analytic_representative_type R Y NY hNY 0,
    analytic_germ b = coefficient W i.
  exact:analytic_germ_has_representative.
have [b hB]:=choice hExists.
pose derivative:=@FormalPolynomialDerivative.value
  [the comNzRingType of (@analytic_germ_ring R Y NY hNY 0)] P embed variable coefficient hP W.
have hDerivative:=@FormalPolynomialDerivative.laws
  [the comNzRingType of (@analytic_germ_ring R Y NY hNY 0)] P embed variable coefficient hP W.
have [U [f [fD [hOrigin [hOpen [hCoefficients [hGerm [_ [hAnalytic _]]]]]]]]]:=
  @analytic_prefix_polynomial_actual_witnesses R X Y NX NY hNX hNY projection E xi fXi
    P embed variable coefficient hP J W derivative N b hE hProjection hXi hValues hJ hDerivative hSupport hB.
exists U,f;by split;[exact:hOrigin|split;[exact:hOpen|split]].
Qed.
