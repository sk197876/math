(** Federer (1969), 3.4.8(10), p. 330:
    the formal polynomial derivative has its
    actual weighted finite analytic representative.
    Apply the shared pointed representative
    connection and the existing finite derivative
    evaluation expression. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP AnalyticGermRepresentatives AnalyticGermUP AnalyticGermRing
  AnalyticScalarsSealed PointedAnalyticPullbackUP PointedPolynomialRepresentative
  CommutativePolynomialUP CommutativePolynomialEvaluationUP FormalPolynomialDerivativeUP
  FormalDerivativeEvaluationExpression.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [pointed_polynomial_derivative_actual_representative]:
    the original W'_(m+1) has the
    displayed weighted coefficient representative,
    3.4.8(10), p. 330. The same
    original coefficient functions represent W
    and its derivative; the derivative
    has no independently chosen coefficients. *)
Theorem pointed_polynomial_derivative_actual_representative (R:realType) (X Y:lmodType R)
  (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
  (projection:Hom X Y)
  (E:{rmorphism [the comNzRingType of (@analytic_germ_ring R Y NY hNY 0)]->
    [the comNzRingType of (@analytic_germ_ring R X NX hNX 0)]})
  (xi:Hom X R^o) (fXi:@analytic_representative_type R X NX hNX 0)
  (T:comNzRingType)
  (embed:{rmorphism [the comNzRingType of (@analytic_germ_ring R Y NY hNY 0)]->T})
  (variable:T) (coefficient:T->nat->@analytic_germ_ring R Y NY hNY 0)
  (hT:is_commutative_polynomial_ring embed variable coefficient)
  (J:{rmorphism T->[the comNzRingType of (@analytic_germ_ring R X NX hNX 0)]})
  (W derivative:T) N (b:'I_N->@analytic_representative_type R Y NY hNY 0):
  is_pointed_analytic_germ_pullback projection E ->
  (forall x,analytic_representative_value fXi x = xi x) ->
  is_commutative_polynomial_evaluation embed variable E (analytic_germ fXi) J ->
  is_formal_polynomial_derivative coefficient W derivative ->
  (forall i,(N<=i)%N ->coefficient W i = 0) ->
  (forall i:'I_N,analytic_germ (b i) = coefficient W i) ->
  exists f:@analytic_representative_type R X NX hNX 0,
    (forall x,analytic_representative_value f x =
      \sum_(i<N) (i:nat)%:R*analytic_representative_value (b i) (projection x)*(xi x)^+(i:nat).-1) /\
    (analytic_germ f:@analytic_germ_ring R X NX hNX 0) = J derivative.
Proof.
move=>hE hXi hJ hDerivative hSupport hB.
have [f [hValues hGerm]]:=@pointed_finite_power_actual_representative R X Y NX NY hNX hNY
  projection E xi fXi N b (fun i=>(i:nat)%:R) (fun i=>(i:nat).-1) hE hXi.
exists f;split;first exact:hValues.
rewrite hGerm (@formal_derivative_evaluation_finite_expression
  [the comNzRingType of (@analytic_germ_ring R Y NY hNY 0)] T
  [the comNzRingType of (@analytic_germ_ring R X NX hNX 0)] embed variable coefficient
  hT E (analytic_germ fXi) J W derivative N hJ hDerivative hSupport).
apply:eq_bigr=>i _;by rewrite rmorph_nat hB.
Qed.
