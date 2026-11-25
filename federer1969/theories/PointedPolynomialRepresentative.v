(** Federer (1969), 3.4.8(10), pp. 330–331:
    the original polynomial in prefix germs
    has its actual finite analytic representative.
    Connect the pointed prefix interface to
    the existing power, product, finite-sum
    and polynomial-evaluation laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP AnalyticGermRepresentatives AnalyticGermUP AnalyticGermRing
  AnalyticGermSealed AnalyticGermRingLaws AnalyticGermPowers AnalyticGermFiniteSum
  PointedAnalyticPullbackUP CommutativePolynomialUP CommutativePolynomialEvaluationUP
  CommutativePolynomialEvaluationLaws AnalyticScalarsUP AnalyticScalarsSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [pointed_finite_power_actual_representative]:
    finite weighted powers with original prefix
    coefficients have their actual analytic
    representatives and exact ring expression,
    supporting 3.4.8(10), pp. 330–331.
    Apply the existing power, product and
    finite-sum representative laws; weights and
    exponents remain arbitrary finite data. *)
Theorem pointed_finite_power_actual_representative (R:realType) (X Y:lmodType R)
  (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
  (projection:Hom X Y)
  (E:{rmorphism [the comNzRingType of (@analytic_germ_ring R Y NY hNY 0)]->
    [the comNzRingType of (@analytic_germ_ring R X NX hNX 0)]})
  (xi:Hom X R^o) (fXi:@analytic_representative_type R X NX hNX 0)
  N (b:'I_N->@analytic_representative_type R Y NY hNY 0)
  (weight:'I_N->R) (exponent:'I_N->nat):
  is_pointed_analytic_germ_pullback projection E ->
  (forall x,analytic_representative_value fXi x = xi x) ->
  exists f:@analytic_representative_type R X NX hNX 0,
    (forall x,analytic_representative_value f x =
      \sum_(i<N) weight i*analytic_representative_value (b i) (projection x)*(xi x)^+(exponent i)) /\
    (analytic_germ f:@analytic_germ_ring R X NX hNX 0) =
      \sum_(i<N) (@AnalyticScalars.map R X NX hNX 0 (weight i))*
        E (analytic_germ (b i))*(analytic_germ fXi:@analytic_germ_ring R X NX hNX 0)^+(exponent i).
Proof.
move=>hE hXi.
pose G:=[the comNzRingType of (@analytic_germ_ring R X NX hNX 0)].
have hPull i:=hE (b i).
pose pulled i:=projT1 (cid (hPull i)).
have hPulled i:=projT2 (cid (hPull i)).
have hPower i:=@analytic_representative_power_exists R X NX hNX 0 fXi (exponent i).
pose power i:=projT1 (cid (hPower i)).
have hPowered i:=projT2 (cid (hPower i)).
pose constant i:=@analytic_constant_representative R X NX hNX 0 (weight i).
pose base i:=@analytic_multiply_representatives R X NX hNX 0 (pulled i) (power i).
pose term i:=@analytic_multiply_representatives R X NX hNX 0 (constant i) (base i).
pose terms:=map (fun i:'I_N=>term i) (enum 'I_N).
have [f [hValues hGerm]]:=@analytic_finite_sum_representative R X NX hNX 0 terms.
exists f;split.
- move=>x;rewrite hValues /terms big_map -[RHS]big_enum.
  apply:eq_bigr=>i _.
  change (weight i*(analytic_representative_value (pulled i) x*analytic_representative_value (power i) x) =
    weight i*analytic_representative_value (b i) (projection x)*(xi x)^+(exponent i)).
  by rewrite (hPulled i).2 (hPowered i).1 hXi mulrA.
- rewrite hGerm /terms big_map -[RHS]big_enum.
  apply:eq_bigr=>i _.
  rewrite -!(analytic_germ_multiply_equation (@AnalyticGerms.laws R X NX hNX 0))
    (hPowered i).2 -(hPulled i).1 -(@AnalyticScalars.laws R X NX hNX 0 (weight i)).
  exact:mulrA.
Qed.

(** Source for [pointed_polynomial_actual_representative]:
    the displayed functions in original
    prefix coordinates represent their exact
    original polynomial germs, 3.4.8(10),
    pp. 330–331. The supplied coefficient
    representatives remain local witnesses; every
    claimed equation follows from the existing
    independent representative and evaluation interfaces. *)
Theorem pointed_polynomial_actual_representative (R:realType) (X Y:lmodType R)
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
  (W:T) N (b:'I_N->@analytic_representative_type R Y NY hNY 0):
  is_pointed_analytic_germ_pullback projection E ->
  (forall x,analytic_representative_value fXi x = xi x) ->
  is_commutative_polynomial_evaluation embed variable E (analytic_germ fXi) J ->
  (forall i,(N<=i)%N ->coefficient W i = 0) ->
  (forall i:'I_N,analytic_germ (b i) = coefficient W i) ->
  exists f:@analytic_representative_type R X NX hNX 0,
    (forall x,analytic_representative_value f x =
      \sum_(i<N) analytic_representative_value (b i) (projection x)*(xi x)^+(i:nat)) /\
    (analytic_germ f:@analytic_germ_ring R X NX hNX 0) = J W.
Proof.
move=>hE hXi hJ hSupport hB.
have [f [hValues hGerm]]:=@pointed_finite_power_actual_representative R X Y NX NY hNX hNY
  projection E xi fXi N b (fun _=>1) (fun i=>(i:nat)) hE hXi.
exists f;split.
- move=>x;rewrite hValues;apply:eq_bigr=>i _;by rewrite mul1r.
- rewrite hGerm (@polynomial_evaluation_finite_expression
    [the comNzRingType of (@analytic_germ_ring R Y NY hNY 0)] T
    [the comNzRingType of (@analytic_germ_ring R X NX hNX 0)] embed variable coefficient
    hT E (analytic_germ fXi) J hJ W N hSupport).
  apply:eq_bigr=>i _;by rewrite rmorph1 mul1r hB.
Qed.
