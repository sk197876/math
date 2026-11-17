(** Federer (1969), 3.4.8(11), p. 334:
    the prepared W_j has actual analytic lower
    coefficient functions, zero coefficient values at
    the origin, and the exact monic scalar formula.
    Reuse the previously proved distinguished representatives
    and original polynomial-evaluation equation. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormAnalyticUP AnalyticGermRepresentatives
  AnalyticGermUP AnalyticGermRing AnalyticGermValueSealed PointedAnalyticPullbackUP
  CommutativePolynomialUP CommutativePolynomialEvaluationUP CommutativePolynomialDegreeUP
  DistinguishedPolynomialUP DistinguishedCoefficientRepresentatives PointedPolynomialRepresentative
  FiniteAnalyticNeighbourhood.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [distinguished_polynomial_actual_monic]:
    the original W_j and M_ij in
    3.4.8(11), pp. 334–335. The
    representatives, common analytic domain and exact
    monic formula are conclusions of this connection. *)
Theorem distinguished_polynomial_actual_monic (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (projection:Hom X Y)
    (E:{rmorphism [the comNzRingType of (@analytic_germ_ring R Y NY hNY 0)]->
      [the comNzRingType of (@analytic_germ_ring R X NX hNX 0)]})
    (xi:Hom X R^o) (fXi:@analytic_representative_type R X NX hNX 0)
    (P:comNzRingType)
    (embed:{rmorphism [the comNzRingType of (@analytic_germ_ring R Y NY hNY 0)]->P})
    (variable:P) (coefficient:P->nat->@analytic_germ_ring R Y NY hNY 0)
    (hP:is_commutative_polynomial_ring embed variable coefficient)
    (J:{rmorphism P->[the comNzRingType of (@analytic_germ_ring R X NX hNX 0)]}) W k:
  is_pointed_analytic_germ_pullback projection E ->
  (forall x,analytic_representative_value fXi x = xi x) ->
  is_commutative_polynomial_evaluation embed variable E (analytic_germ fXi) J ->
  is_distinguished_polynomial coefficient (@AnalyticGermValue.map R Y NY hNY 0) W k ->
  exists (U:set Y) (b:'I_k->@analytic_representative_type R Y NY hNY 0)
    (f:@analytic_representative_type R X NX hNX 0),
    U 0 /\@open (real_norm_metric_space hNY) U /\
    (forall i,@norm_analytic R Y R^o NY (fun z:R^o=>`|z|) hNY (@scalar_absolute_value_norm R)
      U (analytic_representative_value (b i))) /\
    (forall i,analytic_representative_value (b i) 0 = 0) /\
    (analytic_germ f:@analytic_germ_ring R X NX hNX 0) = J W /\
    forall x,analytic_representative_value f x =
      (xi x)^+k+\sum_(i<k) analytic_representative_value (b i) (projection x)*(xi x)^+(i:nat).
Proof.
move=>hE hXi hJ hW.
have [c [hC [hLeading hZero]]]:=@distinguished_coefficient_actual_representatives R Y NY hNY
  P coefficient W k hW.
have hSupport i (hi:(k.+1<=i)%N):coefficient W i = 0.
  exact:(hW.1.1.2 i hi).
have [f [hValues hGerm]]:=@pointed_polynomial_actual_representative R X Y NX NY hNX hNY
  projection E xi fXi P embed variable coefficient hP J W k.+1 c hE hXi hJ hSupport hC.
pose b:=fun i:'I_k=>c (widen_ord (leqnSn k) i).
have [U [hU0 [hUOpen hAnalytic]]]:=@finite_analytic_representative_neighbourhood R Y NY hNY 0
  (Finite.clone 'I_k _) b.
exists U,b,f;split;first exact:hU0.
split;first exact:hUOpen.
split;first exact:hAnalytic.
split.
- move=>i;exact:hZero (widen_ord (leqnSn k) i) (ltn_ord i).
- split;first exact:hGerm.
  move=>x;rewrite hValues big_ord_recr hLeading mul1r addrC.
  by [].
Qed.
