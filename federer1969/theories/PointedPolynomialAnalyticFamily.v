(** Federer (1969), 3.4.8(10), pp. 327, 331:
    the bounded original numerators have actual
    finite expressions on one prefix neighbourhood.
    Retain the chosen coefficients and apply
    the existing finite-neighbourhood, polynomial-representative
    and differential theorems. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormBoundedLinearTopology
  NormAnalyticUP NormAnalyticOperations AnalyticGermRepresentatives AnalyticGermUP AnalyticGermRing
  FiniteAnalyticNeighbourhood PointedAnalyticPullbackUP PointedPolynomialRepresentative
  AnalyticPrefixPolynomialDifferential CommutativePolynomialUP CommutativePolynomialEvaluationUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [pointed_polynomial_analytic_family]:
    the functions sum_i b_(i,j)(p_m(x))
    omega_(m+1)(x)^i on the original cylinder,
    3.4.8(10), pp. 327, 331. The
    exact same original coefficients give their
    germ and actual finite-expression equations. *)
Theorem pointed_polynomial_analytic_family (R:realType) (X Y:lmodType R)
  (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
  (projection:Hom X Y)
  (E:{rmorphism [the comNzRingType of (@analytic_germ_ring R Y NY hNY 0)]->
    [the comNzRingType of (@analytic_germ_ring R X NX hNX 0)]})
  (xi:Hom X R^o) (fXi:@analytic_representative_type R X NX hNX 0)
  (P:comNzRingType)
  (embed:{rmorphism [the comNzRingType of (@analytic_germ_ring R Y NY hNY 0)]->P})
  (variable:P) (coefficient:P->nat->@analytic_germ_ring R Y NY hNY 0)
  (hP:is_commutative_polynomial_ring embed variable coefficient)
  (J:{rmorphism P->[the comNzRingType of (@analytic_germ_ring R X NX hNX 0)]})
  (I:finType) (W:I->P) N (b:I->'I_N->@analytic_representative_type R Y NY hNY 0):
  is_pointed_analytic_germ_pullback projection E ->
  norm_bounded_linear NX NY projection ->norm_bounded_linear NX (fun t:R^o=>`|t|) xi ->
  (forall x,analytic_representative_value fXi x = xi x) ->
  is_commutative_polynomial_evaluation embed variable E (analytic_germ fXi) J ->
  (forall j i,(N<=i)%N ->coefficient (W j) i = 0) ->
  (forall j i,analytic_germ (b j i) = coefficient (W j) i) ->
  exists (U:set Y) (f:I->@analytic_representative_type R X NX hNX 0),
    U 0 /\@open (real_norm_metric_space hNY) U /\
    (forall j i,@norm_analytic R Y R^o NY (fun t:R^o=>`|t|) hNY (@scalar_absolute_value_norm R)
      U (analytic_representative_value (b j i))) /\
    (forall j,(analytic_germ (f j):@analytic_germ_ring R X NX hNX 0) = J (W j)) /\
    (forall j,@norm_analytic R X R^o NX (fun t:R^o=>`|t|) hNX (@scalar_absolute_value_norm R)
      (fun x=>U (projection x)) (analytic_representative_value (f j))) /\
    forall j x,analytic_representative_value (f j) x =
      \sum_(i<N) analytic_representative_value (b j i) (projection x)*(xi x)^+(i:nat).
Proof.
move=>hE hProjection hXi hValues hJ hSupport hB.
pose index:=[the finType of (I*'I_N)%type].
pose coefficients (q:index):=b q.1 q.2.
have [U [hOrigin [hOpen hCoefficients]]]:=@finite_analytic_representative_neighbourhood R Y NY hNY 0
  index coefficients.
have hExists j:=@pointed_polynomial_actual_representative R X Y NX NY hNX hNY projection E xi fXi
  P embed variable coefficient hP J (W j) N (b j) hE hValues hJ (hSupport j) (hB j).
have [f hF]:=choice hExists.
have hInterior y (hy:U y):norm_domain_interior NY U y.
  have hNeighbourhood:=hOpen;rewrite openE in hNeighbourhood.
  exact:((@norm_domain_interior_neighbourhood R Y NY hNY U y).2 (hNeighbourhood y hy)).
exists U,f;split;first exact:hOrigin.
split;first exact:hOpen.
split;first by move=>j i;exact:hCoefficients (j,i).
split;first by move=>j;exact:(hF j).2.
split;last by move=>j;exact:(hF j).1.
move=>j.
have hA:=(@analytic_prefix_polynomial_differential R X Y NX NY hNX hNY U projection xi N
  (fun i=>analytic_representative_value (b j i)) hInterior hProjection hXi
  (fun i=>hCoefficients (j,i))).1.
apply:(@norm_analytic_domain_agreement R X R^o NX (fun t:R^o=>`|t|) hNX
  (@scalar_absolute_value_norm R) (fun x=>U (projection x)) _ _ _ hA)=>x _.
exact:esym ((hF j).1 x).
Qed.
