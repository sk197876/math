(** Federer (1969), 3.4.8(10), pp. 330–331:
    the original polynomial and its derivative
    have actual analytic representatives on one
    original prefix neighbourhood. Apply the
    existing finite analytic neighbourhood and
    checked pointed representative and differential connections. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormBoundedLinearTopology
  NormDifferentialLocal NormAnalyticUP NormAnalyticOperations NormAnalyticDomain
  AnalyticGermRepresentatives AnalyticGermUP AnalyticGermRing FiniteAnalyticNeighbourhood
  PointedAnalyticPullbackUP PointedPolynomialRepresentative PointedPolynomialDerivativeRepresentative
  AnalyticPrefixPolynomialDifferential CommutativePolynomialUP CommutativePolynomialEvaluationUP
  FormalPolynomialDerivativeUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [analytic_prefix_polynomial_actual_witnesses]:
    common analytic Y and the actual
    W_(m+1), W'_(m+1), 3.4.8(10),
    pp. 330–331. The same original
    coefficient representatives occur in the
    polynomial, its formal derivative germ and
    its actual transverse differential. No
    derivative or neighbourhood witness is assumed. *)
Theorem analytic_prefix_polynomial_actual_witnesses (R:realType) (X Y:lmodType R)
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
  norm_bounded_linear NX NY projection ->norm_bounded_linear NX (fun t:R^o=>`|t|) xi ->
  (forall x,analytic_representative_value fXi x = xi x) ->
  is_commutative_polynomial_evaluation embed variable E (analytic_germ fXi) J ->
  is_formal_polynomial_derivative coefficient W derivative ->
  (forall i,(N<=i)%N ->coefficient W i = 0) ->
  (forall i:'I_N,analytic_germ (b i) = coefficient W i) ->
  exists (U:set Y) (f fD:@analytic_representative_type R X NX hNX 0),
    U 0 /\@open (real_norm_metric_space hNY) U /\
    (forall i,@norm_analytic R Y R^o NY (fun t:R^o=>`|t|) hNY (@scalar_absolute_value_norm R)
      U (analytic_representative_value (b i))) /\
    (analytic_germ f:@analytic_germ_ring R X NX hNX 0) = J W /\
    (analytic_germ fD:@analytic_germ_ring R X NX hNX 0) = J derivative /\
    @norm_analytic R X R^o NX (fun t:R^o=>`|t|) hNX (@scalar_absolute_value_norm R)
      (fun x=>U (projection x)) (analytic_representative_value f) /\
    @norm_analytic R X R^o NX (fun t:R^o=>`|t|) hNX (@scalar_absolute_value_norm R)
      (fun x=>U (projection x)) (analytic_representative_value fD) /\
    (forall x,analytic_representative_value f x =
      \sum_(i<N) analytic_representative_value (b i) (projection x)*(xi x)^+(i:nat)) /\
    (forall x,analytic_representative_value fD x =
      \sum_(i<N) (i:nat)%:R*analytic_representative_value (b i) (projection x)*(xi x)^+(i:nat).-1) /\
    forall a:X,U (projection a) ->exists L:Hom X R^o,
      has_norm_differential NX (fun t:R^o=>`|t|) (fun x=>U (projection x))
        (analytic_representative_value f) a L /\
      forall v:X,projection v = 0 ->L v = analytic_representative_value fD a*xi v.
Proof.
move=>hE hProjection hXi hXiValues hJ hDerivative hSupport hB.
have [U [hOrigin [hOpen hAnalytic]]]:=@finite_analytic_representative_neighbourhood R Y NY hNY 0
  [the finType of 'I_N] b.
have hInterior y (hy:U y):norm_domain_interior NY U y.
  have hNeighbourhood:=hOpen;rewrite openE in hNeighbourhood.
  exact:((@norm_domain_interior_neighbourhood R Y NY hNY U y).2 (hNeighbourhood y hy)).
have [f [hValues hGerm]]:=@pointed_polynomial_actual_representative R X Y NX NY hNX hNY
  projection E xi fXi T embed variable coefficient hT J W N b hE hXiValues hJ hSupport hB.
have [fD [hDerivativeValues hDerivativeGerm]]:=@pointed_polynomial_derivative_actual_representative R X Y NX NY hNX hNY
  projection E xi fXi T embed variable coefficient hT J W derivative N b hE hXiValues hJ hDerivative hSupport hB.
have [hF [hD hDifferentials]]:=@analytic_prefix_polynomial_differential R X Y NX NY hNX hNY U
  projection xi N (fun i=>analytic_representative_value (b i)) hInterior hProjection hXi hAnalytic.
pose A:=fun x:X=>U (projection x).
pose NS:=fun t:R^o=>`|t|.
pose hNS:=@scalar_absolute_value_norm R.
have hFActual:@norm_analytic R X R^o NX NS hNX hNS A (analytic_representative_value f).
  apply:(@norm_analytic_domain_agreement R X R^o NX NS hNX hNS A _ _ _ hF)=>x _.
  exact:esym (hValues x).
have hDActual:@norm_analytic R X R^o NX NS hNX hNS A (analytic_representative_value fD).
  apply:(@norm_analytic_domain_agreement R X R^o NX NS hNX hNS A _ _ _ hD)=>x _.
  exact:esym (hDerivativeValues x).
exists U,f,fD;split;first exact:hOrigin.
split;first exact:hOpen.
split;first exact:hAnalytic.
split;first exact:hGerm.
split;first exact:hDerivativeGerm.
split;first exact:hFActual.
split;first exact:hDActual.
split;first exact:hValues.
split;first exact:hDerivativeValues.
move=>a ha;have [L [hL hDirection]]:=hDifferentials a ha.
exists L;split.
- apply:(@norm_differential_domain_agreement R X R^o NX NS hNX A _ _ a L _ hL)=>x _.
  exact:esym (hValues x).
- move=>v hZero;rewrite hDirection //;by rewrite hDerivativeValues.
Qed.
