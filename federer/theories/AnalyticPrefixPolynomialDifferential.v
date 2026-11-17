(** Federer (1969), 3.4.8(10), p. 331:
    the original finite prefix polynomials
    and their displayed directional derivatives
    are analytic on the whole prefix
    domain. Apply the existing analytic
    operations and checked differential connections. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormClassOneUP NormRegularity
  NormLinearDomainLaws NormDifferentialDirectional NormAnalyticUP NormAnalyticLocal NormAnalyticLinear NormAnalyticOperations
  NormAnalyticArithmetic NormAnalyticScalarProducts PrefixCoefficientDirectionalDifferential
  FinitePolynomialDirectionalDifferential.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [analytic_prefix_polynomial_differential]:
    the original polynomial and its actual
    transverse differential on p_m inverse Y,
    3.4.8(10), p. 331. The same
    original analytic coefficient functions occur
    in both expressions. Every direction in
    the original prefix kernel is retained. *)
Theorem analytic_prefix_polynomial_differential (R:realType) (X Y:lmodType R)
  (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
  (U:set Y) (projection:Hom X Y) (xi:Hom X R^o)
  N (b:'I_N->Y->R):
  (forall y,U y ->norm_domain_interior NY U y) ->
  norm_bounded_linear NX NY projection ->norm_bounded_linear NX (fun t:R^o=>`|t|) xi ->
  (forall i,@norm_analytic R Y R^o NY (fun t:R^o=>`|t|) hNY (@scalar_absolute_value_norm R) U (b i)) ->
  let A:=fun x:X=>U (projection x) in
  let F:=fun x:X=>\sum_(i<N) b i (projection x)*(xi x)^+(i:nat) in
  let derivative:=fun x:X=>\sum_(i<N) (i:nat)%:R*b i (projection x)*(xi x)^+(i:nat).-1 in
  @norm_analytic R X R^o NX (fun t:R^o=>`|t|) hNX (@scalar_absolute_value_norm R) A F /\
  @norm_analytic R X R^o NX (fun t:R^o=>`|t|) hNX (@scalar_absolute_value_norm R) A derivative /\
  forall a:X,A a ->exists L:Hom X R^o,
    has_norm_differential NX (fun t:R^o=>`|t|) A F a L /\
    forall v:X,projection v = 0 ->L v = derivative a*xi v.
Proof.
move=>hOpen hProjection hXi hB A F derivative.
pose NS:=fun t:R^o=>`|t|.
pose hNS:=@scalar_absolute_value_norm R.
have hAOpen x (hx:A x):norm_domain_interior NX A x.
  exact:(@norm_bounded_linear_preimage_interior R X Y NX NY hNX projection U x hProjection (hOpen _ hx)).
have hProjectionAnalytic:=@norm_bounded_linear_analytic R X Y NX NY hNX hNY A hAOpen projection hProjection.
have hXiAnalytic:=@norm_bounded_linear_analytic R X R^o NX NS hNX hNS A hAOpen xi hXi.
have hCoefficient i:@norm_analytic R X R^o NX NS hNX hNS A (fun x=>b i (projection x)).
  exact:(@norm_analytic_compose_on R X Y R^o NX NY NS hNX hNY hNS A U projection (b i)
    (fun x hx=>hx) hProjectionAnalytic (hB i)).
have hPolynomialPower i:@norm_analytic R X R^o NX NS hNX hNS A (fun x=>b i (projection x)*(xi x)^+(i:nat)).
  exact:(@norm_analytic_scalar_product R X NX hNX A _ _ (hCoefficient i)
    (@norm_analytic_scalar_power R X NX hNX A xi (i:nat) hXiAnalytic)).
have hDerivativeTerm (i:'I_N):@norm_analytic R X R^o NX NS hNX hNS A
    (fun x=>(i:nat)%:R*b i (projection x)*(xi x)^+(i:nat).-1).
  have hBase:=@norm_analytic_scalar_product R X NX hNX A _ _ (hCoefficient i)
    (@norm_analytic_scalar_power R X NX hNX A xi (i:nat).-1 hXiAnalytic).
  have hScaled:@norm_analytic R X R^o NX NS hNX hNS A
      (fun x=>(i:nat)%:R*:(b i (projection x)*(xi x)^+(i:nat).-1:R^o)).
    move=>x hx;exact:(@norm_analytic_at_scale R X R^o NX NS hNX hNS A _ x (i:nat)%:R (hBase x hx)).
  apply:(@norm_analytic_domain_agreement R X R^o NX NS hNX hNS A _ _ _ hScaled)=>x _.
  change ((i:nat)%:R*(b i (projection x)*(xi x)^+(i:nat).-1) =
    (i:nat)%:R*b i (projection x)*(xi x)^+(i:nat).-1);exact:mulrA.
split.
- exact:(@norm_analytic_finite_scalar_sum R X NX hNX A [the finType of 'I_N] _ hAOpen hPolynomialPower).
split.
- exact:(@norm_analytic_finite_scalar_sum R X NX hNX A [the finType of 'I_N] _ hAOpen hDerivativeTerm).
move=>a hA.
have hEach i:exists D:Y->Hom Y R^o,is_norm_class_one_field NY NS U (b i) D.
  exact:((@norm_class_firstP R Y R^o NY NS hNY hNS U (b i)).1
    (@norm_analytic_class_all_orders R Y R^o NY NS hNY hNS U (b i) (hB i) 1%N)).
pose D:=fun i=>projT1 (cid (hEach i)).
have hD i:=projT2 (cid (hEach i)).
have hCoefficientD i:=@prefix_coefficient_directional_differential R X Y NX NY hNX hNY A U projection
  (b i) a (0:X) (D i (projection a)) (hAOpen a hA) hProjection (fun x hx=>hx) (linear0 projection)
  (norm_class_one_differential (hD i) hA).
have hDifferential i:has_norm_differential NX NS A (fun x=>b i (projection x)) a
    (hom_comp (D i (projection a)) projection):=(hCoefficientD i).1.
have [L [hL _]]:=@finite_polynomial_directional_differential R X NX hNX A a (0:X) N
  (fun i x=>b i (projection x)) (fun i=>hom_comp (D i (projection a)) projection) xi
  (hAOpen a hA) hXi hDifferential (fun i=>(hCoefficientD i).2).
exists L;split;first exact:hL.
move=>v hZero.
have hZeroD i:(hom_comp (D i (projection a)) projection) v = 0.
  by rewrite hom_compE hZero linear0.
have [M [hM hValue]]:=@finite_polynomial_directional_differential R X NX hNX A a v N
  (fun i x=>b i (projection x)) (fun i=>hom_comp (D i (projection a)) projection) xi
  (hAOpen a hA) hXi hDifferential hZeroD.
have hEqual:L = M.
  exact:(@norm_differential_unique R X R^o NX NS hNX hNS A F a L M hL hM).
by rewrite hEqual.
Qed.
