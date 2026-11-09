(** Federer (1969), 3.4.6(1), pp. 321–322:
    the original finite transverse remainder has all required
    actual directional derivatives zero on one neighbourhood. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets.
From Federer Require Import Hom RealNormUP NormDifferentialUP ContinuousMultilinearUP ContinuousMultilinearSealed
  NormHigherDifferentialUP NormHigherDifferentialLocal NormAnalyticUP NormAnalyticLocal
  AnalyticDirectionalCoefficient AnalyticDirectionalPolynomialLine WeierstrassTransverseUP
  WeierstrassFiniteRemainderLine.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [weierstrass_finite_remainder_vanishing]:
    the degree bound is an actual derivative condition
    throughout the original analytic domain, as required
    by 3.4.6(1), pp. 321–322. The proof
    compares actual Taylor coefficients with the finite
    translated polynomial and cancels its nonzero factorial. *)
Theorem weierstrass_finite_remainder_vanishing (R:realType) (X K:lmodType R)
    (NX:X->R) (NK:K->R) (hNX:is_real_norm NX) (v:X)
    (xi:Hom X R^o) (inclusion:Hom K X) (projection:Hom X K)
    k (C:nat->X->R) (A:set X):
  is_weierstrass_transverse_space NX NK v xi inclusion projection ->
  @norm_analytic R X R^o NX (fun r=>`|r|) hNX (@scalar_absolute_value_norm R)
    A (fun x=>\sum_(i<k) (xi x)^+i*C i (inclusion (projection x))) ->
  forall p,(k<=p)%N ->forall a,A a ->
    forall z:@ContinuousMultilinear.space R p X R^o NX (fun r=>`|r|) hNX (@scalar_absolute_value_norm R),
    has_norm_higher_differential NX
      (fun i=>@ContinuousMultilinear.evaluation R i X R^o NX (fun r=>`|r|) hNX (@scalar_absolute_value_norm R))
      (fun i=>@ContinuousMultilinear.norm R i X R^o NX (fun r=>`|r|) hNX (@scalar_absolute_value_norm R))
      setT (fun x=>\sum_(i<k) (xi x)^+i*C i (inclusion (projection x))) p a z ->
    @ContinuousMultilinear.evaluation R p X R^o NX (fun r=>`|r|) hNX (@scalar_absolute_value_norm R)
      [ffun _:'I_p=>v] z=0.
Proof.
move=>hSplit hf p hp a ha z hz.
pose N:=fun r:R^o=>`|r|.
pose hN:=@scalar_absolute_value_norm R.
pose Z i:=@ContinuousMultilinear.space R i X R^o NX N hNX hN.
pose ev i:=@ContinuousMultilinear.evaluation R i X R^o NX N hNX hN.
pose NZ i:=@ContinuousMultilinear.norm R i X R^o NX N hNX hN.
pose hZ i:=@ContinuousMultilinear.laws R i X R^o NX N hNX hN.
pose F:=fun x=>\sum_(i<k) (xi x)^+i*C i (inclusion (projection x)).
have [c [hc _]]:=@analytic_directional_coefficient_exists R X R^o NX N hNX hN A F p v hf.
have [b hLine]:=@weierstrass_finite_remainder_shifted_line R X K NX NK v xi inclusion projection k C hSplit a.
have hFinite:=@analytic_directional_polynomial_line_coefficient R X R^o NX N hNX hN
  A F p v a c k b 1 ha hf hc ltr01 (fun t _=>hLine t).
have hLarge:(p<k)%N=false:=leq_gtF hp.
rewrite hLarge in hFinite.
have hOpen x (hx:A x):norm_domain_interior NX A x:=
  ((norm_analytic_class_all_orders hf 0%N).1 x hx).1.
have hLocal:=(@norm_higher_differential_open_restriction R X R^o NX N hNX hN Z ev NZ hZ
  p setT A F (fun x _=>Logic.I) hOpen a ha z).1 hz.
have hValue:=hc a ha z hLocal.
change (c a=((p`!)%:R)^-1*ev p [ffun _:'I_p=>v] z) in hValue.
rewrite hFinite in hValue.
have hNonzero:((p`!)%:R:R)!=0 by rewrite pnatr_eq0 -lt0n fact_gt0.
have hZero:(ev p [ffun _:'I_p=>v] z==0).
  by move/eqP:(esym hValue);rewrite mulf_eq0 invr_eq0 (negbTE hNonzero) orFb.
exact:eqP hZero.
Qed.
