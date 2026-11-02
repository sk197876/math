(** Federer (1969), 3.2.33, p. 270: actual higher
    differentials and bounds for an individual printed series term. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp ring.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormDifferentialLinear NormClassOneUP NormClassOneLaws
  ContinuousMultilinearUP ContinuousMultilinearNorm NormHigherDifferentialUP NormHigherDifferentialArithmetic
  NormHigherDifferentialLocal NormClassZeroArithmetic NormClassZeroComposition NormClassHigherRestriction
  NormAffineDilationDifferentials.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [rescaled_interval_bump_differentials]: supporting
    all differentiated terms of the series in Federer 3.2.33,
    p. 270. The actual ith differential of a term is
    multiplied by d^(j+1) d^(-i); continuity and the norm
    estimate follow from the earlier affine and scalar laws.
    No derivative formula or regularity is assumed for the sum. *)
Theorem rescaled_interval_bump_differentials (R:realType)
    (Z:nat->lmodType R) (ev:forall i,{ffun 'I_i->R^o}->Hom (Z i) R^o)
    (ZN:forall i,Z i->R)
    (hZ:forall i,is_continuous_multilinear_space (fun t:R^o=>`|t|)
      (fun t:R^o=>`|t|) (ev i) (ZN i))
    (phi:R->R) j i (a d C:R) (D:R->Z i):
  0<d ->0<=C ->
  norm_class_zero (fun t:R^o=>`|t|) (fun t:R^o=>`|t|) (fun _=>True) phi ->
  (forall t,has_norm_higher_differential (fun t:R^o=>`|t|) ev ZN (fun _=>True) phi i t (D t)) ->
  norm_class_zero (fun t:R^o=>`|t|) (ZN i) (fun _=>True) D ->
  (forall t,ZN i (D t)<=C) ->
  exists E:R->Z i,
    norm_class_zero (fun t:R^o=>`|t|) (fun t:R^o=>`|t|) (fun _=>True)
      (fun t=>d^+j.+1*phi ((t-a)/d)) /\
    (forall t,has_norm_higher_differential (fun t:R^o=>`|t|) ev ZN (fun _=>True)
      (fun t=>d^+j.+1*phi ((t-a)/d)) i t (E t)) /\
    norm_class_zero (fun t:R^o=>`|t|) (ZN i) (fun _=>True) E /\
    forall t,ZN i (E t)<=C*d^+j.+1*(d^-1)^+i.
Proof.
move=>hd hC hPhi hD hCont hBound.
pose N:=fun t:R^o=>`|t|.
pose hN:=@scalar_absolute_value_norm R.
pose T (t:R^o):R^o:=d^-1*:t+(-d^-1*a).
pose E t:=d^+j.+1*:((d^-1)^+i*:D (T t)).
have hNZi:=continuous_multilinear_norm_is_norm hN (hZ i).
have hopen t (_:True):norm_domain_interior N (fun _=>True) t.
  exists 1; split; first exact:ltr01; by move=>v hv.
have hT: norm_class_zero N N (fun _=>True) T.
  apply:(norm_everywhere_differentiable_class_zero hN)=>t _.
  exact:(norm_affine_dilation_differential hN d^-1 (-d^-1*a) t).
have hRawD t:has_norm_higher_differential N ev ZN (fun _=>True)
    (fun t=>phi (T t)) i t ((d^-1)^+i*:D (T t)).
  exact:(@norm_higher_differential_affine_dilation R R^o R^o N N hN hN Z ev ZN hZ
    phi d^-1 (-d^-1*a) i D hD t).
have hRawScaled t:has_norm_higher_differential N ev ZN (fun _=>True)
    (fun t=>d^+j.+1*:(phi (T t):R^o)) i t (E t).
  exact:(@norm_higher_differential_field_scale R R^o R^o N N hN hN Z ev ZN hZ
    (fun _=>True) i (fun t=>phi (T t)) (fun t=>(d^-1)^+i*:D (T t)) (d^+j.+1)
    (fun t _=>hRawD t) t Logic.I).
have hTValue t:T t= (t-a)/d by rewrite /T; change (d^-1*t+(-d^-1*a)= (t-a)/d); ring.
have hQ:(fun t=>d^+j.+1*:(phi (T t):R^o))= (fun t=>d^+j.+1*phi ((t-a)/d)).
  by apply:funext=>t; rewrite hTValue.
have hRestrict (Y:lmodType R) (NY:Y->R) (g:R^o->Y):
    norm_class_zero N NY (fun _=>True /\True) g ->norm_class_zero N NY (fun _=>True) g.
  exact:(norm_class_zero_open_restriction (fun t (_:True)=>conj Logic.I Logic.I) hopen).
exists E; split.
- rewrite -hQ; apply:(norm_class_zero_scale hN).
  exact:(hRestrict _ _ _ (norm_class_zero_composition hT hPhi)).
- split; first by move=>t; rewrite -hQ; exact:hRawScaled.
  split.
  + apply:(norm_class_zero_scale hNZi); apply:(norm_class_zero_scale hNZi).
    exact:(hRestrict _ _ _ (norm_class_zero_composition hT hCont)).
  + move=>t; rewrite /E !(real_seminorm_scale hNZi.1).
    have hDNonnegative:0<=d^+j.+1:=exprn_ge0 _ (ltW hd).
    have hInvNonnegative:0<=(d^-1)^+i by apply:exprn_ge0; rewrite invr_ge0; exact:ltW hd.
    rewrite (ger0_norm hDNonnegative) (ger0_norm hInvNonnegative).
    have hh:=ler_wpM2l (mulr_ge0 hDNonnegative hInvNonnegative) (hBound (T t)).
    have hCoeff:d^+j.+1*(d^-1)^+i*C= C*d^+j.+1*(d^-1)^+i by ring.
    rewrite mulrA -hCoeff; exact hh.
Qed.
