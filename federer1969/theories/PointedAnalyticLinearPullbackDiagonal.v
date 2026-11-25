(** Federer (1969), 3.4.8(5), p. 328:
    the original orthogonal germ action transforms each
    actual directional derivative by the same linear map.
    Taylor uniqueness on identical lines proves this rule;
    no derivative transformation is assumed. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormRegularity
  ContinuousMultilinearUP ContinuousMultilinearSealed NormHigherDifferentialUP
  NormHigherDifferentialLocal NormAnalyticUP AnalyticGermRepresentatives AnalyticGermUP
  AnalyticGermRingLaws AnalyticGermJetsSealed AnalyticDirectionalCoefficient
  WeierstrassLineCoefficientAgreement PointedAnalyticPullbackUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [pointed_analytic_linear_pullback_diagonal]: the
    actual diagonal derivative rule for the linear action
    used in 3.4.8(5), p. 328. The independent
    all-representative pullback law supplies exact composition.
    Every derivative order, including zero, remains. *)
Theorem pointed_analytic_linear_pullback_diagonal
    (R:realType) (X Y:lmodType R) (NX:X->R) (NY:Y->R)
    (hNX:is_real_norm NX) (hNY:is_real_norm NY) (a:X) (b:Y)
    (L:Hom X Y) (P:analytic_germ_space hNY b->analytic_germ_space hNX a):
  is_pointed_analytic_germ_pullback L P ->L a=b ->
  forall k (alpha:analytic_germ_space hNY b) (v:X),
    @ContinuousMultilinear.evaluation R k X R^o NX (fun t=>`|t|) hNX
      (@scalar_absolute_value_norm R) [ffun _:'I_k=>v]
      (@AnalyticGermJets.value R X NX hNX a k (P alpha))=
    @ContinuousMultilinear.evaluation R k Y R^o NY (fun t=>`|t|) hNY
      (@scalar_absolute_value_norm R) [ffun _:'I_k=>L v]
      (@AnalyticGermJets.value R Y NY hNY b k alpha).
Proof.
move=>hP hab k alpha v.
pose N:=fun t:R^o=>`|t|.
pose hN:=@scalar_absolute_value_norm R.
pose Z i:=@ContinuousMultilinear.space R i X R^o NX N hNX hN.
pose ez i:=@ContinuousMultilinear.evaluation R i X R^o NX N hNX hN.
pose NZ i:=@ContinuousMultilinear.norm R i X R^o NX N hNX hN.
pose hZ i:=@ContinuousMultilinear.laws R i X R^o NX N hNX hN.
pose W i:=@ContinuousMultilinear.space R i Y R^o NY N hNY hN.
pose ew i:=@ContinuousMultilinear.evaluation R i Y R^o NY N hNY hN.
pose NW i:=@ContinuousMultilinear.norm R i Y R^o NY N hNY hN.
pose hW i:=@ContinuousMultilinear.laws R i Y R^o NY N hNY hN.
have [f hf]:=@analytic_germ_has_representative R Y NY hNY b alpha.
have [g [hG hEquation]]:=hP f.
have hg : analytic_germ g = P alpha by rewrite -hf hG.
have [U [c [hUa [hUT [hClassU hBoundU]]]]]:=analytic_representative_analytic g.
have [V [d [hVb [hVT [hClassV hBoundV]]]]]:=analytic_representative_analytic f.
have hOpenU x (hx:U x):norm_domain_interior NX U x:=((hClassU 0%N).1 x hx).1.
have hOpenV y (hy:V y):norm_domain_interior NY V y:=((hClassV 0%N).1 y hy).1.
have hAnalyticU:@norm_analytic R X R^o NX N hNX hN U (analytic_representative_value g).
  move=>x hx;exists U,c;by split;last split;last split.
have hAnalyticV:@norm_analytic R Y R^o NY N hNY hN V (analytic_representative_value f).
  move=>x hx;exists V,d;by split;last split;last split.
have [s [hS hSAnalytic]]:=@analytic_directional_coefficient_exists R X R^o NX N hNX hN
  U (analytic_representative_value g) k v hAnalyticU.
have [t [hT hTAnalytic]]:=@analytic_directional_coefficient_exists R Y R^o NY N hNY hN
  V (analytic_representative_value f) k (L v) hAnalyticV.
have hSameLines:exists rho:R,0<rho /\forall r:R,`|r|<rho ->
    analytic_representative_value g (a+r*:v)=analytic_representative_value f (b+r*:L v).
  exists 1;split;first exact:ltr01.
  by move=>r _;rewrite hEquation linearD linearZ /= hab.
have hSame:=@weierstrass_line_coefficients_agree R X Y NX NY hNX hNY U V
  (analytic_representative_value g) (analytic_representative_value f)
  k v (L v) a b s t hUa hVb hAnalyticU hAnalyticV hS hT hSameLines.
have hJetG:=@AnalyticGermJets.laws R X NX hNX a k (P alpha) g hg.
have hJetF:=@AnalyticGermJets.laws R Y NY hNY b k alpha f hf.
have hRestrictG:=(@norm_higher_differential_open_restriction R X R^o NX N hNX hN Z ez NZ hZ
  k setT U (analytic_representative_value g) hUT hOpenU a hUa _).1 hJetG.
have hRestrictF:=(@norm_higher_differential_open_restriction R Y R^o NY N hNY hN W ew NW hW
  k setT V (analytic_representative_value f) hVT hOpenV b hVb _).1 hJetF.
rewrite (hS a hUa _ hRestrictG) (hT b hVb _ hRestrictF) in hSame.
have hFactor:((k`!)%:R:R)!=0 by rewrite pnatr_eq0 -lt0n fact_gt0.
have hInverse:((k`!)%:R:R)^-1!=0 by rewrite invr_eq0.
apply:(scalerI hInverse);exact:hSame.
Qed.
