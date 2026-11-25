(** Federer (1969), 3.4.12, p. 339, extending 3.4.8(5), p. 328:
    the original orthogonal germ action transforms each
    actual directional derivative by the same linear map.
    Taylor uniqueness on identical lines proves this rule;
    no derivative transformation is assumed. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import ScalarRestriction ComplexScalarSealed ComplexModulus ComplexScalarNorm HolomorphicLinear HolomorphicGermAnalytic Hom RealNormUP NormDifferentialUP NormRegularity
  ContinuousMultilinearUP ContinuousMultilinearSealed NormHigherDifferentialUP
  NormHigherDifferentialLocal NormAnalyticUP HolomorphicGermRepresentatives HolomorphicGermUP
  HolomorphicGermRingLaws HolomorphicGermJetsSealed AnalyticDirectionalCoefficient
  NormWeierstrassLineCoefficientAgreement PointedHolomorphicPullbackUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [pointed_holomorphic_linear_pullback_diagonal]: the
    actual diagonal derivative rule for the linear action
    used in 3.4.8(5), p. 328. The independent
    all-representative pullback law supplies exact composition.
    Every derivative order, including zero, remains. *)
Theorem pointed_holomorphic_linear_pullback_diagonal
    (R:realType) (X Y:lmodType (ComplexScalars.C R)) (NX:X->R) (NY:Y->R)
    (hNX:@is_real_norm R (restricted_space (ComplexScalars.embed R) X) NX) (hNY:@is_real_norm R (restricted_space (ComplexScalars.embed R) Y) NY) (a:X) (b:Y)
    (L:Hom X Y) (P:holomorphic_germ_space hNY b->holomorphic_germ_space hNX a):
  is_pointed_holomorphic_germ_pullback L P ->L a=b ->
  forall k (alpha:holomorphic_germ_space hNY b) (v:X),
    @ContinuousMultilinear.evaluation R k (restricted_space (ComplexScalars.embed R) X) (restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o) NX (@complex_modulus R) hNX
      (@complex_modulus_real_norm R) [ffun _:'I_k=>v]
      (@HolomorphicGermJets.value R X NX hNX a k (P alpha))=
    @ContinuousMultilinear.evaluation R k (restricted_space (ComplexScalars.embed R) Y) (restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o) NY (@complex_modulus R) hNY
      (@complex_modulus_real_norm R) [ffun _:'I_k=>L v]
      (@HolomorphicGermJets.value R Y NY hNY b k alpha).
Proof.
move=>hP hab k alpha v.
pose N:=@complex_modulus R.
pose hN:=@complex_modulus_real_norm R.
pose Z i:=@ContinuousMultilinear.space R i (restricted_space (ComplexScalars.embed R) X) (restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o) NX N hNX hN.
pose ez i:=@ContinuousMultilinear.evaluation R i (restricted_space (ComplexScalars.embed R) X) (restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o) NX N hNX hN.
pose NZ i:=@ContinuousMultilinear.norm R i (restricted_space (ComplexScalars.embed R) X) (restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o) NX N hNX hN.
pose hZ i:=@ContinuousMultilinear.laws R i (restricted_space (ComplexScalars.embed R) X) (restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o) NX N hNX hN.
pose W i:=@ContinuousMultilinear.space R i (restricted_space (ComplexScalars.embed R) Y) (restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o) NY N hNY hN.
pose ew i:=@ContinuousMultilinear.evaluation R i (restricted_space (ComplexScalars.embed R) Y) (restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o) NY N hNY hN.
pose NW i:=@ContinuousMultilinear.norm R i (restricted_space (ComplexScalars.embed R) Y) (restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o) NY N hNY hN.
pose hW i:=@ContinuousMultilinear.laws R i (restricted_space (ComplexScalars.embed R) Y) (restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o) NY N hNY hN.
have [f hf]:=@holomorphic_germ_has_representative R Y NY hNY b alpha.
have [g [hG hEquation]]:=hP f.
have hg : holomorphic_germ g = P alpha by rewrite -hf hG.
have [U [c [hUa [hUT [hClassU hBoundU]]]]]:=holomorphic_representative_analytic g.
have [V [d [hVb [hVT [hClassV hBoundV]]]]]:=holomorphic_representative_analytic f.
have hOpenU x (hx:U x):@norm_domain_interior R (restricted_space (ComplexScalars.embed R) X) NX U x:=((hClassU 0%N).1 x hx).1.
have hOpenV y (hy:V y):@norm_domain_interior R (restricted_space (ComplexScalars.embed R) Y) NY V y:=((hClassV 0%N).1 y hy).1.
have hAnalyticU:@norm_analytic R (restricted_space (ComplexScalars.embed R) X) (restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o) NX N hNX hN U (holomorphic_representative_value g).
  move=>x hx;exists U,c;by split;last split;last split.
have hAnalyticV:@norm_analytic R (restricted_space (ComplexScalars.embed R) Y) (restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o) NY N hNY hN V (holomorphic_representative_value f).
  move=>x hx;exists V,d;by split;last split;last split.
have [s [hS hSAnalytic]]:=@analytic_directional_coefficient_exists R (restricted_space (ComplexScalars.embed R) X) (restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o) NX N hNX hN
  U (holomorphic_representative_value g) k v hAnalyticU.
have [t [hT hTAnalytic]]:=@analytic_directional_coefficient_exists R (restricted_space (ComplexScalars.embed R) Y) (restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o) NY N hNY hN
  V (holomorphic_representative_value f) k (L v) hAnalyticV.
have hSameLines:exists rho:R,0<rho /\forall r:R,`|r|<rho ->
    holomorphic_representative_value g (a+ComplexScalars.embed R r*:v)=holomorphic_representative_value f (b+ComplexScalars.embed R r*:(L v)).
  exists 1;split;first exact:ltr01.
  move=>r _;rewrite hEquation.
  change (holomorphic_representative_value f ((complex_hom_real L) (a+@GRing.scale R (restricted_space (ComplexScalars.embed R) X) r v))=
    holomorphic_representative_value f (b+@GRing.scale R (restricted_space (ComplexScalars.embed R) Y) r ((complex_hom_real L) v))).
  by rewrite linearD linearZ /= hab.
have hSame:=@norm_weierstrass_line_coefficients_agree R (restricted_space (ComplexScalars.embed R) X) (restricted_space (ComplexScalars.embed R) Y) (restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o) N hN NX NY hNX hNY U V
  (holomorphic_representative_value g) (holomorphic_representative_value f)
  k v (L v) a b s t hUa hVb hAnalyticU hAnalyticV hS hT hSameLines.
have hJetG:=@HolomorphicGermJets.laws R X NX hNX a k (P alpha) g hg.
have hJetF:=@HolomorphicGermJets.laws R Y NY hNY b k alpha f hf.
have hRestrictG:=(@norm_higher_differential_open_restriction R (restricted_space (ComplexScalars.embed R) X) (restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o) NX N hNX hN Z ez NZ hZ
  k setT U (holomorphic_representative_value g) hUT hOpenU a hUa _).1 hJetG.
have hRestrictF:=(@norm_higher_differential_open_restriction R (restricted_space (ComplexScalars.embed R) Y) (restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o) NY N hNY hN W ew NW hW
  k setT V (holomorphic_representative_value f) hVT hOpenV b hVb _).1 hJetF.
rewrite (hS a hUa _ hRestrictG) (hT b hVb _ hRestrictF) in hSame.
have hFactor:((k`!)%:R:R)!=0 by rewrite pnatr_eq0 -lt0n fact_gt0.
have hInverse:((k`!)%:R:R)^-1!=0 by rewrite invr_eq0.
apply:(scalerI hInverse);exact:hSame.
Qed.
