(** Federer (1969), 3.4.7, p. 325: the
    original transverse projection induces the coefficient-ring
    homomorphism. The actual map uses the existing opaque
    analytic pullback; no implementation of germs is exposed. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormOpenDomainLaws
  NormAnalyticUP NormAnalyticLinear AnalyticGermRing AnalyticPullbackRingMorphism
  WeierstrassTransverseUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [weierstrass_transverse_projection_analytic]:
    the original bounded projection is analytic at
    zero, supporting 3.4.7, p. 325. *)
Lemma weierstrass_transverse_projection_analytic (R:realType) (X K:lmodType R)
    (NX:X->R) (NK:K->R) (hNX:is_real_norm NX) (hNK:is_real_norm NK)
    (v:X) (xi:Hom X R^o) (inclusion:Hom K X) (projection:Hom X K):
  is_weierstrass_transverse_space NX NK v xi inclusion projection ->
  @norm_analytic_at R X K NX NK hNX hNK setT projection 0.
Proof.
move=>hSplit;exact:(@norm_bounded_linear_analytic R X K NX NK hNX hNK setT
  (fun x _=>norm_full_domain_interior NX x) projection
  (weierstrass_transverse_projection_bounded hSplit) 0 Logic.I).
Qed.

(** Source for [weierstrass_transverse_ring_pullback]:
    the original coefficient-ring homomorphism induced by
    eta, 3.4.7, p. 325. The actual projection
    of zero is zero by the proved linearity laws. *)
Definition weierstrass_transverse_ring_pullback (R:realType) (X K:lmodType R)
    (NX:X->R) (NK:K->R) (hNX:is_real_norm NX) (hNK:is_real_norm NK)
    (v:X) (xi:Hom X R^o) (inclusion:Hom K X) (projection:Hom X K)
    (hSplit:is_weierstrass_transverse_space NX NK v xi inclusion projection):
  {rmorphism [the comNzRingType of (@analytic_germ_ring R K NK hNK (projection 0))]->
    [the comNzRingType of (@analytic_germ_ring R X NX hNX 0)]}:=
  @analytic_germ_ring_pullback R X K NX NK hNX hNK setT projection 0
    (@weierstrass_transverse_projection_analytic R X K NX NK hNX hNK
      v xi inclusion projection hSplit).
