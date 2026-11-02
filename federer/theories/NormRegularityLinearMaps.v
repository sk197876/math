(** Federer (1969), 3.1.21, p. 234: bounded linear
    coordinate maps used in tangent and normal bundle charts.
    These are adapters to the proved calculus of 3.1.11. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom RealNormUP ContinuousMultilinearUP ContinuousMultilinearSealed
  NormDifferentialUP NormClassOneUP NormClassHigherPostcompose NormRegularity NormRegularityOperations
  NormOpenDomainLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [norm_class_postcompose_linear]: supporting
    bounded linear target changes in the bundle charts of
    Federer 3.1.21, p. 234; the class law is 3.1.11,
    p. 220, expressed in the public sealed operator spaces. *)
Lemma norm_class_postcompose_linear (R:realType) (X U V:lmodType R)
    (NX:X->R) (NU:U->R) (NV:V->R)
    (hNX:is_real_norm NX) (hNU:is_real_norm NU) (hNV:is_real_norm NV)
    (A:X->Prop) (f:X->U) (L:Hom U V) k :
  norm_bounded_linear NU NV L -> norm_class hNX hNU A f k ->
  norm_class hNX hNV A (fun x=>L (f x)) k.
Proof.
exact (@norm_class_higher_postcompose R X U V NX NU NV hNX hNU hNV
  (fun j=>@ContinuousMultilinear.space R j X U NX NU hNX hNU)
  (fun j=>@ContinuousMultilinear.space R j X V NX NV hNX hNV)
  (fun j=>@ContinuousMultilinear.evaluation R j X U NX NU hNX hNU)
  (fun j=>@ContinuousMultilinear.norm R j X U NX NU hNX hNU)
  (fun j=>@ContinuousMultilinear.evaluation R j X V NX NV hNX hNV)
  (fun j=>@ContinuousMultilinear.norm R j X V NX NV hNX hNV)
  (fun j=>@ContinuousMultilinear.laws R j X U NX NU hNX hNU)
  (fun j=>@ContinuousMultilinear.laws R j X V NX NV hNX hNV) A f L k).
Qed.

(** Source for [norm_class_precompose_linear]: supporting
    projection onto the base point in the bundle charts of
    Federer 3.1.21, p. 234. The exact inverse-image domain
    is open by continuity of the given linear map, rather
    than an additional openness hypothesis. *)
Lemma norm_class_precompose_linear (R:realType) (P X Y:lmodType R)
    (NP:P->R) (NX:X->R) (NY:Y->R)
    (hNP:is_real_norm NP) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (A:X->Prop) (f:X->Y) (L:Hom P X) k :
  norm_bounded_linear NP NX L -> norm_class hNX hNY A f k ->
  norm_class hNP hNY (fun p=>A (L p)) (fun p=>f (L p)) k.
Proof.
move=>hL hf.
have hfull p (hp:True):norm_domain_interior NP (fun _=>True) p.
  exact: norm_full_domain_interior.
have hLc:=@norm_class_linear R P X NP NX hNP hNX (fun _=>True) L k hfull hL.
have hc:=norm_class_composition hLc hf.
have hopen p (hp:A (L p)):norm_domain_interior NP (fun p=>A (L p)) p.
  exact (@norm_class_zero_preimage_interior R P X Y NP NX NY A L f
    (norm_class_continuous hLc) (norm_class_continuous hf) p hp).
exact (@norm_class_open_restriction R P Y NP NY hNP hNY
  (fun p=>True /\ A (L p)) (fun p=>A (L p)) (fun p=>f (L p)) k
  (fun p hp=>conj I hp) hopen hc).
Qed.
