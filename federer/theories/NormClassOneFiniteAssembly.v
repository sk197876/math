(** Federer (1969), 3.1.11, p. 223: the finite
    linear assembly used in the coordinate class criterion.
    Auxiliary multilinear spaces come only from the opaque interface. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormClassOneUP
  ContinuousMultilinearUP ContinuousMultilinearSealed NormClassHigherUP
  NormClassHigherFirst NormClassHigherPostcompose NormClassHigherFiniteSums
  NormClassHigherLocalValues.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [norm_class_one_bounded_postcompose]: bounded
    linear coefficient assembly preserves class one, supporting
    the last equivalence in Federer 3.1.11, p. 223. *)
Lemma norm_class_one_bounded_postcompose (R : realType)
    (X U V : lmodType R) (NX : X->R) (NU : U->R) (NV : V->R)
    (hNX : is_real_norm NX) (hNU : is_real_norm NU) (hNV : is_real_norm NV)
    (A : X->Prop) (f : X->U) (L : Hom U V) :
  norm_bounded_linear NU NV L -> norm_class_one NX NU A f ->
  norm_class_one NX NV A (fun x=>L (f x)).
Proof.
move=>hL hf.
pose P i := @ContinuousMultilinear.space R i X U NX NU hNX hNU.
pose ep i := @ContinuousMultilinear.evaluation R i X U NX NU hNX hNU.
pose PN i := @ContinuousMultilinear.norm R i X U NX NU hNX hNU.
pose hP i := @ContinuousMultilinear.laws R i X U NX NU hNX hNU.
pose Q i := @ContinuousMultilinear.space R i X V NX NV hNX hNV.
pose eq i := @ContinuousMultilinear.evaluation R i X V NX NV hNX hNV.
pose QN i := @ContinuousMultilinear.norm R i X V NX NV hNX hNV.
pose hQ i := @ContinuousMultilinear.laws R i X V NX NV hNX hNV.
apply: (@norm_class_higher_first R X V NX NV hNX hNV Q eq QN hQ A _).1.
apply: (@norm_class_higher_postcompose R X U V NX NU NV hNX hNU hNV
  P Q ep PN eq QN hP hQ A f L 1%N hL).
exact: (@norm_class_higher_first R X U NX NU hNX hNU P ep PN hP A f).2 hf.
Qed.

(** Source for [norm_class_one_finite_sum]: finite sums of
    the coordinate coefficient fields preserve class one,
    Federer 3.1.11, p. 223. The open-domain
    hypothesis also covers an empty family of coefficients. *)
Lemma norm_class_one_finite_sum (R : realType)
    (X Y : lmodType R) (NX : X->R) (NY : Y->R)
    (hNX : is_real_norm NX) (hNY : is_real_norm NY)
    (A : X->Prop) (hA : forall x, A x -> norm_domain_interior NX A x)
    (I : finType) (f : I->X->Y) :
  (forall i, norm_class_one NX NY A (f i)) ->
  norm_class_one NX NY A (fun x=>\sum_i f i x).
Proof.
move=>hf.
pose Z i := @ContinuousMultilinear.space R i X Y NX NY hNX hNY.
pose ev i := @ContinuousMultilinear.evaluation R i X Y NX NY hNX hNY.
pose ZN i := @ContinuousMultilinear.norm R i X Y NX NY hNX hNY.
pose hZ i := @ContinuousMultilinear.laws R i X Y NX NY hNX hNY.
apply: (@norm_class_higher_first R X Y NX NY hNX hNY Z ev ZN hZ A _).1.
apply: (@norm_class_higher_finite_sum R X Y NX NY hNX hNY Z ev ZN hZ A hA I f 1%N).
move=>i; exact: (@norm_class_higher_first R X Y NX NY hNX hNY Z ev ZN hZ A _).2 (hf i).
Qed.

(** Source for [norm_class_one_domain_agreement]: the class
    criterion concerns the original domain only; representatives
    outside it do not matter, Federer 3.1.11, p. 223. *)
Lemma norm_class_one_domain_agreement (R : realType)
    (X Y : lmodType R) (NX : X->R) (NY : Y->R)
    (hNX : is_real_norm NX) (hNY : is_real_norm NY)
    (A : X->Prop) (f g : X->Y) :
  (forall x, A x -> f x=g x) ->
  norm_class_one NX NY A f -> norm_class_one NX NY A g.
Proof.
move=>he hf.
pose Z i := @ContinuousMultilinear.space R i X Y NX NY hNX hNY.
pose ev i := @ContinuousMultilinear.evaluation R i X Y NX NY hNX hNY.
pose ZN i := @ContinuousMultilinear.norm R i X Y NX NY hNX hNY.
pose hZ i := @ContinuousMultilinear.laws R i X Y NX NY hNX hNY.
apply: (@norm_class_higher_first R X Y NX NY hNX hNY Z ev ZN hZ A _).1.
apply: (@norm_class_higher_domain_agreement R X Y NX NY hNX hNY Z ev ZN hZ
  A f g 1%N he).
exact: (@norm_class_higher_first R X Y NX NY hNX hNY Z ev ZN hZ A f).2 hf.
Qed.
