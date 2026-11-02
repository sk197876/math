(** Federer (1969), 3.1.11, pp. 219–220:
    restriction to an open subset preserves class k.
    This supports the actual domain of a composite map. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormClassOneUP
  ContinuousMultilinearUP NormHigherDifferentialLocal NormClassHigherUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [norm_class_zero_open_restriction]:
    the open-domain convention for class zero
    in Federer 3.1.1, p. 210, used
    for the higher composition theorem of 3.1.11,
    p. 220. *)
Lemma norm_class_zero_open_restriction (R : realType)
    (X Y : lmodType R) (NX : X->R) (NY : Y->R)
    (A B : X->Prop) (f : X->Y) :
  (forall x, B x -> A x) ->
  (forall x, B x -> norm_domain_interior NX B x) ->
  norm_class_zero NX NY A f -> norm_class_zero NX NY B f.
Proof.
move=> hBA hopen hf a ha; split; first exact: hopen a ha.
move=> e he; have [d [hd hb]] := (hf a (hBA a ha)).2 e he.
exists d; split=> // h hh hs; exact: hb h (hBA _ hh) hs.
Qed.

(** Source for [norm_class_higher_open_restriction]:
    every class k is preserved by restriction
    to an open subset, supporting Federer 3.1.11,
    p. 220. The higher derivative fields
    agree with their original exact graphs. *)
Theorem norm_class_higher_open_restriction (R : realType)
    (X Y : lmodType R) (NX : X->R) (NY : Y->R)
    (hNX : is_real_norm NX) (hNY : is_real_norm NY)
    (Z : nat->lmodType R)
    (ez : forall k, {ffun 'I_k->X}->Hom (Z k) Y)
    (ZN : forall k, Z k->R)
    (hZ : forall k, is_continuous_multilinear_space NX NY (@ez k) (@ZN k))
    (A B : X->Prop) (f : X->Y) k :
  (forall x, B x -> A x) ->
  (forall x, B x -> norm_domain_interior NX B x) ->
  norm_class_higher NX NY ez ZN A f k ->
  norm_class_higher NX NY ez ZN B f k.
Proof.
move=> hBA hopen [hf [D [hD hcD]]].
split; first exact: norm_class_zero_open_restriction hBA hopen hf.
exists D; split.
- move=> a ha.
  exact: (@norm_higher_differential_open_restriction R X Y NX NY
    hNX hNY Z ez ZN hZ k A B f hBA hopen a ha (D a)).1 (hD a (hBA a ha)).
- exact: norm_class_zero_open_restriction hBA hopen hcD.
Qed.
