(** Federer (1969), 3.1.11, p. 220:
    class one in the higher-order definition is exactly
    class one as already defined in 3.1.1, p. 210. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP
  NormClassOneUP NormClassOneLaws NormOperatorNormUP ContinuousOperatorUP
  ContinuousMultilinearUP ContinuousMultilinearOne
  NormHigherDifferentialUP NormHigherDifferentialFirst NormClassHigherUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [norm_class_higher_first]: the higher class
    convention extends the existing class-one notion, as
    required in Federer 3.1.11, p. 220. Representatives
    of derivative fields are compared only on the actual domain. *)
Theorem norm_class_higher_first (R : realType)
    (X Y : lmodType R) (NX : X->R) (NY : Y->R)
    (hNX : is_real_norm NX) (hNY : is_real_norm NY)
    (Z : nat->lmodType R)
    (evaluation : forall k, {ffun 'I_k->X}->Hom (Z k) Y)
    (ZN : forall k, Z k->R)
    (hZ : forall k, is_continuous_multilinear_space NX NY (@evaluation k) (@ZN k))
    (A : X->Prop) (f : X->Y) :
  norm_class_higher NX NY evaluation ZN A f 1%N <-> norm_class_one NX NY A f.
Proof.
pose J := @continuous_multilinear_one_evaluation R X Y (Z 1%N) NX NY
  (@evaluation 1%N) (@ZN 1%N) (@hZ 1%N).
have hJ := @continuous_multilinear_one_operator_space R X Y (Z 1%N) NX NY
  (@evaluation 1%N) (@ZN 1%N) (@hZ 1%N).
split.
- move=> [hzero [G [hG hcont]]].
  pose D x := J (G x).
  exists D; constructor=> //.
  + move=> a ha; exact: (@norm_higher_differential_first R X Y NX NY hNX hNY
      Z evaluation ZN hZ A f a (G a)).1 (hG a ha).
  + have hO x a : A x -> A a ->
        is_norm_operator_norm NX NY (D x-D a) (@ZN 1%N (G x-G a)).
      move=> _ _; rewrite /D -linearB.
      exact: continuous_operator_norm_laws hJ _.
    apply: (norm_field_continuous_operator hNX hO).2.
    by move=> a ha; exact: (hcont a ha).2.
- move=> [D hD]; split; first exact: norm_class_one_zero hD.
  have hex x : exists z : Z 1%N, A x -> J z=D x.
    case: (pselect (A x))=> [hx|hx].
    + have [z hz] := continuous_operator_surjective hJ
        (norm_differential_bounded (norm_class_one_differential hD hx)).
      by exists z.
    + exists 0; by move=> h; exfalso; exact: hx h.
  have [G hG] := choice hex.
  exists G; split.
  + move=> a ha; apply: (@norm_higher_differential_first R X Y NX NY hNX hNY
      Z evaluation ZN hZ A f a (G a)).2.
    change (has_norm_differential NX NY A f a (J (G a))).
    rewrite (hG a ha).
    exact (norm_class_one_differential hD ha).
  + have hO x a : A x -> A a ->
        is_norm_operator_norm NX NY (D x-D a) (@ZN 1%N (G x-G a)).
      move=> hx ha; rewrite -(hG x hx) -(hG a ha) -linearB.
      exact: continuous_operator_norm_laws hJ _.
    have hc := (norm_field_continuous_operator hNX hO).1
      (norm_class_one_continuity hD).
    move=> a ha; split.
    * have hh := (norm_class_one_zero hD ha).1; exact hh.
    * exact: hc a ha.
Qed.
