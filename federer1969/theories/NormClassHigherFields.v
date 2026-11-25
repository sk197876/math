(** Federer (1969), 3.1.11, pp. 219–221:
    simultaneous representatives of all derivatives through
    a fixed class order. Their exact graphs and
    derivative compatibility, rather than any implementation
    of the higher differential, govern their use. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormClassOneUP
  PartialFunctionUP PartialFunctionExtensionUP PartialFunctionExtensionSealed
  ContinuousMultilinearUP NormHigherDifferentialUP NormHigherDifferential
  NormHigherDifferentialFields NormClassHigherUP NormClassHigherLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

Section Fields.
Variable R : realType.
Variables X Y : lmodType R.
Variables (NX : X->R) (NY : Y->R).
Hypothesis hNX : is_real_norm NX.
Hypothesis hNY : is_real_norm NY.
Variable Z : nat->lmodType R.
Variable evaluation : forall k, {ffun 'I_k->X}->Hom (Z k) Y.
Variable ZN : forall k, Z k->R.
Hypothesis hZ : forall k, is_continuous_multilinear_space NX NY (@evaluation k) (@ZN k).

(** Source for [norm_class_higher_fields]:
    representatives of D^i f for every i
    through the class order, Federer 3.1.11,
    pp. 220–221. Outside their exact domains
    the chosen representatives have no asserted value;
    only their existence and laws are exposed. *)
Theorem norm_class_higher_fields (A : X->Prop) (f : X->Y) k :
  norm_class_higher NX NY evaluation ZN A f k ->
  exists D : forall i, X->Z i,
    (forall i, (i<=k)%N -> forall a, A a ->
      has_norm_higher_differential NX evaluation ZN A f i a (D i a)) /\
    (forall i, (i<=k)%N ->
      norm_class_zero NX (@ZN i) A (D i)).
Proof.
move=> hk.
pose H i := @norm_higher_differential R X Y NX NY hNX hNY
  Z evaluation ZN hZ A f i.
pose D i := @PartialFunctionExtension.value X (Z i) (H i) 0.
have hrep i x w :
    has_norm_higher_differential NX evaluation ZN A f i x w -> D i x=w.
  move=> hw; apply: (@PartialFunctionExtension.laws X (Z i) (H i) 0 x w).
  exact: (@norm_higher_differential_graph R X Y NX NY hNX hNY
    Z evaluation ZN hZ A f i x w).2 hw.
exists D; split.
- move=> i hi.
  have [_ [G [hG hcG]]] := @norm_class_higher_lower R X Y NX NY
    hNX hNY Z evaluation ZN hZ A f k i hi hk.
  move=> a ha; rewrite (hrep i a (G a) (hG a ha)); exact (hG a ha).
- move=> i hi.
  have [_ [G [hG hcG]]] := @norm_class_higher_lower R X Y NX NY
    hNX hNY Z evaluation ZN hZ A f k i hi hk.
  move=> a ha; split; first exact: (hcG a ha).1.
  move=> e he; have [d [hd hb]] := (hcG a ha).2 e he.
  exists d; split=> // h hh hs.
  rewrite (hrep i (a+h) (G (a+h)) (hG _ hh)) (hrep i a (G a) (hG _ ha)).
  exact: hb h hh hs.
Qed.
End Fields.
