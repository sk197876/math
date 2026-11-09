(** Federer (1969), 3.4.4, p. 318: convert
    the vanishing first Whitney form into the actual zero differential. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom RealNormUP SymmetricForms ContinuousMultilinearUP
  ContinuousMultilinearOne NormDifferentialUP NormHigherDifferentialUP
  NormHigherDifferentialFirst NormHigherSymmetricFormUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [first_zero_form_is_zero_differential]: the
    first-order case of g^(i)(a)=0 in 3.4.4,
    p. 318. The existing identification of the first
    higher differential with the ordinary differential proves
    that its actual linear map is zero. *)
Lemma first_zero_form_is_zero_differential (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (Z:nat->lmodType R) (ev:forall i,{ffun 'I_i->X}->Hom (Z i) Y)
    (ZN:forall i,Z i->R)
    (hZ:forall i,is_continuous_multilinear_space NX NY (@ev i) (@ZN i))
    A (f:X->Y) a:
  is_norm_higher_differential_form NX ev ZN A f 1 a 0 ->
  has_norm_differential NX NY A f a 0.
Proof.
move=>[z [hz hEvaluation]].
have hD:=(@norm_higher_differential_first R X Y NX NY hNX hNY Z ev ZN hZ A f a z).1 hz.
have hOperator:@continuous_multilinear_one_operator R X Y (Z 1%N) NX NY
    (@ev 1%N) (@ZN 1%N) (hZ 1%N) z=0.
  apply:hom_ext=>v.
  change (@ev 1%N [ffun i=>v] z=(0:Hom X Y) v).
  by rewrite hEvaluation sform_zeroE hom_zeroE.
by rewrite hOperator in hD.
Qed.
