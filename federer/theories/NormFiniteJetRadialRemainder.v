(** Federer (1969), 3.4.5, pp. 318–321: equal
    actual finite jets have a negligible difference along
    every original line, by 3.1.11, pp. 221–222. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets.
From Federer Require Import Hom RealNormUP ContinuousMultilinearUP NormHigherDifferentialUP NormClassHigherUP
  NormLittleOPower NormLittleOPullback NormFiniteJetAgreement NormFiniteJetUniformRemainder.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [norm_finite_jet_radial_remainder]: the
    difference of two functions with equal actual kth
    jets is o(|t|^k) on every line through their
    original centre, supporting 3.4.5, pp. 318–321. *)
Theorem norm_finite_jet_radial_remainder (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (Z:nat->lmodType R) (ev:forall i,{ffun 'I_i->X}->Hom (Z i) Y) (NZ:forall i,Z i->R)
    (hZ:forall i,is_continuous_multilinear_space NX NY (@ev i) (@NZ i))
    (A B:set X) (f g:X->Y) k a:
  A a ->B a ->norm_class_higher NX NY ev NZ A f k ->norm_class_higher NX NY ev NZ B g k ->
  norm_finite_jet_agreement NX ev NZ A B f g k a ->
  forall v,norm_little_o_power NY (fun t=>f (a+t*:v)-g (a+t*:v)) k.
Proof.
move=>ha hb hf hg hAgree v.
pose rho:=fun h:X=>f (a+h)-g (a+h).
have hBound (t:R) (_:`|t|<(1:R)):NX (t*:v)<=NX v*`|t|.
  by rewrite (real_seminorm_scale hNX.1) mulrC.
exact:(@norm_little_o_power_pullback R X Y NX NY hNX rho (fun t=>t*:v) k (NX v) 1
  (real_seminorm_nonnegative hNX.1 v) ltr01 hBound
  (@norm_finite_jet_uniform_remainder R X Y NX NY hNX hNY Z ev NZ hZ A B f g k a
    ha hb hf hg hAgree)).
Qed.
