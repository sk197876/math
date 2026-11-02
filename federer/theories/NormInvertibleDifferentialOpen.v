(** Federer (1969), 3.1.23, p. 237: openness follows
    locally from the inverse-function theorem of 3.1.1. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormBoundedLinearTopology CompleteMetricUP
  NormDifferentialUP NormClassOneUP NormClassOneInverseBall.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [norm_invertible_differential_image_open]: openness
    of the straightening map in Federer 3.1.23, p. 237,
    from the already proved inverse-function ball theorem 3.1.1,
    p. 210. The argument works for arbitrary normed spaces
    with complete source, on the actual open domain. *)
Theorem norm_invertible_differential_image_open (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (hcomplete:is_complete_metric_space [the metricType R of real_norm_metric_space hNX])
    (A:set X) (f:X->Y) (D:X->Hom X Y) :
  is_norm_class_one_field NX NY A f D ->
  (forall a,A a -> exists M:Hom Y X,norm_bounded_linear NY NX M /\
    cancel (D a) M /\ cancel M (D a)) ->
  @open (real_norm_metric_space hNY) (f @` A).
Proof.
move=>hf hInv; rewrite openE=>y [a ha <-].
apply: (@norm_domain_interior_neighbourhood R Y NY hNY (f @` A) (f a)).1.
have [M [hM [hMD hDM]]]:=hInv a ha.
have [r [s [K [hr [hs [hK [hAr [hbound [hinj honto]]]]]]]]]:=
  @norm_class_one_inverse_ball R X Y NX NY hNX hNY hcomplete A f D a M
    hf ha hM hMD hDM.
exists s; split=>// h hh.
have hsmall:NY (f a+h-f a)<=s.
  rewrite addrAC subrr add0r; exact: ltW hh.
have [x [hx hfx]]:=honto (f a+h) hsmall.
exists x; first exact (hAr x hx); exact hfx.
Qed.
