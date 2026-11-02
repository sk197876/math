(** Federer (1969), 3.1.23, p. 237: a uniformly
    small Lipschitz perturbation of the identity is globally invertible. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology lra.
From Federer Require Import RealNormUP NormMetric.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [norm_identity_perturbation_bounds]: the two-sided
    final increment estimate of Federer 3.1.23, p. 237.
    A Lipschitz bound c for f-id gives lower factor 1-c
    and upper factor 1+c, in every normed space. *)
Lemma norm_identity_perturbation_bounds (R:realType) (X:lmodType R)
    (N:X->R) (hN:is_real_norm N) (f:X->X) c :
  (forall x z,N ((f x-x)-(f z-z))<=c*N (x-z)) ->
  forall x z,(1-c)*N (x-z)<=N (f x-f z) /\
    N (f x-f z)<=(1+c)*N (x-z).
Proof.
move=>hb x z.
have he:(f x-f z)-(x-z)=(f x-x)-(f z-z).
  by rewrite !opprB !addrA [f x-f z+z]addrAC
    [f x+z-f z-x]addrAC [f x-x+z]addrAC.
have hbound:N ((f x-f z)-(x-z))<=c*N (x-z) by rewrite he.
have hupper:=real_seminorm_triangle hN.1 ((f x-f z)-(x-z)) (x-z).
rewrite subrK in hupper.
have hlower:=real_seminorm_triangle hN.1 ((x-z)-(f x-f z)) (f x-f z).
rewrite subrK (real_seminorm_subtract hN.1 (x-z) (f x-f z)) in hlower.
split; nra.
Qed.
