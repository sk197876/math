(** Federer (1969), 3.1.24, p. 239: the continuous first
    differential is bounded on a sufficiently small neighbourhood. *)
From mathcomp Require Import all_boot all_order all_algebra reals lra.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormClassOneUP NormClassZeroTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [norm_class_zero_local_bound]: the local bound for
    Df used in the inverse proof of Federer 3.1.24, p. 239.
    Continuity with tolerance one gives a positive radius and a
    positive finite bound on the whole ball, within the actual domain. *)
Lemma norm_class_zero_local_bound (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (A:X->Prop) (f:X->Y) a :
  norm_class_zero NX NY A f -> A a ->
  exists r M:R,0<r /\ 0<M /\ forall x,NX (x-a)<r -> A x /\ NY (f x)<=M.
Proof.
move=>hf ha.
have [r [hr hb]]:=norm_class_zero_local_control hNX hf ha ltr01.
exists r,(NY (f a)+1); split; first exact hr.
split; first by have hn:=real_seminorm_nonnegative hNY.1 (f a); lra.
move=>x hx; have [hAx hfx]:=hb x hx; split; first exact hAx.
have ht:=real_seminorm_triangle hNY.1 (f x-f a) (f a).
rewrite subrK in ht.
apply:le_trans ht _; rewrite addrC.
exact (lerD (lexx _) (ltW hfx)).
Qed.
