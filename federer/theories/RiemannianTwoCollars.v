(** Federer (1969), 3.2.46, printed p. 281: the lower comparison
    with Euclidean curve length must include curves leaving the local
    comparison neighbourhood. This supporting norm estimate retains
    both endpoint collars. Crossing-time existence is proved separately. *)
From mathcomp Require Import all_boot all_order all_algebra reals lra.
From Federer Require Import RealNormUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [norm_two_collar_lower_bound]: supporting the lower
    distance comparison in Federer 3.2.46, p. 281. If both endpoints
    lie in the half ball and u,v lie on the full sphere, the sum of
    the two collar displacements bounds the endpoint displacement.
    No convexity or containment of the intervening curve is assumed. *)
Lemma norm_two_collar_lower_bound (R : realType) (V : lmodType R)
    (N : V -> R) (hN : is_real_norm N) a x y u v (d : R) :
  N (x-a) <= d/2 -> N (y-a) <= d/2 ->
  N (u-a) = d -> N (v-a) = d ->
  N (x-y) <= N (u-x)+N (y-v).
Proof.
move=> hx hy hu hv.
have hxy : N (x-y) <= N (x-a)+N (y-a).
  have he : x-y = (x-a)+(a-y) by rewrite addrA subrK.
  rewrite he; apply: le_trans (real_seminorm_triangle hN.1 _ _) _.
  by rewrite (real_seminorm_subtract hN.1 a y).
have hux : d <= N (u-x)+N (x-a).
  rewrite -hu; have he : u-a = (u-x)+(x-a) by rewrite addrA subrK.
  rewrite he; exact: real_seminorm_triangle hN.1 _ _.
have hyv : d <= N (y-v)+N (y-a).
  rewrite -hv; have he : v-a = (v-y)+(y-a) by rewrite addrA subrK.
  rewrite he (real_seminorm_subtract hN.1 y v).
  exact: real_seminorm_triangle hN.1 _ _.
lra.
Qed.
