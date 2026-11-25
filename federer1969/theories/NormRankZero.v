(** Federer (1969), 3.1.18, p. 229: at a generic point of rank zero
    the map is constant on a neighbourhood. The proof uses the
    derivative increment bound already proved for 3.1.1. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology lra.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  NormDifferentialConvexBound NormConvexHullDiameter LinearRankUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [norm_generic_rank]: the interior points of the rank-v
    level set in Federer 3.1.18, p. 229. The actual differentiable
    domain is included in the neighbourhood predicate. *)
Definition norm_generic_rank (R : realType) (X Y : lmodType R)
    (NX : X->R) (A : set X) (D : X->Hom X Y) (a:X) v :=
  norm_domain_interior NX (fun x=>A x /\ has_linear_rank (D x) v) a.

(** Source for [norm_generic_rank_at_point]: a generic point itself
    has the prescribed rank and belongs to the domain; supporting the
    generic-point definition of 3.1.18, p. 229. *)
Lemma norm_generic_rank_at_point (R : realType) (X Y : lmodType R)
    (NX : X->R) (hNX : is_real_norm NX) (A:set X) (D:X->Hom X Y) a v :
  norm_generic_rank NX A D a v -> A a /\ has_linear_rank (D a) v.
Proof.
exact (@norm_domain_interior_member R X NX hNX (fun x=>A x /\ has_linear_rank (D x) v) a).
Qed.

(** Source for [norm_generic_rank_zero_locally_constant]: the v=0
    conclusion in Federer 3.1.18, p. 229. This supporting generalization
    works in arbitrary normed spaces and needs no completeness. *)
Theorem norm_generic_rank_zero_locally_constant (R : realType)
    (X Y : lmodType R) (NX:X->R) (NY:Y->R)
    (hNX : is_real_norm NX) (hNY : is_real_norm NY)
    (A:set X) (f:X->Y) (D:X->Hom X Y) a :
  (forall x, A x -> has_norm_differential NX NY A f x (D x)) ->
  norm_generic_rank NX A D a 0%N ->
  exists r:R, 0<r /\ forall x, NX (x-a)<r -> A x /\ f x=f a.
Proof.
move=>hD [d [hd hball]].
pose r := d/2.
have hr : 0<r by rewrite /r divr_gt0 // ltr0n.
have hrd : r<d by rewrite /r; lra.
pose U := fun x=>NX (x-a)<=r.
have hU x (hx:U x) : A x /\ has_linear_rank (D x) 0%N.
  have hh := hball (x-a) (le_lt_trans hx hrd).
  by rewrite (addrC a (x-a)) subrK in hh.
have hder x (hx:U x) : exists L:Hom X Y,
    has_norm_differential NX NY A f x L /\ forall v, NY (L v)<=0*NX v.
  exists (D x); split; first exact: hD x (hU x hx).1.
  move=>v; rewrite ((linear_rank_zeroP (D x)).1 (hU x hx).2 v) (real_seminorm_zero hNY.1) mul0r.
  exact: lexx.
have hb := @norm_differential_convex_bound R X Y NX NY hNX hNY A U f 0
  (@norm_ball_inner_convex R X NX hNX a r) (lexx 0) hder.
have ha : U a by rewrite /U subrr (real_seminorm_zero hNX.1); exact: ltW hr.
exists r; split=>// x hx.
have hux : U x := ltW hx.
split; first exact: (hU x hux).1.
have he := hb x a hux ha; rewrite mul0r in he.
have hz : NY (f x-f a)=0.
  by apply/eqP; rewrite eq_le he (real_seminorm_nonnegative hNY.1) andbT.
apply/eqP; rewrite -subr_eq0; apply/eqP; exact: hNY.2 hz.
Qed.
