(** Federer (1969), 3.2.31, p. 269: supporting the
    local unit Lipschitz bound after small linear rescaling.
    On a class-one representative, derivative continuity and
    the earlier convex-domain increment theorem prove it directly. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets.
From Federer Require Import Hom RealNormUP NormClassOneUP InnerConvex
  NormConvexHullDiameter NormDifferentialConvexBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [class_one_half_derivative_local_contraction]:
    supporting the displayed Lip(t^-1 f|E)<= 1 estimate in
    Federer 3.2.31, p. 269. If the actual derivative at
    the center contracts by at most one half, class-one
    continuity gives a neighborhood on which actual function
    increments contract by at most one. This auxiliary C1
    proof avoids assuming the desired local Lipschitz bound. *)
Theorem class_one_half_derivative_local_contraction (R:realType)
    (X Y:lmodType R) (NX:X->R) (NY:Y->R)
    (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (f:X->Y) (D:X->Hom X Y) a:
  is_norm_class_one_field NX NY setT f D ->
  (forall v,NY (D a v)<=(1/2)*NX v) ->
  exists d:R,0<d /\forall x y,NX (x-a)<d ->NX (y-a)<d ->NY (f x-f y)<=NX (x-y).
Proof.
move=>hD hPoint.
have hTwo:(0<(2:R)) by rewrite ltr0n.
have hHalf:(0<(1/2:R)) by rewrite divr_gt0.
have hHalfSum:(1/2+1/2:R)= 1.
  rewrite -mulrDl; change ((2:R)/(2:R)= 1).
  by rewrite divff ?pnatr_eq0.
have [r [hr hRem]]:=@norm_class_one_continuity R X Y NX NY setT f D hD a Logic.I (1/2) hHalf.
pose d:=r/2.
have hd:0<d by rewrite /d divr_gt0.
have hdr:d<r.
  by rewrite /d (@ltr_pdivrMr R 2 r r hTwo) -[ltLHS]mulr1 (ltr_pM2l hr) ltr1n.
pose U:set X:=[set x|NX (x-a)<=d].
have hU x (hx:U x) v:NY (D x v)<=NX v.
  have hSmall:NX (x-a)<r:=le_lt_trans hx hdr.
  have hh:=hRem (x-a) Logic.I hSmall v.
  rewrite (addrC a (x-a)) subrK in hh.
  change (is_true (NY (D x v-D a v)<=(1/2)*NX v)) in hh.
  have hEq:D x v=(D x v-D a v)+D a v by rewrite subrK.
  rewrite hEq; apply:le_trans (real_seminorm_triangle hNY.1 _ _) _.
  have hSum:=lerD hh (hPoint v).
  by rewrite -mulrDl hHalfSum mul1r in hSum.
have hLocal:=@norm_differential_convex_bound R X Y NX NY hNX hNY setT U f 1
  (@norm_ball_inner_convex R X NX hNX a d) ler01.
have hBound:forall x y,U x ->U y ->NY (f x-f y)<= 1*NX (x-y).
  apply:hLocal=>x hx; exists (D x); split.
  - exact (@norm_class_one_differential R X Y NX NY setT f D hD x Logic.I).
  - move=>v; rewrite mul1r; exact (hU x hx v).
exists d; split; first exact hd.
move=>x y hx hy; have hh:=hBound x y (ltW hx) (ltW hy).
by rewrite mul1r in hh.
Qed.
