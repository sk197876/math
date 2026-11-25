(** Federer (1969), 3.1.11, p. 222: a local Lipschitz
    bound used when replacing the inner map by its Taylor jet.
    This supporting estimate follows from the differential bound
    of 3.1.1, pp. 210–211, using the project's convex-set theorem. *)
From mathcomp Require Import all_boot all_order all_algebra reals lra
  classical_sets.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormClassOneUP
  InnerConvex NormConvexHullDiameter NormDifferentialConvexBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [norm_class_one_local_lipschitz]: supporting the
    jet-composition limit in Federer 3.1.11, p. 222.
    Every class-one map has a finite Lipschitz bound on a sufficiently
    small ball about each domain point. The proof uses continuity of
    the derivative and 3.1.1's convex-domain increment bound; it does
    not require a Banach space or a finite-dimensional space. *)
Theorem norm_class_one_local_lipschitz (R : realType)
    (X Y : lmodType R) (NX : X->R) (NY : Y->R)
    (hNX : is_real_norm NX) (hNY : is_real_norm NY)
    (A : set X) (f : X->Y) a :
  A a -> norm_class_one NX NY A f ->
  exists C d : R, 0<C /\ 0<d /\
    (forall x, NX (x-a)<d -> A x) /\
    forall x y, NX (x-a)<d -> NX (y-a)<d ->
      NY (f x-f y)<=C*NX (x-y).
Proof.
move=>ha [D hD].
have [C [hC hCa]] := norm_differential_bounded
  (norm_class_one_differential hD ha).
have [r [hr hAr]] := (norm_class_one_zero hD ha).1.
have [s [hs hDs]] := norm_class_one_continuity hD ha ltr01.
pose d := Num.min r s/2.
have hmin : 0<Num.min r s by rewrite lt_min hr hs.
have hd : 0<d by rewrite /d divr_gt0 // ltr0n.
have hdr : d<r.
  have hh : d<Num.min r s by rewrite /d; lra.
  apply: lt_le_trans hh _; by rewrite ge_min lexx.
have hds : d<s.
  have hh : d<Num.min r s by rewrite /d; lra.
  apply: lt_le_trans hh _; by rewrite ge_min lexx orbT.
pose U : set X := [set x | NX (x-a)<=d].
have hU x (hx : U x) : A x /\ forall v, NY (D x v)<=(1+C)*NX v.
  have hshift : a+(x-a)=x by rewrite addrC subrK.
  have hxr : NX (x-a)<r := le_lt_trans hx hdr.
  have hxs : NX (x-a)<s := le_lt_trans hx hds.
  have hAx : A x by rewrite -hshift; exact: hAr (x-a) hxr.
  split; first exact hAx.
  move=>v.
  have hAx' : A (a+(x-a)) by rewrite hshift.
  have hh := hDs (x-a) hAx' hxs v.
  rewrite hshift mul1r in hh.
  change (is_true (NY (D x v-D a v)<=NX v)) in hh.
  have he : D x v=(D x v-D a v)+D a v by rewrite subrK.
  rewrite {1}he; apply: le_trans (real_seminorm_triangle hNY.1 _ _) _.
  have hb := lerD hh (hCa v); by rewrite -{1}[NX v]mul1r -mulrDl in hb.
have hpositive : 0<1+C by lra.
have hbound := @norm_differential_convex_bound R X Y NX NY hNX hNY
  A U f (1+C) (@norm_ball_inner_convex R X NX hNX a d) (ltW hpositive).
have hlocal : forall x y, U x -> U y -> NY (f x-f y)<=(1+C)*NX (x-y).
  apply: hbound=>x hx.
  have [hAx hb] := hU x hx; exists (D x); split; last exact hb.
  exact (norm_class_one_differential hD hAx).
exists (1+C), d; split; first exact hpositive.
split; first exact hd.
split.
- move=>x hx; exact: (hU x (ltW hx)).1.
- move=>x y hx hy; exact (hlocal x y (ltW hx) (ltW hy)).
Qed.
