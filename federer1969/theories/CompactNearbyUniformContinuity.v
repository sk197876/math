(** Federer (1969), 3.1.11, p. 221:
    uniform continuity near a compact set of base points,
    supporting the uniform Taylor remainder. The second
    point may lie outside the compact set, in the open
    function domain. No finite dimension is required. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp
  classical_sets reals topology lra.
From Federer Require Import CompactFiniteCover MetricClosedBalls RealNormUP NormMetric
  NormClassOneUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [metric_compact_uniform_nearby]:
    the compact-base uniformity used in the Taylor
    remainder assertion of Federer 3.1.11, p. 221.
    A finite cover by half continuity balls gives
    one radius for all base points in K. *)
Theorem metric_compact_uniform_nearby (R : realType) (X Y : metricType R)
    (A K : set X) (f : X->Y) :
  compact K -> K `<=` A ->
  (forall c, K c -> forall e : R, 0<e ->
    exists r, 0<r /\ forall y, A y -> mdist c y<r -> mdist (f c) (f y)<e) ->
  forall e : R, 0<e -> exists d, 0<d /\
    forall x y, K x -> A y -> mdist x y<d -> mdist (f x) (f y)<e.
Proof.
move=> hK hKA hc e he.
have he2 : 0<e/2 by rewrite divr_gt0 // ltr0n.
have hex c : exists r : R, 0<r /\
    (K c -> forall y, A y -> mdist c y<r -> mdist (f c) (f y)<e/2).
  case: (pselect (K c))=> [hkc|hkc].
  - have [r [hr hb]] := hc c hkc _ he2; exists r; by split=> // _.
  - exists 1; split; first exact: ltr01; by move=> /hkc.
have [rad hrad] := choice hex.
have hcover : K `<=` \bigcup_(c in K) [set y | mdist c y<rad c/2].
  move=> x hx; exists x=> //; rewrite /= mdistxx divr_gt0 //; exact: (hrad x).1.
have [F hFK hF] := @compact_open_finite_cover X X K
  (fun c=>[set y | mdist c y<rad c/2]) K hK
  (fun c _=>metric_open_ball_open c (rad c/2)) hcover.
pose d := \big[Order.min/1]_(i : F) (rad (val i)/2).
have hd : 0<d.
  rewrite /d; apply: (big_ind (fun z : R=>0<z)).
  - exact: ltr01.
  - by move=> u v hu hv; rewrite lt_min hu hv.
  - move=> i _; by rewrite divr_gt0 //; exact: (hrad (val i)).1.
have hdc c : c \in F -> d<=rad c/2.
  move=> hcf; exact: (bigmin_le 1 [` hcf]%fset (fun i : F=>rad (val i)/2)).
exists d; split=> // x y hx hy hxy.
have [c hcf hcx] := hF x hx.
have hkc : K c := set_mem (hFK c hcf).
have hrc := (hrad c).1.
change (is_true (mdist c x<rad c/2)) in hcx.
have hcxr : mdist c x<rad c by lra.
have hcyr : mdist c y<rad c.
  have hdist := metric_triangle c x y.
  have hsmall := lt_le_trans hxy (hdc c hcf).
  lra.
have hfx := (hrad c).2 hkc x (hKA x hx) hcxr.
have hfy := (hrad c).2 hkc y hy hcyr.
have hdist := metric_triangle (f x) (f c) (f y).
rewrite (metric_sym (f x) (f c)) in hdist.
have hb := le_lt_trans hdist (ltrD hfx hfy).
have hs : e/2+e/2=e by lra.
by rewrite hs in hb.
Qed.

(** Source for [norm_class_zero_compact_uniform_nearby]:
    continuity of the kth differential implies a
    uniform modulus near compact base sets, as used
    in Federer 3.1.11, p. 221. This supporting
    norm formulation retains the surrounding domain A. *)
Theorem norm_class_zero_compact_uniform_nearby (R : realType)
    (X Y : lmodType R) (NX : X->R) (NY : Y->R)
    (hNX : is_real_norm NX) (hNY : is_real_norm NY)
    (A K : set X) (f : X->Y) :
  compact [set x : real_norm_metric_space hNX | K x] ->
  K `<=` A -> norm_class_zero NX NY A f ->
  forall e : R, 0<e -> exists d, 0<d /\
    forall x y, K x -> A y -> NX (y-x)<d -> NY (f y-f x)<e.
Proof.
move=> hK hKA hf e he.
have hc c : K c -> forall t : R, 0<t ->
    exists r, 0<r /\ forall y, A y ->
      mdist (c : real_norm_metric_space hNX) y<r ->
      mdist (f c : real_norm_metric_space hNY) (f y)<t.
  move=> hk t ht; have [r [hr hb]] := (hf c (hKA c hk)).2 _ ht.
  exists r; split=> // y hy hh.
  have hshift : c+(y-c)=y by rewrite addrC subrK.
  have hs : NX (y-c)<r.
    change (is_true (NX (c-y)<r)) in hh.
    by rewrite (real_seminorm_subtract hNX.1).
  have hy' : A (c+(y-c)) by rewrite hshift.
  have hh' := hb (y-c) hy' hs; rewrite hshift in hh'.
  change (is_true (NY (f c-f y)<t)).
  by rewrite (real_seminorm_subtract hNY.1).
have [d [hd hb]] := @metric_compact_uniform_nearby R
  (real_norm_metric_space hNX) (real_norm_metric_space hNY)
  A K f hK hKA hc e he.
exists d; split=> // x y hx hy hsmall.
have hs : mdist (x : real_norm_metric_space hNX) y<d.
  change (is_true (NX (x-y)<d)); by rewrite (real_seminorm_subtract hNX.1).
have hh := hb x y hx hy hs.
change (is_true (NY (f x-f y)<e)) in hh.
by rewrite (real_seminorm_subtract hNY.1).
Qed.
