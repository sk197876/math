(** Federer (1969), 3.1.11, p. 221:
    a compact set of base points in an open
    domain has one positive radius that keeps
    all the short Taylor segments in the domain. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp
  classical_sets reals topology lra.
From Federer Require Import CompactFiniteCover MetricClosedBalls RealNormUP NormMetric
  NormDifferentialUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [metric_compact_uniform_domain_radius]:
    the compact-domain neighborhood needed for
    uniformity in Federer 3.1.11, p. 221.
    A finite cover gives a common positive
    radius without finite-dimensional or local
    compactness assumptions on the ambient space. *)
Theorem metric_compact_uniform_domain_radius (R : realType) (X : metricType R)
    (A K : set X) :
  compact K ->
  (forall c, K c -> exists r : R, 0<r /\
    forall y, mdist c y<r -> A y) ->
  exists d : R, 0<d /\ forall x y, K x -> mdist x y<d -> A y.
Proof.
move=> hK hc.
have hex c : exists r : R, 0<r /\
    (K c -> forall y, mdist c y<r -> A y).
  case: (pselect (K c))=>[hk|hk].
  - have [r [hr hb]] := hc c hk; exists r; by split=> // _.
  - exists 1; split; first exact: ltr01; by move=> /hk.
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
exists d; split=> // x y hx hxy.
have [c hcf hcx] := hF x hx.
apply: ((hrad c).2 (set_mem (hFK c hcf)) y).
change (is_true (mdist c x<rad c/2)) in hcx.
have hdist := metric_triangle c x y.
have hsmall := lt_le_trans hxy (hdc c hcf).
lra.
Qed.

(** Source for [norm_compact_uniform_domain_radius]:
    the norm-ball form of the common domain
    radius used in Federer 3.1.11, p. 221.
    In particular the statement includes an empty
    compact set and arbitrary normed source spaces. *)
Theorem norm_compact_uniform_domain_radius (R : realType)
    (X : lmodType R) (NX : X->R) (hNX : is_real_norm NX)
    (A K : set X) :
  compact [set x : real_norm_metric_space hNX | K x] ->
  (forall a, K a -> norm_domain_interior NX A a) ->
  exists d : R, 0<d /\ forall a v, K a -> NX v<d -> A (a+v).
Proof.
move=> hK hA.
have hc c : K c -> exists r : R, 0<r /\
    forall y, mdist (c : real_norm_metric_space hNX) y<r -> A y.
  move=> hk; have [r [hr hb]] := hA c hk.
  exists r; split=> // y hy.
  have hshift : c+(y-c)=y by rewrite addrC subrK.
  rewrite -hshift; apply: hb.
  change (is_true (NX (c-y)<r)) in hy.
  by rewrite (real_seminorm_subtract hNX.1).
have [d [hd hb]] := @metric_compact_uniform_domain_radius R
  (real_norm_metric_space hNX) A K hK hc.
exists d; split=> // a v ha hv.
apply: (hb a (a+v) ha).
change (is_true (NX (a-(a+v))<d)).
have he : a-(a+v)= -v by rewrite opprD addrA subrr add0r.
by rewrite he (real_seminorm_negate hNX.1).
Qed.
