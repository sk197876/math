(** Supporting general topology for Federer (1969), 3.1.15, pp. 227–228, and
    3.1.16, p. 229: the open annuli {x : i < dist(c,x) < i+1}, i = 0, 1, 2,
    ..., are pairwise disjoint open sets, and a union of closed sets, one
    inside each annulus, is closed. The annuli serve the sigma-finite
    exhaustion of the domain by sets of finite measure. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology
  cardinality.
From Federer Require Import MetricClosedBalls.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [open_annulus]: supporting definition for the exhaustion in
    Federer 3.1.15, pp. 227–228: the set of points at distance strictly
    between i and i+1 from the centre c. *)
Definition open_annulus (R : realType) (T : metricType R) (c : T) (i : nat) : set T :=
  [set x | i%:R<mdist c x<i.+1%:R].

(** Source for [open_annulus_open]: supporting general topology for
    Federer 3.1.15, pp. 227–228: the annulus is the intersection of the
    complement of a closed ball with an open ball. *)
Lemma open_annulus_open (R : realType) (T : metricType R) (c : T) (i : nat) :
  open (open_annulus c i).
Proof.
have he : open_annulus c i
    = (~` metric_closed_ball c i%:R) `&` [set x | mdist c x < i.+1%:R].
  apply/seteqP; split=> x.
  - by move=> /andP [h1 h2]; split=> //; rewrite /metric_closed_ball /= leNgt h1.
  - by move=> [h1 h2]; apply/andP; split=> //; rewrite ltNge; apply/negP.
rewrite he; apply: openI; last exact: metric_open_ball_open.
exact: (closed_openC (@metric_closed_ball_closed R T c i%:R)).
Qed.

(** Source for [open_annulus_disjoint]: supporting general topology for
    Federer 3.1.15, pp. 227–228: a point lies in at most one annulus. *)
Lemma open_annulus_disjoint (R : realType) (T : metricType R) (c : T) (i j : nat) (x : T) :
  open_annulus c i x -> open_annulus c j x -> i=j.
Proof.
move=> /andP [hi1 hi2] /andP [hj1 hj2]; apply/eqP; rewrite eqn_leq; apply/andP; split.
- by rewrite -ltnS -(ltr_nat R); exact: (lt_trans hi1 hj2).
- by rewrite -ltnS -(ltr_nat R); exact: (lt_trans hj1 hi2).
Qed.

(** Source for [annuli_closed_union]: supporting general topology for
    Federer 3.1.15, pp. 227–228, and 3.1.16, p. 229: closed sets F_i inside
    the annuli have a closed union. Near a point x at distance t from the
    centre, with n the integer part of t, the unit ball about x meets only
    the sets F_i with i < n+2; the finite union of these is closed. *)
Theorem annuli_closed_union (R : realType) (T : metricType R) (c : T) (F : nat->set T) :
  (forall i, closed (F i)) -> (forall i, F i `<=` open_annulus c i) ->
  closed (\bigcup_i F i).
Proof.
move=> hcl hsub; rewrite -openC openE=> x hx.
have /andP [hn1 hn2] := truncn_itv (mdist_ge0 c x).
pose n := Num.truncn (mdist c x).
pose G := \bigcup_(i in `I_n.+2) F i.
have hG : closed G by apply: (closed_bigcup (finite_II n.+2))=> i _; exact: hcl.
pose U := (~` G) `&` [set y | mdist x y < 1].
have hUo : open U.
  by apply: openI; [exact: closed_openC hG | exact: metric_open_ball_open].
have hxU : U x.
  split; last by rewrite /= mdistxx ltr01.
  by move=> [i _ hi]; apply: hx; exists i.
have hUsub : U `<=` ~` \bigcup_i F i.
  move=> y [hyG hyx] [i _ hiy]; apply: hyG; exists i=> //.
  have /andP [hi1 hi2] := hsub i y hiy.
  rewrite /= -(ltr_nat R); apply: (lt_trans hi1).
  apply: (le_lt_trans (metric_triangle c x y)).
  by rewrite -natr1; exact: (ltrD hn2 hyx).
exact: (filterS hUsub (open_nbhs_nbhs (conj hUo hxU))).
Qed.
