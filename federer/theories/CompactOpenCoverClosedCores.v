(** Federer (1969), 3.2.47, p. 283: supporting
    reduction to finitely many compact base cores inside actual
    translated open patches. This is general metric topology from
    the finite-cover principle of 2.2.5, p. 63,
    and imposes no properness or finite-dimensional hypothesis. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp finmap classical_sets topology lra.
From Federer Require Import CoveringFamilyUP MetricClosedBalls CompactFiniteCover.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [compact_open_cover_closed_cores]: finitely many
    compact intersections of the original compact S with
    closed balls cover S and stay inside individual original
    open patches. This supplies the compact refinement in
    the local product argument of 3.2.47, p. 283. *)
Theorem compact_open_cover_closed_cores (R:realType) (X:metricType R)
    (I:choiceType) (D:set I) (U:I->set X) (S:set X):
  compact S ->(forall i,D i ->open (U i)) ->S `<=` \bigcup_(i in D) U i ->
  exists F:{fset (I*(X*R))%type},
    (forall p,p \in F ->D p.1 /\(0<p.2.2)%R /\
      compact (S `&` metric_closed_ball p.2.1 p.2.2) /\
      S `&` metric_closed_ball p.2.1 p.2.2 `<=` U p.1) /\
    S `<=` \bigcup_(p in [set` F]) (S `&` metric_closed_ball p.2.1 p.2.2).
Proof.
move=>hS hOpen hCover.
pose J:=(I*(X*R))%type.
pose P:set J:=[set p|D p.1 /\S p.2.1 /\(0<p.2.2)%R /\
  metric_closed_ball p.2.1 p.2.2 `<=` U p.1].
pose V:=fun p:J=>@metric_open_ball R X p.2.1 p.2.2.
have hRefinement:S `<=` \bigcup_(p in P) V p.
  move=>x hx; have [i hi hxU]:=hCover x hx.
  have hNeighbour:nbhs x (U i).
    apply:open_nbhs_nbhs; split; first exact:hOpen i hi.
    exact hxU.
  have [d hd hBall]:=(proj1 (metricType_numDomainType.nbhs_mdistP x (U i))) hNeighbour.
  have hHalf:0<d/2 by rewrite divr_gt0 // ltr0n.
  have hLess:d/2<d by nra.
  exists (i,(x,d/2)); last by rewrite /V /metric_open_ball /= mdistxx.
  split; first exact hi.
  split; first exact hx.
  split; first exact hHalf.
  move=>y hy; exact:hBall y (le_lt_trans hy hLess).
have [F hFP hFS]:=@compact_open_finite_cover X
  [the choiceType of J] P V S hS (fun (p:J) _=>@metric_open_ball_open R X p.2.1 p.2.2) hRefinement.
exists F; split.
- move=>p hp; have hP:P p by apply/set_mem; exact:hFP p hp.
  split; first exact hP.1.
  split; first exact hP.2.2.1.
  split; first exact (@compact_closedI X S (metric_closed_ball p.2.1 p.2.2) hS
    (@metric_closed_ball_closed R X p.2.1 p.2.2)).
  by move=>x hx; exact:hP.2.2.2 x hx.2.
- move=>x hx; have [p hp hxV]:=hFS x hx.
  exists p; first exact hp; split; first exact hx.
  exact:ltW hxV.
Qed.
