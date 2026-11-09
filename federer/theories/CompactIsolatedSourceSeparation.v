(** Federer (1969), 3.4.2(7), p. 312: compact subsets of a discrete
    source have a uniform scale excluding distinct source pairs. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals topology.
From Federer Require Import RealNormUP NormMetric NormDifferentialUP
  SubmanifoldBasicLaws CoveringFamilyUP CompactMetricOpenCoverNumber MetricClosedBalls.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [compact_isolated_source_separation]: supporting the
    discrete case mu=nu=0 in the proof of 3.4.2(7), p. 312, and the
    dimension-zero case of (6). Compactness gives one positive radius
    at which every original source point near an original compact-set
    point must equal it. No finiteness premise is supplied. *)
Theorem compact_isolated_source_separation (R:realType) (X:lmodType R)
    (N:X->R) (hN:is_real_norm N) (S C:set X):
  @compact (real_norm_metric_space hN) C ->
  (forall c,C c ->norm_isolated_point N S c) ->
  exists d:R,0<d /\forall x c,S x ->C c ->N (x-c)<d ->x=c.
Proof.
move=>hC hIso.
case:(pselect (C!=set0))=>[hNonempty|hEmpty];last first.
  exists 1;split;first exact:ltr01.
  move=>x c hx hc hdist;exfalso;apply:hEmpty;by exists c.
pose M:=real_norm_metric_space hN.
have hex c:exists r:R,0<r /\
    (C c ->forall x,S x ->mdist (c:M) x<r ->x=c).
  case:(pselect (C c))=>[hc|hc];last first.
    exists 1;split;first exact:ltr01.
    by move=>/hc.
  have [_ [r [hr hBall]]]:=hIso c hc.
  exists r;split;first exact:hr.
  move=>_ x hx hd.
  have hNdist:N (x-c)<r.
    rewrite -(real_seminorm_subtract hN.1 c x).
    exact:hd.
  have hh:=hBall (x-c) hNdist.
  by rewrite addrC subrK in hh;exact:hh hx.
have [rho hRho]:=choice hex.
pose U (c:M):set M:=@metric_open_ball R M c (rho c).
have hCover:C `<=` \bigcup_(c in C) U c.
  move=>c hc;exists c;first exact:hc.
  change (is_true (N (c-c)<rho c)).
  by rewrite subrr (real_seminorm_zero hN.1);exact:(hRho c).1.
have [d [hd hD]]:=@compact_metric_open_cover_number R M [the choiceType of M]
  C U C hNonempty hC (fun c _=>@metric_open_ball_open R M c (rho c)) hCover.
exists d;split;first exact:hd.
move=>x c hx hc hdist.
pose P:set M:=[set y|y=x \/y=c].
have hMeet:C `&` P!=set0.
  exists c;split;first exact:hc.
  by right.
have hSmall:forall u v,P u ->P v ->mdist u v<d.
  move=>u v [->|->] [->|->].
  - change (is_true (N (x-x)<d)).
    by rewrite subrr (real_seminorm_zero hN.1).
  - exact:hdist.
  - change (is_true (N (c-x)<d)).
    by rewrite (real_seminorm_subtract hN.1 c x).
  - change (is_true (N (c-c)<d)).
    by rewrite subrr (real_seminorm_zero hN.1).
have [a [ha hPA]]:=hD P hMeet hSmall.
have hXa:mdist (a:M) x<rho a:=hPA x (or_introl (erefl x)).
have hCa:mdist (a:M) c<rho a:=hPA c (or_intror (erefl c)).
have hSc:S c:=(hIso c hc).1.
exact:(eq_trans ((hRho a).2 ha x hx hXa) (esym ((hRho a).2 ha c hSc hCa))).
Qed.
