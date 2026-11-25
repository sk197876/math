(** Federer (1969), 4.1.14, p. 371: continuous
    scalar tests of uniformly converging maps converge uniformly
    on the original compact support. This is the compact-base
    nearby-continuity consequence of 3.1.11, p. 221.
    No compactness of a whole target or nonempty source is required. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals topology.
From Federer Require Import MetricClosedBalls CompactNearbyUniformContinuity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [metric_compact_uniform_composition]: uniform
    convergence on a compact image remains uniform after a
    continuous target map, supporting the weighted integrals
    in Federer 4.1.14, p. 371. Values of the approximants
    need not lie in the compact image itself. *)
Theorem metric_compact_uniform_composition (R:realType)
    (A:choiceType) (X Y:metricType R) (K:set A)
    (f:A->X) (g:nat->A->X) (h:X->Y):
  compact (f @` K)->continuous h->
  (forall eps:R,0<eps->exists N:nat,forall i:nat,(N<=i)%N->
    forall x,K x->mdist (g i x) (f x)<eps)->
  forall eps:R,0<eps->exists N:nat,forall i:nat,(N<=i)%N->
    forall x,K x->mdist (h (g i x)) (h (f x))<eps.
Proof.
move=>hImage hH hUniform eps hEps.
have hPoint c:(f @` K) c->forall e:R,0<e->exists r:R,
    0<r /\forall y,setT y->mdist c y<r->mdist (h c) (h y)<e.
  move=>_ e he.
  pose O:=[set z:Y|mdist (h c) z<e].
  have hO:nbhs (h c) O.
    apply:open_nbhs_nbhs;split;first exact:metric_open_ball_open.
    by rewrite /O /= mdistxx.
  have hPre:nbhs c (h @^-1` O):=hH c O hO.
  have[r hr hBall]:=(metricType_numDomainType.nbhs_mdistP c _).1 hPre.
  exists r;split;first exact:hr.
  by move=>y _ hy;exact:hBall y hy.
have[d [hd hNearby]]:=@metric_compact_uniform_nearby R X Y setT
  (f @` K) h hImage (fun _ _=>Logic.I) hPoint eps hEps.
have[N hN]:=hUniform d hd.
exists N=>i hi x hx.
have hDistance:mdist (f x) (g i x)<d.
  rewrite metric_sym;exact:hN i hi x hx.
have hValue:=hNearby (f x) (g i x) (imageP f hx) Logic.I hDistance.
by rewrite metric_sym;exact:hValue.
Qed.
