(** Federer (1969), 3.3.19, p. 303: supporting
    finite-cover compactness. A sufficiently small original
    set meeting the compact source lies in one original
    open cover member. This is general metric topology. *)
From mathcomp Require Import all_boot all_order all_algebra finmap reals boolp classical_sets cardinality topology lra.
From Federer Require Import CoveringFamilyUP CompactFiniteCover FiniteRealMaximum MetricClosedBalls.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [compact_metric_open_cover_number]: the
    uniform small-set consequence of compactness used to
    put each original G_n disc in a cover member,
    3.3.19, p. 303. All cover members and the
    original compact set are retained; no Lebesgue number
    is supplied as an additional hypothesis. *)
Theorem compact_metric_open_cover_number (R:realType) (X:metricType R)
    (I:choiceType) (D:set I) (U:I->set X) (K:set X):
  K!=set0 ->compact K ->(forall i,D i ->open (U i)) ->
  K `<=` \bigcup_(i in D) U i ->
  exists d:R,0<d /\forall S:set X,K `&` S!=set0 ->
    (forall x y,S x ->S y ->mdist x y<d) ->
    exists i,D i /\S `<=` U i.
Proof.
move=>hNonempty hK hOpen hCover.
pose J:=(I*(X* R))%type.
pose P:set J:=[set p|D p.1 /\K p.2.1 /\(0<p.2.2)%R /\
  (@metric_open_ball R X p.2.1 (2* p.2.2)) `<=` U p.1].
pose V:=fun p:J=>@metric_open_ball R X p.2.1 p.2.2.
have hRefinement:K `<=` \bigcup_(p in P) V p.
  move=>x hx;have [i hi hxU]:=hCover x hx.
  have hNeighbour:nbhs x (U i) by apply:open_nbhs_nbhs;split;[exact:hOpen i hi|exact hxU].
  have [r hr hBall]:=(proj1 (metricType_numDomainType.nbhs_mdistP x (U i))) hNeighbour.
  have hQuarter:0<r/4 by rewrite divr_gt0 // ltr0n.
  exists (i,(x,r/4));last by rewrite /V /metric_open_ball /= mdistxx.
  split=>//;split=>//;split=>//.
  move=>y hy;change (is_true (mdist x y<2*(r/4))) in hy.
  have hSmall:mdist x y<r by lra.
  exact:hBall y hSmall.
have [F hFP hFCover]:=@compact_open_finite_cover X [the choiceType of J] P V K hK
  (fun (p:J) _=>@metric_open_ball_open R X p.2.1 p.2.2) hRefinement.
have hFNonempty:[set` F]!=set0.
  have [x hx]:=hNonempty;have [p hp _]:=hFCover x hx;by exists p.
have hFFinite:finite_set [set` F] by apply/finite_fsetP;by exists F.
have [p [hp hMinimum]]:=@finite_nonempty_real_maximum R [the choiceType of J]
  [set` F] (fun p:J=> -p.2.2) hFFinite hFNonempty.
have hP p':p' \in F ->P p' by move=>hp';apply/set_mem;exact:hFP p' hp'.
have hPositive:0<p.2.2:=(hP p hp).2.2.1.
exists p.2.2;split=>//;move=>S [x [hxK hxS]] hSmall.
have [q hq hxV]:=hFCover x hxK.
have hQ:=hP q hq.
have hMinimumQ:p.2.2<=q.2.2 by have hh:=hMinimum q hq;by rewrite lerN2 in hh.
exists q.1;split;first exact:hQ.1.
move=>y hy;apply:hQ.2.2.2.
change (is_true (mdist q.2.1 y<2* q.2.2)).
have hX:mdist q.2.1 x<q.2.2:=hxV.
have hY:=hSmall x y hxS hy.
have hTriangle:=metric_triangle q.2.1 x y;lra.
Qed.
