(** Federer (1969), 3.3.18, p. 301: finite radial
    layers shrinking to their original centre form a closed carrier. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality
  reals topology lra.
From Federer Require Import MetricClosedBalls MetricClosedSeparation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [shrinking_finite_metric_layers_closed]: supporting
    the actual countable topological support in the examples of
    Federer 3.3.18, p. 301. Every layer is finite and all late
    layers lie in every prescribed original neighbourhood of a.
    A finite closed initial part and the triangle inequality
    separate each missing point from the full original carrier. *)
Theorem shrinking_finite_metric_layers_closed (R:realType) (X:metricType R)
    (a:X) (F:nat->set X):
  (forall k,finite_set (F k)) ->
  (forall e:R,0<e ->exists K:nat,forall k,(K<=k)%N ->forall y,F k y ->mdist a y<e) ->
  closed ([set a] `|` \bigcup_k F k).
Proof.
move=>hFinite hSmall.
pose E:=[set a] `|` \bigcup_k F k.
have hOpen:open (~` E).
  rewrite openE=>x hx.
  have hXA:x!=a.
    apply/eqP=>h; apply:hx; left; exact:h.
  have hPositive:0<mdist a x by rewrite mdist_gt0 eq_sym.
  pose e:=mdist a x/3.
  have he:0<e by rewrite /e divr_gt0 // ltr0n.
  have [K hTail]:=hSmall e he.
  pose I:=[set k:nat|(k<K)%N].
  have hI:finite_set I.
    have hEqual:I=`I_K by apply/seteqP; split.
    rewrite hEqual; exact:finite_II.
  pose H:=[set a] `|` \bigcup_(k in I) F k.
  have hHFinite:finite_set H by rewrite finite_setU; split; [exact:finite_set1|exact:bigcup_finite hI (fun k _=>hFinite k)].
  have hHClosed:closed H:=(@accessible_finite_set_closed X).1
    (hausdorff_accessible (@metric_hausdorff R X)) H hHFinite.
  have hSub:H `<=` E.
    move=>y [hy|[k _ hy]]; first by left.
    right; by exists k.
  have hxH:~H x by move=>h; exact:hx (hSub x h).
  have [d [hd hAvoid]]:=closed_set_missing_closed_ball hHClosed hxH.
  pose r:=Num.min d e.
  have hr:0<r by rewrite /r lt_min hd he.
  apply:(metricType_numDomainType.nbhs_mdistP x (~` E)).2.
  exists r; first exact:hr.
  move=>y hNear hEy.
  have hRD:r<=d by rewrite /r ge_min lexx.
  have hRE:r<=e by rewrite /r ge_min lexx orbT.
  have hNearD:mdist x y<=d:=le_trans (ltW hNear) hRD.
  have hNearE:mdist x y<e:=lt_le_trans hNear hRE.
  have hNotH:~H y:=hAvoid y hNearD.
  case:hEy=>[hYA|[k _ hFk]].
  - apply:hNotH; by left.
  - have [hk|hk]:=leqP K k.
    + have hFar:=hTail k hk y hFk.
      have hTriangle:=metric_triangle a y x.
      rewrite (metric_sym y x) in hTriangle.
      rewrite /e in hFar hNearE; lra.
    + apply:hNotH; right; exists k; first exact:hk.
      exact:hFk.
have hClosed:=open_closedC hOpen.
by rewrite setCK in hClosed.
Qed.
