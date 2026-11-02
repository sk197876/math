(** Federer (1969), 3.1.20, pp. 232–233: locally stationary
    intermediate maps have an open eventual domain and a class-k
    limit. The ranges and fixed-point laws are those corrected in
    the erratum p. 4, book p. 232 line 11. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormRegularity
  NormRegularityOperations NormRegularityLocal NormClassZeroTopology NormOpenPreimage
  NormBoundedLinearTopology LocalRetractionUP RetractionUP StationaryRetractionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [stationary_retraction_limit]: the conclusion of
    the forward proof of Federer 3.1.20, pp. 232–233, from its
    locally stationary domain and value laws. The hypotheses are
    exactly the intermediate invariants to be proved by the patching
    construction, not an assumed global retraction. *)
Theorem stationary_retraction_limit (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) (B U:set X)
    (W:nat->set X) (f:nat->X->X) k :
  (forall i, is_partial_neighbourhood_retraction hNX B (W i) (f i) k) ->
  (forall i, W i `<=` U) ->
  (forall x, U x -> exists (Q:set X) d,
    @open [the topologicalType of real_norm_metric_space hNX] Q /\ Q x /\
    forall i, (d<=i)%N -> forall y, Q y ->
      (W i y <-> W d y) /\ (W d y -> f i y=f d y)) ->
  B `<=` eventual_open_domain W ->
  exists h:X->X, is_norm_class_retraction hNX (eventual_open_domain W) B h k.
Proof.
move=>hpartial hWU hstation hBA.
pose A:=eventual_open_domain W.
have hAU:A `<=` U.
  move=>x [d hd]; exact: hWU d x (hd d (leqnn d)).
have hEV x (hx:A x):exists y, stationary_map_graph W f x y.
  have [Q [d [hQ [hxQ hstab]]]]:=hstation x (hAU x hx).
  have [e he]:=hx.
  have hmax:W (maxn d e) x:=he _ (leq_maxr d e).
  have hdx:W d x:=(hstab _ (leq_maxl d e) x hxQ).1.1 hmax.
  exists (f d x),d=>i hi; split.
  - exact: (hstab i hi x hxQ).1.2 hdx.
  - exact: (hstab i hi x hxQ).2 hdx.
have hex x:exists y:X, A x -> stationary_map_graph W f x y.
  case: (pselect (A x))=>[hx|hx].
  - have [y hy]:=hEV x hx; by exists y.
  - exists 0=>ha; by exfalso; exact: hx ha.
have [h hh]:=choice hex.
have hclass:norm_class hNX hNX A h k.
  apply: norm_class_local_representatives=>x hx.
  have [Q [d [hQ [hxQ hstab]]]]:=hstation x (hAU x hx).
  have [e he]:=hx.
  have hdx:W d x:=(hstab _ (leq_maxl d e) x hxQ).1.1 (he _ (leq_maxr d e)).
  pose O:=fun y=>W d y /\ Q y.
  have hOA:O `<=` A.
    move=>y [hyW hyQ]; exists d=>i hi; exact: (hstab i hi y hyQ).1.2 hyW.
  have hf:=partial_neighbourhood_retraction_class (hpartial d).
  have hOint y (hy:O y):norm_domain_interior NX O y.
    have hWint:=(norm_class_continuous hf).
    have hQint:=proj2 (@norm_domain_interior_neighbourhood R X NX hNX Q y)
      (open_nbhs_nbhs (conj hQ hy.2)).
    have [r [hr hWr]]:=(@hWint y hy.1).1.
    have [s [hs hQs]]:=hQint.
    exists (Num.min r s); split; first by rewrite lt_min hr hs.
    move=>v; rewrite lt_min=>/andP [hvr hvs]; exact: conj (hWr v hvr) (hQs v hvs).
  exists O,(f d); split; first exact: conj hdx hxQ.
  split; first exact hOA.
  split.
  - exact (@norm_class_open_restriction R X X NX NX hNX hNX (W d) O (f d) k
      (fun y hy=>hy.1) hOint hf).
  - move=>y [hyW hyQ].
    have hgraph:stationary_map_graph W f y (f d y).
      exists d=>i hi; split; [exact: (hstab i hi y hyQ).1.2 hyW|exact: (hstab i hi y hyQ).2 hyW].
    exact: stationary_map_graph_unique hgraph (hh y (hOA y (conj hyW hyQ))).
exists h; constructor=>//.
- move=>x hx; have [d hd]:=hh x hx.
  have [hxW hfx]:=hd d (leqnn d).
  have hb:=@partial_neighbourhood_retraction_range R X NX hNX B (W d) (f d) k (hpartial d) x hxW.
  by rewrite hfx in hb.
- move=>x hx; have [d hd]:=hh x (hBA x hx).
  have [hxW hfx]:=hd d (leqnn d).
  have hfix:=@partial_neighbourhood_retraction_fixed R X NX hNX B (W d) (f d) k (hpartial d) x hx hxW.
  exact (eq_trans (esym hfx) hfix).
Qed.
