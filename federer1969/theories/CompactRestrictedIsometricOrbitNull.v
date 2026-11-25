(** Federer (1969), 3.4.8(8), p. 330:
    restrict an original orthogonal action to
    its invariant sphere without changing the
    original group topology. The existing
    compact transitive action and orbit-null
    theorems supply the measure conclusion. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  constructive_ereal topology subtype_topology.
From Federer Require Import TopologicalGroupUP HomogeneousSpaceUP CompactGroupHomogeneousMeasures
  TopologicalProductMaps IsotropyGroupTopology MetricSubsetBackground HausdorffMeasure HaarIntegralUP CompactIsometricOrbitNull.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [compact_restricted_isometric_orbit_null]:
    the original compact rotation group
    acts on its actual sphere, 3.4.8(8),
    p. 330. The restricted action is
    a local witness; continuity, compatibility,
    transitivity and isometry pass through
    their existing subtype interfaces. *)
Theorem compact_restricted_isometric_orbit_null (R:realType) (G:topologicalType) (X:metricType R)
  (mul:G->G->G) (inv:G->G) (unit:G) (F:G->X->X)
  (hG:is_locally_compact_hausdorff_group mul inv unit) (S:set X)
  d (C:R) (mu:set G->\bar R) (u:X) (hU:S u) (D:set X):
  compact (@setT G) ->
  continuous (fun p:G*X=>F p.1 p.2) ->
  (forall g h x,F (mul g h) x = F g (F h x)) ->
  (forall g x,S x ->S (F g x)) ->
  (forall x y,S x ->S y ->exists g:G,F g x = y) ->
  (forall g x y,mdist (F g x) (F g y) = mdist x y) ->
  0<C ->@hausdorff_measure R [the metricType R of metric_subset S] d setT = C%:E ->
  is_left_haar_measure mul mu ->
  @hausdorff_measure R [the metricType R of metric_subset S] d [set x|D (val x)] = 0%:E ->
  mu [set g:G|D (F g u)] = 0%:E.
Proof.
move=>hCompact hContinuous hCompatible hInvariant hTransitive hDistance hPositive hMass hMu hNull.
pose M:=[the metricType R of metric_subset S].
pose A:G->M->M:=fun (g:G) (x:M)=>exist _ (F g (val x)) (mem_set (hInvariant g (val x) (set_valP x))).
have hAContinuous:continuous (fun p:G*M=>A p.1 p.2).
  apply:set_type_continuous_into.
  have hPair:continuous (fun p:G*M=>(p.1,(val p.2:X)):G*X).
    apply:topological_pair_continuous;first exact:first_projection_continuous.
    move=>p;exact:(continuous_comp (@second_projection_continuous G M p)
      (@metric_subset_inclusion_continuous R X S p.2)).
  move=>p;exact:(continuous_comp (hPair p) (hContinuous (p.1,val p.2))).
have hACompatible g h x:A (mul g h) x = A g (A h x).
  apply:val_inj;exact:hCompatible.
have hATransitive (x y:M):exists g:G,A g x = y.
  have [g hGxy]:=hTransitive (val x) (val y) (set_valP x) (set_valP y).
  exists g;apply:val_inj;exact:hGxy.
have hHomogeneous:=@compact_transitive_homogeneous G M mul inv unit A
  (lch_group_topological hG) hCompact (@metric_hausdorff R M) hAContinuous hACompatible hATransitive.
have hADistance g (x y:M):mdist (A g x:M) (A g y:M) = mdist x y.
  rewrite !metric_subset_distanceE;exact:hDistance.
pose u0:M:=exist _ u (mem_set hU).
exact:(@compact_transitive_isometric_orbit_null R G M mul inv unit A hG hHomogeneous d C mu u0
  [set x:M|D (val x)] hCompact hPositive hMass hADistance hMu hNull).
Qed.
