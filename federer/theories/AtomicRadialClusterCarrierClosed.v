(** Federer (1969), 3.3.18, p. 301: the actual
    triangular radial-cluster carrier is closed. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality
  reals topology.
From Federer Require Import EuclideanInnerProduct InnerNorm InnerMetric
  GeometricErrorBudget AtomicRadialClusterBudgets ShrinkingFiniteMetricLayersClosed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [atomic_radial_cluster_carrier_closed]: the countable
    topological-support example mentioned in Federer 3.3.18,
    p. 301. The original triangular carrier has finitely many
    directions at each squared-weight radius. Unit directions
    and the actual geometric tail place all late layers in every
    original neighbourhood of zero. Proved finite-layer closedness
    retains exactly the original carrier; no closure hull is added. *)
Theorem atomic_radial_cluster_carrier_closed (R:realType) n
    (v:nat->inner_metric_space (@euclidean_inner_productP R n))
    (E:set (inner_metric_space (@euclidean_inner_productP R n))):
  (forall j,inner_norm (@euclidean_inner_productP R n) (v j)= 1) ->
  E=([set 0%R] `|` ((fun p:nat*nat=>(geometric_error_budget (1:R) p.2)^+2 *:v p.1) @`
      [set p:nat*nat|(p.1<=p.2)%N])) ->closed E.
Proof.
move=>hUnit hShape.
pose X:=inner_metric_space (@euclidean_inner_productP R n).
pose b:=geometric_error_budget (1:R).
pose F k:=(fun j=>b k^+2 *:v j) @` [set j:nat|(j<=k)%N].
have hFinite k:finite_set (F k).
  apply:finite_image.
  have hEqual:[set j:nat|(j<=k)%N]=`I_k.+1 by apply/seteqP; split.
  rewrite hEqual; exact:finite_II.
have hSmall (e:R):0<e ->exists K:nat,forall k,(K<=k)%N ->forall y,F k y ->mdist (0%R:X) y<e.
  move=>he.
  have hMin:0<Num.min 1 e by rewrite lt_min ltr01 he.
  have [K hK]:=@atomic_radial_cluster_budget_small R (Num.min 1 e) hMin.
  exists K=>k hk y [j hj <-].
  have hb:0<b k:=geometric_error_budget_positive k (@ltr01 R).
  have hWeight:b k<Num.min 1 e:=hK k hk.
  have hOne:b k<= 1.
    apply:ltW; apply:lt_le_trans hWeight _; by rewrite ge_min lexx.
  have hRadiusBound:b k<e.
    apply:lt_le_trans hWeight _; by rewrite ge_min lexx orbT.
  have hSquare:b k^+2<=b k.
    have h:=ler_wpM2r (ltW hb) hOne; by rewrite mul1r -expr2 in h.
  rewrite inner_metric_distanceE sub0r inner_normN inner_normZ
    (ger0_norm (sqr_ge0 (b k))) hUnit mulr1.
  exact:le_lt_trans hSquare hRadiusBound.
have hLayers:E=[set (0%R:X)] `|` \bigcup_k F k.
  rewrite hShape; apply/seteqP; split.
  - move=>x [hx|[p hp <-]]; first by left.
    right; exists p.2; first exact:Logic.I.
    by exists p.1.
  - move=>x [hx|[k _ [j hj <-]]]; first by left.
    right; by exists (j,k).
rewrite hLayers.
exact:shrinking_finite_metric_layers_closed hFinite hSmall.
Qed.
