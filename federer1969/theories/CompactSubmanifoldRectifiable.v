(** Federer (1969), 3.2.28, pp. 265–267:
    compact smooth manifolds in the area/coarea applications
    are rectifiable and have finite Hausdorff mass. A finite
    chart cover proves this prerequisite, including degree zero. *)
From mathcomp Require Import all_boot all_order all_algebra finmap reals classical_sets cardinality topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric InnerNormedTopology
  RectifiableSetUP RectifiableElementary RectifiableUnion RectifiableFiniteHausdorffMass
  EuclideanSubmanifoldUP SubmanifoldLocalRectifiable HausdorffMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [rectifiable_finite_indexed_union]: the finite
    chart cover used in Federer 3.2.28, pp. 265–267,
    by the union observation following 3.2.14, p. 252.
    The image sets need not be measurable or closed. *)
Lemma rectifiable_finite_indexed_union (R:realType) (X:metricType R) m
    (I:choiceType) (D:set I) (F:I->set X):
  finite_set D ->(forall i,D i ->is_m_rectifiable m (F i)) ->
  is_m_rectifiable m (\bigcup_(i in D) F i).
Proof.
move=>/finite_fsetP [A ->]; elim/fset1U_rect:A=>[|a A ha IH] hF.
- rewrite set_fset0 bigcup_set0; exact:rectifiable_empty.
- rewrite set_fsetU1 bigcup_setU1; rewrite set_fsetU1 in hF.
  apply:rectifiable_union.
  + apply:hF; by left.
  + apply:IH=>i hi; apply:hF; by right.
Qed.

(** Source for [compact_submanifold_rectifiable]: the actual
    finite-mass rectifiability prerequisite for the area/coarea
    arguments in Federer 3.2.28, pp. 265–267. The
    compact subset may be arbitrary within a class-k
    manifold, k>=1; its finite chart cover is proved. *)
Theorem compact_submanifold_rectifiable (R:realType) n mu k
    (B K:set (R_n R n)):
  (1<=k)%N ->@is_euclidean_submanifold R n mu k B ->K `<=` B ->
  @compact [the topologicalType of inner_metric_space (@euclidean_inner_productP R n)] K ->
  @is_m_rectifiable R (inner_metric_space (@euclidean_inner_productP R n)) mu K.
Proof.
move=>hk hB hKB hK.
pose X:=inner_metric_space (@euclidean_inner_productP R n).
pose D:set (set X):=[set U:set X|open U /\@is_m_rectifiable R X mu (B `&` U)].
have hCover:K `<=` \bigcup_(U in D) U.
  move=>x hx; have [U [hU [hxU hRect]]]:=submanifold_local_rectifiable hk hB (hKB x hx).
  exists U; first by split.
  exact hxU.
have hCK:@cover_compact [the topologicalType of X] K.
  by rewrite -(@compact_cover [the ptopologicalType of X]).
have [F hFD hFK]:=hCK [the choiceType of set X] D id (fun U hU=>hU.1) hCover.
have hUnion:@is_m_rectifiable R X mu (\bigcup_(U in [set` F]) (B `&` U)).
  apply:(@rectifiable_finite_indexed_union R X mu [the choiceType of set X]
    [set` F] (fun U=>B `&` U) (finite_fset F)).
  move=>U hU; have hDU:D U by apply/set_mem; exact:hFD U hU.
  exact hDU.2.
apply:(rectifiable_subset _ hUnion)=>x hx.
have [U hU hxU]:=hFK x hx.
exists U; first exact hU.
by split; first exact:hKB x hx.
Qed.

(** Source for [compact_submanifold_measure_rectifiable]:
    actual (H^mu,mu) rectifiability in the applications
    of Federer 3.2.28, pp. 265–267. Finiteness is
    derived from the bounded parametrizations, not assumed. *)
Theorem compact_submanifold_measure_rectifiable (R:realType) n mu k
    (B K:set (R_n R n)):
  (1<=k)%N ->@is_euclidean_submanifold R n mu k B ->K `<=` B ->
  @compact [the topologicalType of inner_metric_space (@euclidean_inner_productP R n)] K ->
  is_measure_m_rectifiable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R n)) mu) mu K.
Proof.
move=>hk hB hKB hK; apply:rectifiable_hausdorff_measure_rectifiable.
exact:compact_submanifold_rectifiable hk hB hKB hK.
Qed.
