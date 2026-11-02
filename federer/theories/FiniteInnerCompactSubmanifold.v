(** Federer (1969), 3.2.28, pp. 265–267:
    compact subsets of the finite inner-product manifolds
    are rectifiable, with finite Hausdorff measure. Only
    the abstract ambient isometry and manifold laws are used. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerProductUP
  InnerNorm InnerMetric NormMetricScaleContinuity FiniteInnerChartUP FiniteInnerSubmanifoldUP
  CompactSubmanifoldRectifiable RectifiableSetUP LipschitzUP LipschitzBasic
  LipschitzRectifiableImages RectifiableElementary RectifiableFiniteHausdorffMass
  FiniteInnerChartHausdorff MeasureUP MeasureBasic MeasureAlmostUP HausdorffMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [finite_inner_compact_submanifold_rectifiable]:
    the finite-mass source and target manifolds for the
    area/coarea calculations of Federer 3.2.28,
    pp. 265–267, by the finite chart-cover argument
    and the Lipschitz invariance of 3.2.14, pp. 251–252. *)
Theorem finite_inner_compact_submanifold_rectifiable (R:realType)
    (V:lmodType R) (B:V->V->R) (hB:is_inner_product B) mu k (S K:set V):
  (1<=k)%N ->is_inner_submanifold B mu k S ->K `<=` S ->
  @compact [the topologicalType of inner_metric_space hB] K ->
  @is_m_rectifiable R (inner_metric_space hB) mu K.
Proof.
move=>hk [n [e [p [hChart hS]]]] hKS hK.
pose X:=inner_metric_space (@euclidean_inner_productP R n).
pose Y:=inner_metric_space hB.
have hPc:continuous (fun y:Y=>(p y:X)).
  apply:(@metric_fixed_lipschitz_continuous R Y X _ 1 ler01)=>x y.
  rewrite !inner_metric_distanceE mul1r -linearB.
  change (is_true (inner_norm (@euclidean_inner_productP R n) (p (x-y))<=inner_norm hB (x-y))).
  by rewrite (finite_inner_chart_inverse_norm hB hChart).
have hPK:@compact [the topologicalType of X] (p @` K):=continuous_compact (continuous_subspaceT hPc) hK.
have hSub:p @` K `<=` p @` S.
  by move=>z [x hx <-]; exists x; first exact:hKS x hx.
have hRect:=@compact_submanifold_rectifiable R n mu k (p @` S) (p @` K) hk hS hSub hPK.
have hLip:@is_metric_lipschitz R X Y (p @` K) e.
  apply:metric_lipschitz_of_bound; split; first exact:ler01.
  move=>x y _ _; rewrite !inner_metric_distanceE mul1r.
  change (is_true (inner_norm hB (e x-e y)<=inner_norm (@euclidean_inner_productP R n) (x-y))).
  rewrite -linearB.
  by rewrite (finite_inner_chart_norm hB hChart).
have hResult:=rectifiable_lipschitz_image hLip hRect.
have hImage:e @` (p @` K)=K.
  apply/seteqP; split=>x.
  - move=>[z [y hy <-] <-]; by rewrite (finite_inner_chart_right_inverse hChart).
  - move=>hx; exists (p x); last exact:finite_inner_chart_right_inverse hChart x.
    by exists x.
by rewrite hImage in hResult.
Qed.

(** Source for [finite_inner_compact_submanifold_measure_rectifiable]:
    actual finite (H^mu,mu) rectifiability of the compact
    manifolds used in Federer 3.2.28, pp. 265–267.
    The finite measure is concluded from rectifiability. *)
Theorem finite_inner_compact_submanifold_measure_rectifiable (R:realType)
    (V:lmodType R) (B:V->V->R) (hB:is_inner_product B) mu k (S K:set V):
  (1<=k)%N ->is_inner_submanifold B mu k S ->K `<=` S ->
  @compact [the topologicalType of inner_metric_space hB] K ->
  is_measure_m_rectifiable (@hausdorff_measure R (inner_metric_space hB) mu) mu K.
Proof.
move=>hk hS hKS hK.
have hRect:=@finite_inner_compact_submanifold_rectifiable R V B hB mu k S K hk hS hKS hK.
have hH:=@hausdorff_measure_is_measure R (inner_metric_space hB) mu.
split.
- split; first exact hH.
  exists K; split; first exact:rectifiable_countably_rectifiable hRect.
  by rewrite /measure_almost_included setDv (measure_empty hH).
- have [n [e [p [hChart _]]]]:=hS.
  have hLip:@is_metric_lipschitz R (inner_metric_space hB)
      (inner_metric_space (@euclidean_inner_productP R n)) K p.
    apply:metric_lipschitz_of_bound; split; first exact:ler01.
    move=>x y _ _; rewrite !inner_metric_distanceE mul1r -linearB.
    change (is_true (inner_norm (@euclidean_inner_productP R n) (p (x-y))<=inner_norm hB (x-y))).
    by rewrite (finite_inner_chart_inverse_norm hB hChart).
  have hRP:=rectifiable_lipschitz_image hLip hRect.
  have hFinite:=rectifiable_finite_hausdorff_mass hRP.
  have hEqual:=@finite_inner_chart_hausdorff_invariance R V B hB n e p hChart mu (p @` K).
  have hImage:e @` (p @` K)=K.
    apply/seteqP; split=>x.
    + move=>[z [y hy <-] <-]; by rewrite (finite_inner_chart_right_inverse hChart).
    + move=>hx; exists (p x); last exact:finite_inner_chart_right_inverse hChart x.
      by exists x.
  rewrite hImage in hEqual; by rewrite hEqual.
Qed.
