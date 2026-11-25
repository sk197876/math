(** Federer (1969), 3.2.28, pp. 265–267:
    isometric coordinates preserve the compact source and
    target manifolds in the area and coarea applications. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerProductUP InnerNorm InnerMetric
  NormMetricScaleContinuity FiniteInnerChartUP FiniteInnerChartHausdorff EuclideanSubmanifoldUP
  CompactSubmanifoldRectifiable RectifiableSetUP HausdorffMeasure HausdorffClosedCoverAgreement
  MeasureUP BorelRegularMeasureUP TopologicalBorel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [finite_inner_chart_compact]: the compact
    Euclidean representatives used in Federer 3.2.28,
    pp. 265–267. Continuity is proved from the
    exact isometric chart laws of 1.7.1, p. 28. *)
Lemma finite_inner_chart_compact (R:realType) (V:lmodType R)
    (B:V->V->R) (hB:is_inner_product B) n
    (e:Hom (R_n R n) V) (p:Hom V (R_n R n)) (S:set V):
  is_finite_inner_chart B e p ->
  @compact [the topologicalType of inner_metric_space hB] S ->
  @compact [the topologicalType of inner_metric_space (@euclidean_inner_productP R n)] (p @` S).
Proof.
move=>hChart hS.
pose X:=inner_metric_space hB.
pose Y:=inner_metric_space (@euclidean_inner_productP R n).
have hP:continuous (fun x:X=>(p x:Y)).
  apply:(@metric_fixed_lipschitz_continuous R X Y _ 1 ler01)=>x y.
  rewrite !inner_metric_distanceE mul1r -linearB.
  change (is_true (inner_norm (@euclidean_inner_productP R n) (p (x-y))<=inner_norm hB (x-y))).
  by rewrite (finite_inner_chart_inverse_norm hB hChart).
exact:continuous_compact (continuous_subspaceT hP) hS.
Qed.

(** Source for [finite_inner_chart_compact_manifold_measure]:
    measurable finite rectifiability of the actual compact
    manifolds in Federer 3.2.28, pp. 265–267,
    in the Euclidean coordinates of 3.2.22. *)
Theorem finite_inner_chart_compact_manifold_measure (R:realType) (V:lmodType R)
    (B:V->V->R) (hB:is_inner_product B) n mu k
    (e:Hom (R_n R n) V) (p:Hom V (R_n R n)) (S:set V):
  is_finite_inner_chart B e p ->(1<=k)%N ->
  @is_euclidean_submanifold R n mu k (p @` S) ->
  @compact [the topologicalType of inner_metric_space hB] S ->
  is_measure_m_rectifiable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R n)) mu) mu (p @` S) /\
  measure_measurable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R n)) mu) (p @` S).
Proof.
move=>hChart hk hMan hS.
have hC:=@finite_inner_chart_compact R V B hB n e p S hChart hS.
split.
- exact:compact_submanifold_measure_rectifiable hk hMan (subset_refl _) hC.
- apply:(borel_regular_borel_measurable
    (@hausdorff_measure_is_measure R (inner_metric_space (@euclidean_inner_productP R n)) mu)
    (@hausdorff_measure_borel_regular R (inner_metric_space (@euclidean_inner_productP R n)) mu)).
  apply:closed_borel_set.
  exact:compact_closed (@metric_hausdorff R (inner_metric_space (@euclidean_inner_productP R n))) hC.
Qed.

(** Source for [finite_inner_chart_inverse_hausdorff]: actual
    Hausdorff mass in inverse orthonormal coordinates,
    supporting Federer 3.2.28, pp. 265–267,
    by 2.10.11, p. 176. No measurability or
    finite-mass premise is needed. *)
Lemma finite_inner_chart_inverse_hausdorff (R:realType) (V:lmodType R)
    (B:V->V->R) (hB:is_inner_product B) n
    (e:Hom (R_n R n) V) (p:Hom V (R_n R n)):
  is_finite_inner_chart B e p ->forall q S,
    @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) q (p @` S)=
      @hausdorff_measure R (inner_metric_space hB) q S.
Proof.
move=>hChart q S.
have h:=@finite_inner_chart_hausdorff_invariance R V B hB n e p hChart q (p @` S).
have hImage:e @` (p @` S)=S.
  apply/seteqP; split=>x.
  - move=>[z [y hy <-] <-]; by rewrite (finite_inner_chart_right_inverse hChart).
  - move=>hx; exists (p x); last exact:finite_inner_chart_right_inverse hChart x.
    by exists x.
rewrite hImage in h; exact:esym h.
Qed.
