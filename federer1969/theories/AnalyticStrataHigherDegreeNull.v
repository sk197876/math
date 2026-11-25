(** Federer (1969), 3.4.8(13), p. 335:
    the complete finite stratification gives a representative
    with zero measure in every degree greater than
    its original dimension. Actual analytic charts connect
    the strata to the already proved rectifiability theorem. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality
  reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric GrassmannAbbreviations EuclideanInnerProduct InnerNorm
  InnerMetric HilbertFormCompactness FunctionalAnalyticSubmanifoldUP FunctionalAnalyticManifold
  AnalyticSubmanifoldUP SubmanifoldCountablyRectifiable CountablyRectifiableHigherDegreeNull
  HausdorffMeasure MeasureUP MeasureAlmostBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [analytic_strata_higher_degree_null]: the
    H^(m+1)-null representative in 3.4.8(13), p. 335.
    This supporting result works at every q>m,
    without a measurability assumption on the original union. *)
Theorem analytic_strata_higher_degree_null (R:realType) n m q mu
    (V S:'I_mu->set (R_n R n)):
  (m<q)%N ->
  (forall i,exists d,(d<=m)%N /\@is_functional_analytic_submanifold R n d (V i) (S i)) ->
  @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) q (\bigcup_i S i)=0%E.
Proof.
move=>hMQ hStrata.
apply:(@measure_null_countable_union R (inner_metric_space (@euclidean_inner_productP R n))
  [the choiceType of 'I_mu]
  (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) q)
  (@hausdorff_measure_is_measure R (inner_metric_space (@euclidean_inner_productP R n)) q)
  setT S (countableP setT))=>i hi.
have [d [hDM hMan]]:=hStrata i.
apply:(@countably_rectifiable_higher_degree_null R n d q (S i) (leq_ltn_trans hDM hMQ)).
apply:(@submanifold_countably_rectifiable R n d 1%N (S i) (leqnn 1)).
exact:analytic_submanifold_class_one (functional_analytic_submanifold_analytic hMan).
Qed.
