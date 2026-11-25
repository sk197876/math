(** Federer (1969), 3.2.6, p. 245: Euclidean
    curve targets are Banach for the abstract norm metric
    used by 2.9.22. Transport the already proved Euclidean
    Cauchy-filter completeness through the identical distances. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
From Federer Require Import EuclideanInnerProduct InnerMetric InnerNorm HilbertFormCompactness NormMetric
  CompleteMetricUP EuclideanMetricCompleteness MetricCauchyImages.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_own_norm_complete]: supporting
    Banach hypothesis for the finite Euclidean curve in
    Federer 3.2.6, pp. 245–246. No external Euclidean
    completeness theorem or new completed carrier is introduced. *)
Lemma euclidean_own_norm_complete (R:realType) n:
  is_complete_metric_space (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n))).
Proof.
pose M:=real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n)).
pose L:=inner_metric_space (@euclidean_inner_productP R n).
move=>F PF hc.
pose f (x:M):L:=x.
have PF':ProperFilter (f @ F):=@fmap_proper_filter M L f F PF.
have hNon:forall x y:M,mdist (f x) (f y)<=mdist x y.
  move=>x y; change (is_true (inner_norm (@euclidean_inner_productP R n) (x-y)<=
    inner_norm (@euclidean_inner_productP R n) (x-y))); exact:lexx.
have hCauchy:=@distance_nonincreasing_cauchy_image R [the metricType R of M]
  [the metricType R of L] f F PF hNon hc.
have [x hx]:=@euclidean_metric_complete R n (f @ F) PF' hCauchy.
exists (x:M)=>U hU.
have [e he hSub]:=(metricType_numDomainType.nbhs_mdistP (x:M) U).1 hU.
have hNb:nbhs (x:L) [set y:L|mdist x y<e].
  apply:(metricType_numDomainType.nbhs_mdistP (x:L) _).2; exists e=>//; by move=>y hy.
have hh:=hx _ hNb.
apply:(@filterS M F (@filter_filter M F PF) _ _ _ hh)=>y hy.
apply:hSub; exact hy.
Qed.
