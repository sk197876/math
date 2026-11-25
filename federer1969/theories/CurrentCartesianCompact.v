(** Federer (1969), 4.1.8, p. 360: separated tests have compact
    product support. Reuse the compact Cartesian product from 3.2.23,
    p. 260, through the proved identity between the original inner
    and norm topologies. No replacement product topology is introduced. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric InnerNorm InnerMetric HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct EuclideanCartesianMap
  EuclideanCartesianBorel EuclideanDistributionMeasureContext.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [current_cartesian_compact]: compact support of the
    separated tests in the characterising condition of Federer 4.1.8,
    p. 360. This supporting adapter reuses the original compact
    rectangle theorem and includes empty factors and dimensions. *)
Theorem current_cartesian_compact (R:realType) m n
    (A:set (R_n R m)) (B:set (R_n R n)):
  @compact (real_norm_metric_space
    (inner_norm_real_norm (@euclidean_inner_productP R m))) A->
  @compact (real_norm_metric_space
    (inner_norm_real_norm (@euclidean_inner_productP R n))) B->
  @compact (real_norm_metric_space
    (inner_norm_real_norm (@euclidean_inner_productP R (m+n))))
    (euclidean_cartesian_set A B).
Proof.
move=>hA hB.
have hAI:=continuous_compact
  (continuous_subspaceT (@euclidean_distribution_norm_to_inner R m)) hA.
change (@compact (inner_metric_space (@euclidean_inner_productP R m))
  ((fun x:R_n R m=>x) @` A)) in hAI.
rewrite image_id in hAI.
have hBI:=continuous_compact
  (continuous_subspaceT (@euclidean_distribution_norm_to_inner R n)) hB.
change (@compact (inner_metric_space (@euclidean_inner_productP R n))
  ((fun x:R_n R n=>x) @` B)) in hBI.
rewrite image_id in hBI.
have hProduct:=@euclidean_cartesian_compact R m n A B hAI hBI.
have hNorm:=continuous_compact
  (continuous_subspaceT (@euclidean_distribution_inner_to_norm R (m+n))) hProduct.
change (@compact (real_norm_metric_space
    (inner_norm_real_norm (@euclidean_inner_productP R (m+n))))
  ((fun x:R_n R (m+n)=>x) @` (euclidean_cartesian_set A B))) in hNorm.
by rewrite image_id in hNorm.
Qed.
