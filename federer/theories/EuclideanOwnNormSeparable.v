(** Federer (1969), 2.7.16, pp. 134–135: the ordinary
    finite Euclidean target is separable in its own norm metric.
    This supports only the original target premise of 4.1.2,
    p. 347; it makes no assertion about an operator space. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals topology.
From Federer Require Import RealNormUP NormMetric VectorDaniellHypotheses
  GrassmannAbbreviations EuclideanInnerProduct InnerNorm HilbertFormCompactness
  EuclideanNormCountableBase CountableBaseDenseSet.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [euclidean_own_norm_separable]: the separability
    of finite Euclidean spaces in Federer 2.7.16, pp. 134–135,
    including the one-point source in dimension zero. *)
Theorem euclidean_own_norm_separable (R:realType) n:
  is_separable_normed_space (inner_norm_real_norm (@euclidean_inner_productP R n)).
Proof.
have[B hB]:=@euclidean_norm_countable_open_base R n.
rewrite /is_separable_normed_space.
exact:(@countable_open_base_dense_set
  [the topologicalType of real_norm_metric_space
    (inner_norm_real_norm (@euclidean_inner_productP R n))]
  (0:real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n))) B hB).
Qed.
