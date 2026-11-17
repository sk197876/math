(** Federer (1969), 3.4.12, pp. 338–339:
    finite Hermitian spaces are Banach for their original
    real norm metric. Reuse actual finite inner-product
    charts and the proved Euclidean Cauchy completeness. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals topology.
From Federer Require Import Hom RealNormUP InnerProductUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct LinearBasis FiniteInnerChartUP FiniteInnerChart
  NormMetric CompleteMetricUP EuclideanOwnNormCompleteness CompleteMetricIsometricBijection.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [finite_inner_norm_complete]: the original
    finite inner-product norm is complete, supporting
    the complex Banach-space hypothesis of 3.4.12,
    pp. 338–339. The zero-dimensional case is retained. *)
Theorem finite_inner_norm_complete (R:realType) (X:lmodType R)
    B (hB:@is_inner_product R X B) n (b:'I_n->X):
  is_basis b ->is_complete_metric_space (real_norm_metric_space (inner_norm_real_norm hB)).
Proof.
move=>hb;have [e [p hChart]]:=finite_inner_chart_exists hB hb.
apply:(@complete_metric_isometric_bijection R
  (real_norm_metric_space (inner_norm_real_norm hB))
  (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n))) p e).
- exact:finite_inner_chart_right_inverse hChart.
- exact:finite_inner_chart_left_inverse hChart.
- move=>x y;change (inner_norm (@euclidean_inner_productP R n) (p x-p y)=inner_norm hB (x-y)).
  have hLinear:p (x-y)=p x-p y by exact:linearB.
  by rewrite -hLinear (finite_inner_chart_inverse_norm hB hChart).
- exact:euclidean_own_norm_complete.
Qed.
