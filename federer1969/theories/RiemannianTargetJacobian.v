(** Federer (1969), 3.2.46, p. 282: target-metric
    area Jacobians after cancelling the source volume density.
    The source differential is the actual coordinate differential,
    not a supplied field. These supporting interfaces preserve
    its exact partial domain in every exterior degree. *)
From mathcomp Require Import all_boot all_order all_algebra reals
  classical_sets constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerNorm
  InnerMetric HilbertFormCompactness RiemannianTensorUP RiemannianLinearJacobian
  PartialFunctionUP PartialFunctionSourcePostcomposition NormDifferentialUP NormDifferential
  MeasureUP MeasureAlmostUP MeasureAlmostBasic PartialExtendedOrderLoci
  MeasureStepIntegralIdentification ExtendedRealOrderTopology RealMetricBackground
  EuclideanLebesgueDimensions LipschitzUP Rademacher.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section TargetJacobian.
Context (R : realType) m n A h (hh : @is_continuous_riemannian_tensor R n A h)
  (f : R_n R m -> R_n R n) (hf : forall x, A (f x)).
Local Notation NX := (inner_norm (@euclidean_inner_productP R m)).
Local Notation NY := (inner_norm (@euclidean_inner_productP R n)).

(** Source for [has_target_riemannian_jacobian]: actual
    exterior norm of Df(a) with Euclidean source and
    target inner product h(f(a)), supporting 3.2.46,
    p. 282. It states no area or coarea identity. *)
Definition has_target_riemannian_jacobian k a j :=
  exists D : Hom (R_n R m) (R_n R n),
    has_norm_differential NX NY setT f a D /\
    riemannian_linear_jacobian (@euclidean_inner_productP R m)
      (riemannian_tensor_inner hh (hf a)) k D = j.

(** Source for [target_riemannian_jacobian]: coordinate
    Jacobian with the actual varying target metric in
    3.2.46, p. 282, obtained from the existing sealed
    differential and exterior norm, retaining the exact domain. *)
Definition target_riemannian_jacobian k : partial_function (R_n R m) R :=
  partial_function_source_postcompose
    (norm_differential (inner_norm_real_norm (@euclidean_inner_productP R m))
      (inner_norm_real_norm (@euclidean_inner_productP R n)) setT f)
    (fun a D=>riemannian_linear_jacobian (@euclidean_inner_productP R m)
      (riemannian_tensor_inner hh (hf a)) k D).

(** Source for [target_riemannian_jacobian_graph]: the
    exact independent graph law for the coordinate Jacobian
    used in 3.2.46, p. 282. *)
Lemma target_riemannian_jacobian_graph k a j :
  partial_function_graph (target_riemannian_jacobian k) a j <->
    has_target_riemannian_jacobian k a j.
Proof.
split.
- move=> [D [hD hJ]]; exists D; split; last exact hJ.
  exact: (norm_differential_graph _ _ setT f a D).1 hD.
- move=> [D [hD hJ]]; exists D; split; last exact hJ.
  exact: (norm_differential_graph _ _ setT f a D).2 hD.
Qed.

(** Source for [extended_target_riemannian_jacobian]: the
    same finite real Jacobian embedded as an extended-real
    integrand, supporting 3.2.46, p. 282. Neither a
    default value nor a different differentiability domain is used. *)
Definition extended_target_riemannian_jacobian k :=
  partial_real_function_embed (target_riemannian_jacobian k).

(** Source for [target_riemannian_jacobian_nonnegative]:
    nonnegativity of every actual exterior-norm value, supporting
    the area/coarea extensions of 3.2.46, p. 282. *)
Lemma target_riemannian_jacobian_nonnegative k a j :
  partial_function_graph (target_riemannian_jacobian k) a j -> 0<=j.
Proof.
move=> /(target_riemannian_jacobian_graph k a j) [D [_ <-]].
exact: riemannian_linear_jacobian_nonnegative.
Qed.

(** Source for [target_riemannian_jacobian_nonnegative_almost]:
    the original Rademacher theorem gives a conull domain
    for the actual target-metric integrand, supporting 3.2.46,
    p. 282. No extra differentiability premise or field
    is supplied. All natural source dimensions are retained. *)
Lemma target_riemannian_jacobian_nonnegative_almost k :
  @is_metric_lipschitz R
    [the metricType R of inner_metric_space (@euclidean_inner_productP R m)]
    [the metricType R of inner_metric_space (@euclidean_inner_productP R n)] setT f ->
  measure_almost_everywhere (@euclidean_lebesgue_measure R m)
    (partial_extended_nonnegative_locus (extended_target_riemannian_jacobian k)).
Proof.
move=> hLip.
apply: (@measure_almost_everywhere_mono R _ _ (euclidean_lebesgue_is_measure R m)
  _ _ _ (federer_3_1_6 hLip))=> a [D hD].
pose j := riemannian_linear_jacobian (@euclidean_inner_productP R m)
  (riemannian_tensor_inner hh (hf a)) k D.
have hJ : partial_function_graph (target_riemannian_jacobian k) a j.
  apply: (target_riemannian_jacobian_graph k a j).2; exists D; by split.
exists j%:E; split.
- exists j; by split.
- rewrite lee_fin; exact: riemannian_linear_jacobian_nonnegative.
Qed.
End TargetJacobian.
