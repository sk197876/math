(** Federer (1969), 3.2.46, p. 281: continuity of the tensor
    bounds its speeds uniformly along a compact interval. This
    supporting integrability estimate uses only the original finite
    coordinate basis, with no selected frame field. *)
From mathcomp Require Import all_boot all_order all_algebra reals
  classical_sets topology num_normedtype pseudometric_normed_Zmodule normed_module.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates
  EuclideanInnerProduct InnerNorm InnerMetric HilbertFormCompactness
  RealNormUP EuclideanCoordinateTopology EuclideanCoordinateMetric
  RealMetricBackground ContinuousSegmentBound RiemannianTensorUP
  RiemannianTensorSpeedContinuity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [riemannian_tensor_coordinate_speed_bound]: the
    inner-product triangle inequality bounds the speed of v by its
    ordinary norm times the sum of the coordinate speeds. Supporting
    the finite curve integrals in Federer 3.2.46, p. 281; the empty
    coordinate family and the zero vector are included. *)
Lemma riemannian_tensor_coordinate_speed_bound (R : realType) n A g
    (hg : @is_continuous_riemannian_tensor R n A g) x (hx : A x) v :
  riemannian_tensor_speed g x v <=
    (\sum_i riemannian_tensor_speed g x (@coordinate_basis R n i)) *
      inner_norm (@euclidean_inner_productP R n) v.
Proof.
pose hG := riemannian_tensor_inner hg hx.
have hSum := real_seminorm_sum (inner_norm_real_norm hG).1
  (fun i : 'I_n => v i *: (@coordinate_basis R n i)).
rewrite euclidean_coordinate_expansion in hSum.
rewrite (riemannian_tensor_speed_inner_norm hg hx).
apply: le_trans hSum _.
have hTerm i : inner_norm hG (v i *: (@coordinate_basis R n i)) <=
    riemannian_tensor_speed g x (@coordinate_basis R n i) *
      inner_norm (@euclidean_inner_productP R n) v.
  rewrite inner_normZ -(@riemannian_tensor_speed_inner_norm R n A g hg x hx).
  rewrite [X in _ <= X]mulrC.
  exact (ler_wpM2r (riemannian_tensor_speed_nonnegative g x _)
    (euclidean_coordinate_norm_bound i v)).
have h : (\sum_i inner_norm hG (v i *: (@coordinate_basis R n i))) <=
    \sum_i riemannian_tensor_speed g x (@coordinate_basis R n i) *
      inner_norm (@euclidean_inner_productP R n) v.
  apply: ler_sum=> i _; exact: hTerm.
by rewrite -mulr_suml in h.
Qed.

(** Source for [riemannian_curve_uniform_speed_bound]: continuity
    and compactness supply a finite bound on the tensor-speed norm
    along the actual curve interval in Federer 3.2.46, p. 281.
    No bound on a derivative field is assumed. *)
Theorem riemannian_curve_uniform_speed_bound (R : realType) n A g
    (hg : @is_continuous_riemannian_tensor R n A g)
    (C : real_line_metric R -> inner_metric_space (@euclidean_inner_productP R n)) a b :
  continuous C -> (forall t, A (C t)) ->
  exists M : R, 0 < M /\ forall t, a <= t <= b -> forall v,
    riemannian_tensor_speed g (C t) v <=
      M * inner_norm (@euclidean_inner_productP R n) v.
Proof.
move=> hC hA.
pose S := fun t : real_line_metric R =>
  \sum_i riemannian_tensor_speed g (C t) (@coordinate_basis R n i).
have hS : continuous (fun t => (S t : real_line_metric R)).
  apply: continuous_big; first exact: add_continuous.
  move=> i _.
  have hConst : continuous (fun t : real_line_metric R =>
      (@coordinate_basis R n i : inner_metric_space (@euclidean_inner_productP R n))).
    by move=> t; exact: cvg_cst.
  exact (@riemannian_tensor_speed_continuous R n A g hg
    [the topologicalType of real_line_metric R] C (fun _=>@coordinate_basis R n i)
    hC hConst hA).
have [M [hM hBound]] := continuous_positive_segment_bound a b hS.
exists M; split=> // t ht v.
apply: le_trans (riemannian_tensor_coordinate_speed_bound hg (hA t) v) _.
have hSM : S t <= M := le_trans (ler_norm (S t)) (hBound t ht).
exact (ler_wpM2r (inner_norm_nonnegative (@euclidean_inner_productP R n) v) hSM).
Qed.
