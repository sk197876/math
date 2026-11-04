(** Federer (1969), 3.2.46, p. 281: the actual speed determined
    by the continuous tensor is a continuous expression in a point
    and a vector. This supporting fact supplies measurability of
    the genuine derivative-speed integral. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp
  classical_sets topology num_normedtype pseudometric_normed_Zmodule normed_module.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates
  EuclideanInnerProduct InnerProductUP InnerProductLaws InnerNorm InnerMetric
  HilbertFormCompactness EuclideanCoordinateTopology BilinearFiniteCoordinates
  RealNormUP NormMetric NormClassZeroTopology InnerOwnNormTopology HomeomorphismUP
  ScalarNormExtendedEmbedding RealMetricBackground
  SignedSquareRootUP SignedSquareRootSealed SignedSquareRootContinuity
  RiemannianTensorUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [riemannian_coefficient_along_continuous_map]:
    each actual coefficient of g is continuous along a continuous
    map into A, supporting the integral in Federer 3.2.46, p. 281.
    No extension of g beyond its original domain is required. *)
Lemma riemannian_coefficient_along_continuous_map (R : realType) n A g
    (hg : @is_continuous_riemannian_tensor R n A g)
    (X : topologicalType)
    (p : X -> inner_metric_space (@euclidean_inner_productP R n)) u v :
  continuous p -> (forall x, A (p x)) ->
  continuous (fun x => (g (p x) u v : real_line_metric R)).
Proof.
move=> hp hA x.
have hNorm := homeomorphism_continuous
  (inner_own_norm_homeomorphism (@euclidean_inner_productP R n)).
have hPair := @norm_class_zero_continuous_at R (R_n R n) R^o
  (inner_norm (@euclidean_inner_productP R n)) (fun t : R^o=>`|t|)
  (inner_norm_real_norm (@euclidean_inner_productP R n))
  (scalar_absolute_value_norm R) A (fun a=>g a u v) (p x)
  (riemannian_tensor_pair_continuous hg u v) (hA x).
have hpN : (fun z : X => (p z : real_norm_metric_space
    (inner_norm_real_norm (@euclidean_inner_productP R n)))) @ x -->
    (p x : real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n))).
  exact: continuous_comp (hp x) (hNorm (p x)).
have hScalar : (fun z : X => (g (p z) u v : real_norm_metric_space
    (scalar_absolute_value_norm R))) @ x -->
    (g (p x) u v : real_norm_metric_space (scalar_absolute_value_norm R)).
  exact: continuous_comp hpN hPair.
exact: continuous_comp hScalar (@ScalarNormExtendedEmbedding.scalar_norm_real_identity_continuous R (g (p x) u v)).
Qed.

(** Source for [riemannian_tensor_diagonal_continuous]: finite
    coordinate expansion of the bilinear expression g(p(x))(v(x),v(x)),
    supporting Federer 3.2.46, p. 281. The coordinates are the existing
    Euclidean coordinates and no frame field is chosen. *)
Lemma riemannian_tensor_diagonal_continuous (R : realType) n A g
    (hg : @is_continuous_riemannian_tensor R n A g)
    (X : topologicalType)
    (p v : X -> inner_metric_space (@euclidean_inner_productP R n)) :
  continuous p -> continuous v -> (forall x, A (p x)) ->
  continuous (fun x => (g (p x) (v x) (v x) : real_line_metric R)).
Proof.
move=> hp hv hA.
have hExpansion x : g (p x) (v x) (v x) =
    \sum_i \sum_j (v x i * v x j) *
      g (p x) (@coordinate_basis R n i) (@coordinate_basis R n j).
  have h := @bilinear_finite_expansion R (R_n R n) (g (p x))
    (inner_bilinear (riemannian_tensor_inner hg (hA x)))
    [the finType of 'I_n] [the finType of 'I_n]
    (@coordinate_basis R n) (@coordinate_basis R n) (v x) (v x).
  by rewrite !euclidean_coordinate_expansion in h.
have he : (fun x => (g (p x) (v x) (v x) : real_line_metric R)) =
    (fun x => (\sum_i \sum_j (v x i * v x j) *
      g (p x) (@coordinate_basis R n i) (@coordinate_basis R n j)
      : real_line_metric R)).
  exact: funext hExpansion.
rewrite he; apply: continuous_big; first exact: add_continuous.
move=> i _; apply: continuous_big; first exact: add_continuous.
move=> j _ x; apply: (@continuousM R X).
- apply: (@continuousM R X).
  + exact: continuous_comp (hv x) (@euclidean_coordinate_continuous R n i (v x)).
  + exact: continuous_comp (hv x) (@euclidean_coordinate_continuous R n j (v x)).
- exact: riemannian_coefficient_along_continuous_map hp hA x.
Qed.

(** Source for [riemannian_tensor_speed_continuous]: the actual
    square-root speed is continuous, supporting the defining integral
    in Federer 3.2.46, p. 281. Zero vectors and dimension zero are
    retained; the root's continuity at zero comes from the proved
    scalar square-root laws, not a differentiability premise. *)
Theorem riemannian_tensor_speed_continuous (R : realType) n A g
    (hg : @is_continuous_riemannian_tensor R n A g)
    (X : topologicalType)
    (p v : X -> inner_metric_space (@euclidean_inner_productP R n)) :
  continuous p -> continuous v -> (forall x, A (p x)) ->
  continuous (fun x => (riemannian_tensor_speed g (p x) (v x) : real_line_metric R)).
Proof.
move=> hp hv hA.
have hDiagonal := riemannian_tensor_diagonal_continuous hg hp hv hA.
have he : (fun x => (riemannian_tensor_speed g (p x) (v x) : real_line_metric R)) =
    (fun x => SignedSquareRoot.value (g (p x) (v x) (v x))).
  apply: funext=> x; rewrite /riemannian_tensor_speed.
  exact: esym (signed_square_root_nonnegative (SignedSquareRoot.laws R)
    (inner_nonnegative (riemannian_tensor_inner hg (hA x)) (v x))).
rewrite he; move=> x.
exact: continuous_comp (hDiagonal x) (@signed_root_continuous R _).
Qed.
