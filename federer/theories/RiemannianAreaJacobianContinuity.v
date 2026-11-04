(** Federer (1969), 3.2.46, p. 282: measurability
    of the genuine varying-metric area integrand follows
    from its continuous dependence on the point and its
    actual differential. The Gram polynomial uses the
    original tensor coefficients and no auxiliary frame. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp fingroup perm
  classical_sets topology num_normedtype pseudometric_normed_Zmodule normed_module.
From Federer Require Import Hom Bilinear GrassmannAbbreviations FiniteCoordinates
  EuclideanInnerProduct InnerNorm InnerMetric EuclideanHomOperator NormMetric
  ContinuousOperatorUP NormOperatorNormUP NormMetricScaleContinuity RealMetricBackground
  RiemannianTensorUP RiemannianLinearJacobian RiemannianAreaGramPolynomial
  RiemannianTensorVariablePairing InversionCount SignedSquareRootUP SignedSquareRootSealed
  SignedSquareRootContinuity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.
Local Open Scope ring_scope.

(** Source for [euclidean_operator_fixed_evaluation_continuous]:
    evaluation of an actual linear map at a fixed vector
    is continuous in its operator norm, supporting 3.2.46,
    p. 282, by 1.7.6, p. 33. The zero vector
    and zero-dimensional spaces are retained. *)
Lemma euclidean_operator_fixed_evaluation_continuous (R : realType) m n (v : R_n R m) :
  continuous (fun D : real_norm_metric_space (@euclidean_operator_norm_is_norm R m n)=>
    (D v : inner_metric_space (@euclidean_inner_productP R n))).
Proof.
pose H := [the metricType R of real_norm_metric_space (@euclidean_operator_norm_is_norm R m n)].
pose E := [the metricType R of inner_metric_space (@euclidean_inner_productP R n)].
apply: (@metric_fixed_lipschitz_continuous R H E (fun D=>D v)
  (inner_norm (@euclidean_inner_productP R m) v) (inner_norm_nonnegative _ _)).
move=> D F.
change (is_true (inner_norm (@euclidean_inner_productP R n) (D v-F v)<=
  inner_norm (@euclidean_inner_productP R m) v*euclidean_operator_norm (D-F))).
have hBound := norm_operator_bound (continuous_operator_norm_laws (@euclidean_hom_operator_space R m n) (D-F)) v.
change (is_true (inner_norm (@euclidean_inner_productP R n) ((D-F) v)<=
  euclidean_operator_norm (D-F)*inner_norm (@euclidean_inner_productP R m) v)) in hBound.
have hEval : (D-F) v=D v-F v := linB (hom_eval_linear v) D F.
by rewrite hEval mulrC in hBound.
Qed.

(** Source for [riemannian_area_jacobian_continuous_parameter]:
    continuous coordinate parameters and actual linear maps
    give a continuous Euclidean-source Riemannian area Jacobian,
    supporting 3.2.46, p. 282. Singular maps are included;
    the square-root Gram polynomial is nonnegative by the
    proved actual exterior norm identity, not by assumption. *)
Theorem riemannian_area_jacobian_continuous_parameter (R : realType) m n A g
    (hg : @is_continuous_riemannian_tensor R n A g) (X : topologicalType)
    (p : X -> inner_metric_space (@euclidean_inner_productP R n))
    (hA : forall x, A (p x))
    (D : X -> real_norm_metric_space (@euclidean_operator_norm_is_norm R m n)) :
  continuous p -> continuous D ->
  continuous (fun x=>(riemannian_linear_jacobian (@euclidean_inner_productP R m)
    (riemannian_tensor_inner hg (hA x)) m (D x) : real_line_metric R)).
Proof.
move=> hp hD.
pose Q x := \sum_(sigma : 'S_m) FedererPermutation.index R sigma *
  \prod_(i < m) g (p x) (D x (@coordinate_basis R m (sigma i))) (D x (@coordinate_basis R m i)).
have hVector v : continuous (fun x=>(D x v : inner_metric_space (@euclidean_inner_productP R n))).
  move=> x; exact (continuous_comp (hD x)
    (@euclidean_operator_fixed_evaluation_continuous R m n v (D x))).
have hQ : continuous (fun x=>(Q x : real_line_metric R)).
  apply: continuous_big; first exact: add_continuous.
  move=> sigma _ x; apply: (@continuousM R X); first exact: cst_continuous.
  apply: continuous_big; first exact: mul_continuous.
  move=> i _; exact (@riemannian_variable_pairing_continuous R n A g hg X p
    (fun x=>D x (@coordinate_basis R m (sigma i)))
    (fun x=>D x (@coordinate_basis R m i)) hA hp (hVector _) (hVector _)).
have hNonnegative x : 0<=Q x.
  rewrite /Q -(@riemannian_area_gram_polynomial R m n (g (p x))
    (riemannian_tensor_inner hg (hA x)) (D x)); exact: sqr_ge0.
have hFormula : (fun x=>(riemannian_linear_jacobian (@euclidean_inner_productP R m)
    (riemannian_tensor_inner hg (hA x)) m (D x) : real_line_metric R)) =
    (fun x=>SignedSquareRoot.value (Q x)).
  apply: funext=> x.
  rewrite (@riemannian_area_jacobian_gram_root R m n (g (p x))
    (riemannian_tensor_inner hg (hA x)) (D x)).
  exact: esym (signed_square_root_nonnegative (SignedSquareRoot.laws R) (hNonnegative x)).
rewrite hFormula=> x; exact (continuous_comp (hQ x) (@signed_root_continuous R (Q x))).
Qed.
