(** Federer (1969), 4.1.2, p. 347: replacing
    the original measurable field by an almost-equal
    total representative preserves every convolution integral.
    Both directions retain the full actual L1 domain. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionUP PartialFunctionBasic PartialFunctionSourcePostcomposition
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasureAlmostEquality
  MeasureVectorIntegralUP MeasureVectorIntegralAlmostEquality TotalVectorIntegralArithmetic
  GrassmannAbbreviations EuclideanLebesgueDimensions SmoothingConvolutionUP PartialSmoothingConvolutionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [partial_scalar_vector_weight_almost_equal]: null
    modifications preserve the original kernel integrand,
    supporting Federer 4.1.2, p. 347, by 2.3.1,
    p. 72, and 2.4.12, pp. 87–88. *)
Lemma partial_scalar_vector_weight_almost_equal (R:realType) (X:choiceType) (Y:lmodType R)
    (NY:Y->R) (hNY:is_real_norm NY) (mu:set X->\bar R) (hm:is_measure mu)
    (w:X->R) (f g:partial_function X (real_norm_metric_space hNY)):
  measure_almost_equal mu f g ->measure_almost_equal mu
    (partial_scalar_vector_weight w f) (partial_scalar_vector_weight w g).
Proof.
move=>he; apply:(@measure_almost_everywhere_mono R X mu hm _ _ _ he)=>x [y [hf hg]].
exists (w x*:y); split; exists y; by split.
Qed.

(** Source for [partial_weight_total_graph]: the weighted
    total representative has exactly its expected integral
    graph, supporting Federer 4.1.2, p. 347. *)
Lemma partial_weight_total_graph (R:realType) (X:Type) (Y:lmodType R)
    (NY:Y->R) (hNY:is_real_norm NY) (w:X->R) (F:X->Y) x z:
  partial_function_graph (partial_scalar_vector_weight w
    (partial_function_total (fun x=>(F x:real_norm_metric_space hNY)))) x z <->
  partial_function_graph (partial_function_total (fun x=>(w x*:F x:real_norm_metric_space hNY))) x z.
Proof.
split.
- move=>[y [hy he]]; change (F x=y) in hy.
  change (w x*:F x=z); by rewrite hy.
- move=>he; exists (F x); by split.
Qed.

(** Source for [partial_smoothing_convolution_extension_iff]: convolution
    of the original measurable partial field agrees
    with convolution of every almost-equal total representative,
    Federer 4.1.2, p. 347, by 2.3.2,
    p. 73. No extra full-domain hypothesis is imposed. *)
Theorem partial_smoothing_convolution_extension_iff (R:realType) n (Y:lmodType R)
    (NY:Y->R) (hNY:is_real_norm NY) (psi:R_n R n->R)
    (f:partial_function (R_n R n) (real_norm_metric_space hNY)) (F g:R_n R n->Y):
  measure_almost_equal (@euclidean_lebesgue_measure R n) f
    (partial_function_total (fun x=>(F x:real_norm_metric_space hNY))) ->
  (is_partial_smoothing_convolution psi f g <->is_smoothing_convolution hNY psi F g).
Proof.
move=>he; split=>hI x.
- have hWeight:=@partial_scalar_vector_weight_almost_equal R (R_n R n) Y NY hNY
    (@euclidean_lebesgue_measure R n) (euclidean_lebesgue_is_measure R n)
    (fun z=>psi (x-z)) _ _ he.
  have hi:=@measure_vector_integral_almost_equal R (R_n R n) Y NY hNY
    (@euclidean_lebesgue_measure R n) (euclidean_lebesgue_is_measure R n) _ _ (g x) (hI x) hWeight.
  apply:(@measure_vector_integral_graph_equivalent R (R_n R n) Y NY hNY
    (@euclidean_lebesgue_measure R n) (euclidean_lebesgue_is_measure R n) _ _ (g x) _ hi)=>z y.
  exact:partial_weight_total_graph.
- have hWeight:=@partial_scalar_vector_weight_almost_equal R (R_n R n) Y NY hNY
    (@euclidean_lebesgue_measure R n) (euclidean_lebesgue_is_measure R n)
    (fun z=>psi (x-z)) _ _ (measure_almost_equal_sym he).
  have hi:is_measure_vector_integral (@euclidean_lebesgue_measure R n)
      (partial_scalar_vector_weight (fun z=>psi (x-z))
        (partial_function_total (fun z=>(F z:real_norm_metric_space hNY)))) (g x).
    apply:(@measure_vector_integral_graph_equivalent R (R_n R n) Y NY hNY
      (@euclidean_lebesgue_measure R n) (euclidean_lebesgue_is_measure R n) _ _ (g x) _ (hI x))=>z y.
    symmetry; exact:partial_weight_total_graph.
  exact:(measure_vector_integral_almost_equal (euclidean_lebesgue_is_measure R n) hi hWeight).
Qed.
