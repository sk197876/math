(** Federer (1969), 4.1.2, p. 347: the
    original Banach-valued integral is invariant under the
    injective measure-preserving substitution in the two
    convolution formulas. Its L1 domain and every dual
    evaluation are transported explicitly. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric VectorDaniellHypotheses PartialFunctionUP PartialFunctionBasic
  PartialFunctionPrecomposition MeasureUP MeasurePushforward PushforwardMeasurabilityTransfer
  MeasurableFunctionUP MeasurableGraphEquivalence MeasureLpMembershipUP MeasureLpNorm
  MeasureIntegralUP MeasureIntegralGraphEquivalence MeasureVectorIntegralUP SummableRealFunctionUP
  WeakDerivativeFieldVectorIntegral MeasureLoneNormIntegralGeneral TotalVectorNormIntegrability InvariantRealIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [invariant_total_vector_integral]: the exact
    substitution in Federer 4.1.2, p. 347,
    preserving the original L1 membership and integral value.
    The target remains any separable normed space. *)
Theorem invariant_total_vector_integral (R:realType) (X:choiceType) (Y:lmodType R)
    (N:Y->R) (hN:is_real_norm N) (mu:set X->\bar R) (hm:is_measure mu)
    (u:X->X) (f:X->Y) y:
  is_separable_normed_space hN ->
  injective u ->measure_pushforward u mu=mu ->
  is_measure_vector_integral mu
    (partial_function_total (fun x=>(f x:real_norm_metric_space hN))) y ->
  is_measure_vector_integral mu
    (partial_function_total (fun x=>(f (u x):real_norm_metric_space hN))) y.
Proof.
move=>hSep hInj hInvariant hI.
have hf:=hI.1.2.1.1.
have hMeasPull:=@measurable_function_pushforward_precompose R X X (real_norm_metric_space hN)
  u mu (partial_function_total (fun x=>(f x:real_norm_metric_space hN))) hInj.
rewrite hInvariant in hMeasPull.
have hMeas:is_measure_measurable_function mu
    (partial_function_total (fun x=>(f (u x):real_norm_metric_space hN))).
  apply:(measurable_function_graph_equivalent _ (hMeasPull hf))=>x z; reflexivity.
pose P:=measure_lp_norm mu N 1 (partial_function_total (fun x=>(f x:real_norm_metric_space hN))).
have hNonneg:(0<=P)%E:=@measure_lp_norm_nonnegative R X Y N hN mu 1 _ hm (lexx _) hf.
have hFinite:P \is a fin_num by rewrite (ge0_fin_numE hNonneg); exact:hI.1.2.2.1.
pose b:=fine P.
have hP:P=b%:E by rewrite /b fineK.
have hNorm:is_measure_integral mu (real_total_integrand (fun x=>N (f x))) b%:E.
  have h:=@measurable_lone_norm_integral R X Y N hN mu hm _ hf.
  rewrite -hP.
  apply:(measure_integral_graph_equivalent _ h)=>x z.
  exact:(@total_vector_norm_power_one_graph R X Y N hN f x z).
have hPull:=@invariant_real_total_integral R X mu hm u (fun x=>N (f x)) b hInj hInvariant hNorm.
split.
- exact:(@total_vector_lone_from_norm_integral R X Y N hN mu hm (fun x=>f (u x)) b hSep hMeas hPull).
- move=>alpha hAlpha.
  have hScalar:is_measure_integral mu (real_total_integrand (fun x=>alpha (f x))) (alpha y)%:E.
    apply:(measure_integral_graph_equivalent _ (hI.2 alpha hAlpha))=>x z.
    by rewrite total_functional_evaluation_graph real_total_integrand_graph.
  have hScalarPull:=@invariant_real_total_integral R X mu hm u
    (fun x=>alpha (f x)) (alpha y) hInj hInvariant hScalar.
  apply:(measure_integral_graph_equivalent _ hScalarPull)=>x z.
  by rewrite total_functional_evaluation_graph real_total_integrand_graph.
Qed.
