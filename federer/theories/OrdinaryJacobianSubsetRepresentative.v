(** Federer (1969), 3.2.22, pp. 259–260:
    ordinary coordinate Jacobian representatives preserve
    their actual subset integrals. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric NormDifferentialUP
  LipschitzUP Rademacher EuclideanLebesgueDimensions EuclideanLinearJacobian Jacobian JacobianUP
  PartialFunctionUP PartialFunctionBasic PartialFunctionPostcomposition PartialZeroExtension
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasureAlmostEquality MeasureIntegralUP MeasureSubsetIntegral
  MeasureIntegralAlmostEquality RealMetricBackground ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [ordinary_jacobian_subset_representative]:
    the ordinary J_mu phi_ij integral in Federer
    3.2.22, p. 260. Exact agreement with
    actual differential values and Rademacher justify
    replacing the partial ordinary Jacobian by its
    total representative under any subset cutoff.
    No values are added to the public partial graph. *)
Theorem ordinary_jacobian_subset_representative (R:realType) m n q
    (f:inner_metric_space (@euclidean_inner_productP R m)->
      inner_metric_space (@euclidean_inner_productP R n)) (A:set (R_n R m)) (J:R_n R m->R):
  is_metric_lipschitz setT f ->
  (forall x D,has_norm_differential (inner_norm (@euclidean_inner_productP R m))
    (inner_norm (@euclidean_inner_productP R n)) setT f x D ->J x=euclidean_linear_jacobian q D) ->
  forall a,is_measure_subset_integral (@euclidean_lebesgue_measure R m) A
    (partial_function_postcompose (euclidean_jacobian q setT f)
      (fun j=>(j%:E:extended_real_line R))) a <->
    is_measure_subset_integral (@euclidean_lebesgue_measure R m) A
      (partial_function_total (fun x=>((J x)%:E:extended_real_line R))) a.
Proof.
move=>hF hJ a.
pose rho:=@euclidean_lebesgue_measure R m.
have hr:=euclidean_lebesgue_is_measure R m.
have hAE:measure_almost_equal rho
    (partial_function_zero_extension (0:extended_real_line R) A
      (partial_function_postcompose (euclidean_jacobian q setT f) (fun j=>(j%:E:extended_real_line R))))
    (partial_function_zero_extension (0:extended_real_line R) A
      (partial_function_total (fun x=>((J x)%:E:extended_real_line R)))).
  apply:(measure_almost_everywhere_mono hr _ (federer_3_1_6 hF))=>x [D hD].
  have [hx|hx]:=pselect (A x).
  - exists (J x)%:E; split; apply:(partial_function_zero_extension_on _ _ _ hx).2.
    + exists (J x); split; last reflexivity.
      apply:(euclidean_jacobian_graph q setT f x (J x)).2.
      exists D; split; first exact hD; exact:esym (hJ x D hD).
    + reflexivity.
  - exists 0; split; apply:(partial_function_zero_extension_off _ _ _ hx).2; reflexivity.
split=>hI.
- exact:(measure_integral_almost_equal hr hI hAE).
- exact:(measure_integral_almost_equal hr hI (measure_almost_equal_sym hAE)).
Qed.
