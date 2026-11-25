(** Federer (1969), 3.2.13, p. 250: the
    defining Gamma integrand is measurable after zero completion
    off the positive ray. No continuity at zero is assumed. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal
  topology num_normedtype pseudometric_normed_Zmodule normed_module.
From Federer Require Import RealMetricBackground ExtendedRealOrderTopology EulerGammaUP
  RealPowerDifferential RealExponentialDifferential ScalarDifferentialContinuity ScalarOpenZeroBorel
  RealExponentialSealed PartialFunctionUP PartialFunctionBasic PartialFunctionPreimages
  MeasurableFunctionUP MeasureAlmostBasic BorelRegularMeasureUP BorelFunctionUP
  LebesgueScalarMeasure MeasurableRealEmbedding SummableRealFunctionUP MeasurableGraphEquivalence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports numFieldNormedType.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Close Scope ereal_scope.

(** Source for [euler_gamma_integrand_continuous_at]:
    continuity on the positive domain of Gamma's defining
    integral, Federer 3.2.13, p. 250, from
    the actual internal real-power and exponential differentials. *)
Lemma euler_gamma_integrand_continuous_at (R:realType) (s a:R):
  (0<a)%R ->(fun x:real_line_metric R=>(euler_gamma_integrand s x:real_line_metric R))
    @ a -->(euler_gamma_integrand s a:real_line_metric R).
Proof.
move=>ha.
have hP:=scalar_differential_continuous_at (real_power_differential (s-1) ha).
have hE:=scalar_differential_continuous_at (@real_exponential_differential R (-a)).
have hNeg:(fun x:real_line_metric R=>((-x)%R:real_line_metric R)) @ a -->((-a)%R:real_line_metric R).
  change ((fun x:R^o=>(-x)%R) @ (a:R^o) -->((-a)%R:R^o)).
  exact:cvgN cvg_id.
have hComp:(fun x:real_line_metric R=>(RealExponential.exponential (-x):real_line_metric R))
    @ a -->(RealExponential.exponential (-a):real_line_metric R).
  move=>U hU; exact (hNeg _ (hE U hU)).
exact:cvgM hComp hP.
Qed.

(** Source for [gamma_positive_completion]: prescribed
    zero completion of the defining positive-ray integrand,
    Federer 3.2.13, p. 250. It is
    auxiliary to the existence proof, not Gamma itself. *)
Definition gamma_positive_completion (R:realType) (s x:R):R:=
  if (0<x)%R then euler_gamma_integrand s x else 0%R.

(** Source for [gamma_positive_completion_measurable]:
    measurability required by the defining Gamma integral,
    Federer 3.2.13, p. 250, including negative
    powers when 0<s<1 and without a boundary limit. *)
Lemma gamma_positive_completion_measurable (R:realType) (s:R):
  is_measure_measurable_function (@lebesgue_scalar_measure R)
    (real_total_integrand (gamma_positive_completion s)).
Proof.
pose M:=real_line_metric R.
pose mu:=@lebesgue_scalar_measure R.
have hB:=@scalar_open_zero_borel R [set x:M|(0<x)%R] (euler_gamma_integrand s)
  (@open_gt R 0) (fun a ha=>@euler_gamma_integrand_continuous_at R s a ha).
have hBool (x:R):asbool ((0<x)%R)=(0<x)%R by apply/idP/idP; [move/asboolP|move=>h; apply/asboolP].
have hTotal:is_measure_measurable_function mu
    (partial_function_total (fun x:M=>(gamma_positive_completion s x:M))).
  constructor.
  - rewrite partial_function_total_domain; exact:measure_almost_everywhere_true (lebesgue_scalar_is_measure R).
  - move=>U hU; rewrite partial_function_total_preimage.
    have hPre:=hB U hU.
    have hEq:(fun x:M=>((if asbool ((0<x)%R) then euler_gamma_integrand s x else 0%R):M))=
        (fun x:M=>(gamma_positive_completion s x:M)).
      apply:funext=>x; by rewrite hBool.
    rewrite hEq in hPre.
    exact:(borel_regular_borel_measurable (lebesgue_scalar_is_measure R)
      (lebesgue_scalar_borel_regular R) hPre).
have hI:=measurable_total_real_embedding (lebesgue_scalar_is_measure R) hTotal.
apply:measurable_function_graph_equivalent _ hI=>x z.
by rewrite real_total_integrand_graph.
Qed.
