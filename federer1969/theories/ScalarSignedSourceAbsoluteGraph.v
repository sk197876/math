(** Federer (1969), 3.2.7, p. 246: supporting
    exact absolute-value identification for the third
    counterexample. A nonnegative weight turns the
    absolute signed derivative product into the area
    source integrand without extending derivative domains. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology normedtype.
From Federer Require Import RealMetricBackground ExtendedRealOrderTopology RealCurveDerivativeUP RealCurveDerivativeIntegrands
  PartialFunctionUP PartialFunctionBasic PartialFunctionPostcomposition PartialZeroExtension PartialDensityProduct
  PartialAbsolutePartsGraph WeightedRealDerivativeIntegrand ScalarSignedSourceSplitting ScalarAbsoluteContinuousArea.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [scalar_nonnegative_weight_signed_source_absolute_graph]:
    the actual absolute source integrand needed to
    refute the second equation of 3.2.6 in
    Federer 3.2.7, p. 246. This is an
    exact partial-graph identity, with no almost-everywhere
    derivative defaults and no regularity hypothesis on f. *)
Lemma scalar_nonnegative_weight_signed_source_absolute_graph (R:realType)
    (f g:R->R) (a b:R):
  (forall y,0<=g y) -> forall x z,
  partial_function_graph (partial_extended_function_absolute_value
    (scalar_signed_substitution_source f g a b)) x z <->
  partial_function_graph (scalar_curve_area_source_integrand f `[a,b] g) x z.
Proof.
move=>hg x z.
case:(pselect ((`[a,b]:set (real_line_metric R)) x))=>hx.
- have hAbs v:`|(g (f x)*v)%:E|%E=(g (f x) * `|v|)%:E.
    by rewrite abse_EFin normrM (ger0_norm (hg (f x))).
  split.
  + move=>[w [hw hwz]].
    have hS:partial_function_graph (weighted_real_curve_derivative_integrand (g \o f) f) x w.
      exact ((partial_function_zero_extension_on _ _ _ hx).1 hw).
    have [v [hv hValue]]:=(weighted_real_derivative_integrand_graph (g \o f) f x w).1 hS.
    rewrite -hwz -hValue hAbs.
    exact (scalar_area_source_actual_value g hv hx).
  + move=>hA.
    have hProd:partial_function_graph
      (partial_density_product (partial_function_total (fun x:R=>(g (f x))%:E:extended_real_line R))
        (real_curve_absolute_derivative_integrand f)) x z.
      exact ((partial_function_zero_extension_on _ _ _ hx).1 hA).
    have [u [w [hu [hw he]]]]:=(partial_density_product_graph _ _ x z).1 hProd.
    have [v [hv hvw]]:=hw.
    have hValue:(g (f x) * `|v|)%:E=z.
      change ((g (f x))%:E=u) in hu.
      by rewrite -he -hu -hvw -EFinM.
    exists (g (f x)*v)%:E; split; last by rewrite hAbs.
    apply/partial_function_zero_extension_graph; left; split=>//.
    apply/weighted_real_derivative_integrand_graph; exists v; by split.
- split.
  + move=>[w [hw hwz]].
    have hw0:w=0%E:= (partial_function_zero_extension_off _ _ _ hx).1 hw.
    apply:(partial_function_zero_extension_off _ _ _ hx).2.
    by rewrite -hwz hw0 abse0.
  + move=>hA; have hz0:z=0%E:=(partial_function_zero_extension_off _ _ _ hx).1 hA.
    exists 0%E; split; last by rewrite hz0 abse0.
    exact ((partial_function_zero_extension_off _ _ _ hx).2 (erefl _)).
Qed.
