(** Federer (1969), 2.4.16, p. 90: transferring norming tests of bounded
    restrictions gn to the original f. For our include-or-omit restrictions,
    the products are exactly equal. The test is aligned with sign(f) but may
    vanish at omitted points; a separate positive mixture restores full
    sign. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionUP PartialFunctionBasic PartialScalarProduct
  MeasureUP MeasurableFunctionUP MeasureIntegralUP MeasureIntegralGraphEquivalence MeasureLpNorm
  MeasureDualTestUP DualPowerTest TotalDualPowerTest SignPreservingMixture ConjugateExponents.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [restricted_power_test_transfer]: supporting
    comparison of dual values for gn and f in Federer 2.4.16,
    p. 90, final display. For restrictions the comparison is equality. *)
Lemma restricted_power_test_transfer (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (p a : R)
    (f g : X -> real_norm_metric_space (scalar_absolute_value_norm R)) :
  (1 < p)%R -> (0 < a)%R -> is_measure_measurable_function mu (partial_function_total g) ->
  measure_lp_norm mu (fun y : R => `|y|%R) p (partial_function_total g)=a%:E ->
  (forall x, g x=0%R \/ g x=f x) ->
  exists u : X -> real_norm_metric_space (scalar_absolute_value_norm R),
    is_finite_lp_unit_test mu (finite_conjugate_exponent p) (partial_function_total u) /\
    (forall x, u x=(`|u x|*Num.sg (f x))%R) /\
    is_measure_integral mu (partial_scalar_product (partial_function_total f) (partial_function_total u)) a%:E.
Proof.
move=> hp ha hg hga hres.
pose u x := (dual_power_test p a (g x) : real_norm_metric_space (scalar_absolute_value_norm R)).
have [hu hi] := @total_dual_power_test_admissible R X mu hm p a g hp ha hg hga.
have hu0 x : g x=0%R -> u x=0%R by move=> hz; rewrite /u /dual_power_test hz sgr0 mulr0.
have hprod x : (f x*u x=g x*u x)%R.
  have [hz|he] := hres x; last by rewrite he.
  by rewrite (hu0 x hz) !mulr0.
exists u; split=> //; split.
- move=> x; have [hz|he] := hres x.
  + by rewrite (hu0 x hz) normr0 mul0r.
  + apply: sign_matching_absolute_factor; rewrite /u he; exact: dual_power_test_sign hp ha.
- apply: (@measure_integral_graph_equivalent R X mu _ _ _ _ hi)=> x z.
  rewrite !partial_scalar_product_graph; split.
  + move=> [v [w [hv [hw hvw]]]]; exists (f x),(u x); split=> //; split=> //.
    by rewrite hprod (hv : g x=v) (hw : u x=w).
  + move=> [v [w [hv [hw hvw]]]]; exists (g x),(u x); split=> //; split=> //.
    by rewrite -hprod (hv : f x=v) (hw : u x=w).
Qed.
