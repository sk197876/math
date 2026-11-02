(** Federer (1969), 2.5.10, pp. 100–101: a bounded measurable density acts
    on L1 even without countably measurable support. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasurableFunctionUP
  FunctionLatticeSeminormUP MeasureIntegralUP SummableRealFunctionUP TotalScalarLpUP
  TotalScalarLpFiniteSeminorm TotalScalarPairing TotalScalarPairingValue.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [bounded_measurable_pairing_linear_bound]: supporting
    functional represented by the glued density in Federer 2.5.10, pp.
    100–101 Summability of each product and its bound are proved explicitly. *)
Theorem bounded_measurable_pairing_linear_bound (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (k : X -> R) (M : R) :
  (0 <= M)%R -> is_measure_measurable_function mu (total_scalar_function k) ->
  (forall x, (`|k x| <= M)%R) ->
  is_linear_functional_on_functions (total_scalar_lp mu 1) (fun f => total_scalar_pairing mu f k) /\
    forall f, total_scalar_lp mu 1 f ->
      is_measure_integral mu (real_total_integrand (fun x => (f x * k x)%R)) (total_scalar_pairing mu f k)%:E /\
      (`|total_scalar_pairing mu f k| <= M * finite_total_scalar_lp_norm mu 1 f)%R.
Proof.
move=> hM hk hb.
have ha : measure_almost_everywhere mu [set x | (`|k x| <= M)%R].
  apply: (@measure_almost_everywhere_mono R X mu hm setT _ _ (measure_almost_everywhere_true hm))=> x _.
  exact: hb.
have hp f (hf : total_scalar_lp mu 1 f) := @total_scalar_pairing_bounded_factor R X mu hm f k M hf hk hM ha.
have hs f : total_scalar_lp mu 1 f -> summable_real_functions mu (fun x => (f x * k x)%R).
  move=> hf; have [c [hi hc]] := hp f hf; by exists c.
split.
- split.
  + move=> f g hf hg; exact: (@total_scalar_pairing_add_left R X mu hm f g k (hs f hf) (hs g hg)).
  + move=> c f hf; exact: (@total_scalar_pairing_scale_left R X mu hm f k c (hs f hf)).
- move=> f hf; have [c [hi hc]] := hp f hf.
  have he := total_scalar_pairing_value_of_integral hi; rewrite he; by split.
Qed.
