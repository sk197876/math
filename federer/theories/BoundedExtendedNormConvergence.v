(** Supporting finite-exponent approximation for Federer (1969), 2.10.5(2),
    p. 173, the open/closed convex construction comparison. At a fixed
    finite exponent, uniformly bounded nonnegative measurable inputs on a
    probability space have convergent norms under pointwise convergence.
    Apply 2.4.9, p. 85, to the actual positive powers, then take the root
    from 2.4.12, p. 86. This statement deliberately excludes exponent
    infinity: pointwise convergence alone does not imply convergence in the
    essential-supremum norm. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology ExtendedRealOrderLimit
  ExtendedPositivePower ExtendedPositivePowerLimit RealPower PartialFunctionUP PartialFunctionBasic
  PartialFunctionPostcomposition PartialExtendedOrderLoci PartialAbsolutePartsGraph PartialDominatedConvergence
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasurableFunctionUP MeasureIntegralUP
  MeasureIntegralBounds MeasureIntegralUniqueness MeasureNonnegativeLowerIntegral
  MeasureBoundedConvergence ProbabilityConstantIntegral MeasurableNonnegativeExtendedPower
  NonnegativeExtendedExponentNormUP NonnegativeExtendedExponentNorm.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [bounded_nonnegative_extended_norm_convergence]:
    supporting finite-exponent norm approximation
    for Federer 2.10.5(2), p. 173. Dominate
    the powered inputs by the integrable constant
    M^p and use the sealed integral-root formula.
    The finite values are proved by domination,
    rather than silently replacing infinite inputs. *)
Theorem bounded_nonnegative_extended_norm_convergence (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : nat -> X -> extended_real_line R) (g : X -> extended_real_line R) (M p : R) :
  mu setT = 1 -> (1<=p)%R ->
  (forall k x, 0<=f k x /\ f k x<=M%:E) ->
  (forall x, 0<=g x /\ g x<=M%:E) ->
  (forall k, is_measure_measurable_function mu (partial_function_total (f k))) ->
  is_measure_measurable_function mu (partial_function_total g) ->
  (forall x, extended_order_limit (fun k => f k x) (g x)) ->
  extended_order_limit (fun k => nonnegative_extended_exponent_norm mu (f k) p%:E)
    (nonnegative_extended_exponent_norm mu g p%:E).
Proof.
move=> hprob hp hb hgb hf hg hl.
have hp0 : (0<p)%R := lt_le_trans ltr01 hp.
pose F k : partial_function X (extended_real_line R) :=
  partial_function_total (fun x => extended_positive_power (f k x) p).
pose G : partial_function X (extended_real_line R) :=
  partial_function_total (fun x => extended_positive_power (g x) p).
pose C := real_power M p.
pose H := partial_function_total (fun _ : X => (C%:E : extended_real_line R)).
have hH : is_measure_summable mu H.
  exists C; exact: probability_constant_integral hm C hprob.
have hF k : is_measure_measurable_function mu (F k).
  exact: (@measurable_nonnegative_extended_power R X mu hm (f k) p
    (fun x => (hb k x).1) hp0 (hf k)).
have hG : is_measure_measurable_function mu G.
  exact: (@measurable_nonnegative_extended_power R X mu hm g p
    (fun x => (hgb x).1) hp0 hg).
have hbound k : measure_almost_everywhere mu
    (partial_extended_le_locus (partial_extended_function_absolute_value (F k)) H).
  apply: (@measure_almost_everywhere_mono R X mu hm setT _ _
    (measure_almost_everywhere_true hm))=> x _.
  exists (`|extended_positive_power (f k x) p|), C%:E; split.
  - exists (extended_positive_power (f k x) p); by split.
  - split=> //.
    rewrite (gee0_abs (extended_positive_power_nonnegative (f k x) p)).
    exact: (@extended_positive_power_monotone R (f k x) M%:E p (hb k x).1 (hb k x).2 hp0).
have hlimit : measure_almost_everywhere mu (partial_extended_convergence_locus F G).
  apply: (@measure_almost_everywhere_mono R X mu hm setT _ _
    (measure_almost_everywhere_true hm))=> x _.
  exists (fun k => extended_positive_power (f k x) p), (extended_positive_power (g x) p).
  split=> //; split=> //.
  exact: (@extended_positive_power_order_limit R (fun k => f k x) (g x) p
    (fun k => (hb k x).1) (hgb x).1 hp0 (hl x)).
have [a [e [b [hai [hbi [hei [hel hal]]]]]]] :=
  @measure_bounded_convergence R X mu hm F G H hH hF hG hbound hlimit.
have hvalue (u : X -> extended_real_line R) (v : \bar R) :
    (forall x, 0<=u x) -> is_measure_integral mu (partial_function_total u) v -> 0<=v.
  move=> hu hi.
  have hpos : measure_almost_everywhere mu (partial_extended_nonnegative_locus (partial_function_total u)).
    apply: (@measure_almost_everywhere_mono R X mu hm setT _ _
      (measure_almost_everywhere_true hm))=> x _; exists (u x); by split.
  have he := @measure_lower_integral_unique R X mu (partial_function_total u) _ v
    (measure_lower_integral_specification mu _) hi.2.2.
  have hnon := @measure_lower_integral_nonnegative R X mu hm (partial_function_total u) hpos.
  by rewrite he in hnon.
have ha0 k : 0<=(a k)%:E.
  exact: (hvalue _ _ (fun x => extended_positive_power_nonnegative (f k x) p) (hai k)).
have hb0 : 0<=b%:E.
  exact: (hvalue _ _ (fun x => extended_positive_power_nonnegative (g x) p) hbi).
have heF k : nonnegative_extended_exponent_norm mu (f k) p%:E=
    extended_positive_power (a k)%:E p^-1.
  have [_ [v [hi ->]]] := @nonnegative_extended_exponent_norm_specification R X mu (f k) p%:E
    hm (fun x => (hb k x).1) hp (hf k).
  by rewrite (measure_integral_unique hi (hai k)).
have heG : nonnegative_extended_exponent_norm mu g p%:E=extended_positive_power b%:E p^-1.
  have [_ [v [hi ->]]] := @nonnegative_extended_exponent_norm_specification R X mu g p%:E
    hm (fun x => (hgb x).1) hp hg.
  by rewrite (measure_integral_unique hi hbi).
have hefun : (fun k => nonnegative_extended_exponent_norm mu (f k) p%:E)=
    (fun k => extended_positive_power (a k)%:E p^-1) by apply: funext=> k; exact: heF.
rewrite hefun heG.
apply: extended_positive_power_order_limit ha0 hb0 _ hal.
by rewrite invr_gt0.
Qed.
