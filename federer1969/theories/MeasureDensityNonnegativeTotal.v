(** Federer (1969), 2.4.10, p. 85: nonnegative case of the change-of-density
    identity, using 2.3.3 and 2.4.8 as the book prescribes. The integrand
    here is total; later null-replacement arguments recover arbitrary
    partial domains. The density may already be partial. Source context:
    PartialZeroExtensionUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import RealMetricBackground ExtendedRealOrderTopology PartialFunctionUP PartialFunctionBasic
  PartialDensityProduct MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasurableFunctionUP PartialExtendedOrderLoci
  MeasureIntegralUP MeasureDensityUP MeasureDensityCover DensityCharacteristicIntegral
  WeightedCharacteristicExpansionUP WeightedCharacteristicExpansion PositiveVanishingWeightsSealed
  CharacteristicFunctionUP MeasureCharacteristicUpperBound PartialDensitySeries NonnegativeSum
  MeasureCountableNonnegativeSum.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_density_nonnegative_total]: nonnegative
    total-integrand case of Federer 2.4.10, p. 85,
    proved by its stated characteristic-expansion argument.
    Both integral values may be positive infinity. *)
Lemma measure_density_nonnegative_total (R : realType) (X : choiceType)
    (mu nu : set X -> \bar R) (hm : is_measure mu)
    (h : partial_function X (extended_real_line R)) (f : X -> extended_real_line R) :
  is_measure_density mu h nu -> is_measure_measurable_function mu h ->
  (forall x z, partial_function_graph h x z -> 0 <= z) ->
  is_measure_measurable_function mu (partial_function_total f) -> (forall x, 0 <= f x) ->
  exists a, is_measure_integral nu (partial_function_total f) a /\
    is_measure_integral mu (partial_density_product (partial_function_total f) h) a.
Proof.
move=> hn hh hp hf hfp.
have hpAE : measure_almost_everywhere mu (partial_extended_nonnegative_locus h).
  apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ (measurable_function_domain hh)).
  move=> x [z hz]; exists z; split=> //; exact: hp x z hz.
have hnu := @measure_density_is_measure R X mu nu hm h hn hpAE.
pose r := @PositiveVanishingWeights.value R.
have hr := @PositiveVanishingWeights.laws R.
have [A [s [hrep _]]] := @measurable_weighted_characteristic_expansion R X mu hm f r hf hfp hr.
pose u n x := ((r n*s n x)%R%:E : extended_real_line R).
pose a n := (r n)%:E*nu (A n).
have hup n x : 0 <= u n x.
  rewrite /u lee_fin; apply: mulr_ge0 (ltW (expansion_weights_positive hr n)) _.
  exact: (andP (characteristic_function_scalar_bounds (expansion_characteristic_laws hrep n) x)).1.
have hterm n : is_measure_integral nu (partial_function_total (u n)) (a n) /\
    is_measure_integral mu (partial_density_product (partial_function_total (u n)) h) (a n).
  exact (@density_weighted_characteristic_integral R X mu nu hm h (A n) (s n) (r n)
    hn hpAE hh (expansion_sets_measurable hrep n) (expansion_characteristic_laws hrep n)
    (expansion_weights_positive hr n)).
have hsum x : nonnegative_sum setT (fun n => u n x)=f x := expansion_pointwise_sum hrep x.
exists (nonnegative_sum setT a); split.
- apply: (@measure_countable_nonnegative_integral_values R X [the choiceType of (nat : Type)] nu hnu
    setT (fun n => partial_function_total (u n)) (partial_function_total f) a (countableP setT)).
  + exact: partial_total_nonnegative_series (fun n _ => hup n) hsum.
  + move=> n _ x y hy; by rewrite -(hy : u n x=y); exact: hup.
  + move=> n _; exact: (hterm n).1.
- apply: (@measure_countable_nonnegative_integral_values R X [the choiceType of (nat : Type)] mu hm
    setT (fun n => partial_density_product (partial_function_total (u n)) h)
    (partial_density_product (partial_function_total f) h) a (countableP setT)).
  + apply: partial_density_total_series _ (fun n _ => hup n) hp hsum; by exists 0%N.
  + move=> n _ x y hy; have [b [c [hb [hc he]]]] := (partial_density_product_graph _ h x y).1 hy.
    rewrite -he; apply: mule_ge0; last exact: hp x c hc.
    by rewrite -(hb : u n x=b); exact: hup.
  + move=> n _; exact: (hterm n).2.
Qed.
