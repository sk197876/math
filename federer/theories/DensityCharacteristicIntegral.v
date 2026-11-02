(** Federer (1969), 2.4.10, p. 85: the characteristic-function and
    positive-multiple cases of the change-of-density formula. Partial
    density domains are retained: the product and zero extension agree
    almost everywhere. Source context: PartialZeroExtensionUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import RealMetricBackground ExtendedRealOrderTopology PartialFunctionUP PartialFunctionBasic
  PartialZeroExtension PartialDensityProduct MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasurableFunctionUP
  MeasurableZeroExtension ZeroExtensionNonnegative PartialExtendedOrderLoci MeasureIntegralUP MeasureIntegralBounds
  MeasureIntegralUniqueness MeasureIntegralGraphEquivalence MeasureIntegralAlmostEquality MeasureNonnegativeIntegral
  MeasureSubsetIntegral MeasureDensityUP MeasureDensityCover MeasureDensityMeasurable
  MeasureUpperIntegralScale MeasureIntegralScaleLaw CharacteristicFunctionUP MeasureStepIntegralIdentification
  MeasureFiniteCharacteristicIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [real_total_embedding_graph]: supporting
    identification of the embedded real characteristic sums in
    Federer 2.4.10, p. 85, with their total extended values. *)
Lemma real_total_embedding_graph (R : realType) (X : Type) (u : X -> real_line_metric R) x y :
  partial_function_graph (partial_real_function_embed (partial_function_total u)) x y <->
  partial_function_graph (partial_function_total (fun x => (u x)%:E : extended_real_line R)) x y.
Proof.
split; first by move=> [r [hr ery]]; rewrite -(hr : u x=r) in ery.
move=> hy; exists (u x); by split.
Qed.

(** Source for [measurable_density_subset_integral]: for a measurable
    nonnegative density the upper integral over a measurable A is its signed
    integral, as used in Federer 2.4.10, p. 85 *)
Lemma measurable_density_subset_integral (R : realType) (X : choiceType)
    (mu nu : set X -> \bar R) (hm : is_measure mu)
    (h : partial_function X (extended_real_line R)) (A : set X) :
  is_measure_density mu h nu -> measure_almost_everywhere mu (partial_extended_nonnegative_locus h) ->
  is_measure_measurable_function mu h -> measure_measurable mu A ->
  is_measure_subset_integral mu A h (nu A).
Proof.
move=> hn hp hh hA.
have hcut := @measurable_zero_extension R X (extended_real_line R) mu hm 0 A h hA hh.
have hpos := @zero_extension_nonnegative_almost R X mu hm A h hp.
have hi := (@nonnegative_measurable_function_integral R X mu hm _ hcut hpos).1.
have he := @measure_upper_integral_unique R X mu _ _ _ (measure_upper_integral_specification mu _) hi.2.1.
by rewrite (hn A) /measure_subset_upper_integral he.
Qed.

(** Source for [density_weighted_characteristic_integral]: direct
    positive-multiple characteristic case of the change-of-density identity
    in Federer 2.4.10, p. 85. *)
Lemma density_weighted_characteristic_integral (R : realType) (X : choiceType)
    (mu nu : set X -> \bar R) (hm : is_measure mu)
    (h : partial_function X (extended_real_line R)) (A : set X)
    (s : X -> real_line_metric R) (r : R) :
  is_measure_density mu h nu -> measure_almost_everywhere mu (partial_extended_nonnegative_locus h) ->
  is_measure_measurable_function mu h -> measure_measurable mu A -> is_characteristic_function A s -> (0 < r)%R ->
  is_measure_integral nu (partial_function_total (fun x => ((r*s x)%R%:E : extended_real_line R))) (r%:E*nu A) /\
  is_measure_integral mu (partial_density_product
    (partial_function_total (fun x => ((r*s x)%R%:E : extended_real_line R))) h) (r%:E*nu A).
Proof.
move=> hn hp hh hA hs hr.
have hnu := @measure_density_is_measure R X mu nu hm h hn hp.
have hAnu := @measure_density_preserves_measurable_sets R X mu nu hm h A hn hp hA.
split.
- have hi := @measure_positive_characteristic_integral R X nu hnu A s r hs hAnu hr.
  exact: measure_integral_graph_equivalent (real_total_embedding_graph _) hi.
- have hcut := @measurable_density_subset_integral R X mu nu hm h A hn hp hh hA.
  have hscale := @measure_integral_positive_scale R X mu hm r _ (nu A) hr hcut.
  apply: (@measure_integral_almost_equal R X mu hm _ _ (r%:E*nu A) hscale).
  apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ (measurable_function_domain hh)).
  move=> x [z hz]; have [hx|hx] := pselect (A x).
  + have hsx := characteristic_on_set hs hx.
    exists (r%:E*z); split.
    * exists z; split=> //; apply/partial_function_zero_extension_graph; left; by split.
    * apply/partial_density_product_graph; exists r%:E,z; split.
      -- by rewrite /= hsx mulr1.
      -- by split.
  + have hsx := characteristic_off_set hs hx.
    exists 0; split.
    * exists 0; split; last exact: mule0.
      apply/partial_function_zero_extension_graph; right; by split.
    * apply/partial_density_product_graph; exists 0,z; split.
      -- by rewrite /= hsx mulr0.
      -- split=> //; exact: mul0e.
Qed.
