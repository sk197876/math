(** Federer (1969), 2.5.9, p. 100: supporting identification of two
    densities on a positive lattice test. Testing the measurable
    positive-sign piece and the whole function shows that the absolute
    product has integral zero. This supplies detail for the unqualified
    almost-uniqueness assertion; it does not impose boundedness on the
    competing density. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric MeasureUP MeasureAlmostUP MeasurableFunctionUP MeasurableTotalBasic
  FunctionLatticeUP FunctionLatticeRegularityUP RealIntegralFunctionalUP
  SummableRealFunctionUP SummableRealArithmetic MeasureIntegralUP
  TotalScalarLpUP TotalScalarComparison TotalScalarLpZeroCriterion TotalLoneSummability
  CharacteristicFunctionUP CharacteristicFunctionSealed LatticeZeroPairingPieces.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [lattice_zero_pairing_product_almost_zero]:
    supporting consequence of positive density for Federer 2.5.9,
    p. 100: each positive lattice test times the difference
    of representing densities vanishes almost everywhere. *)
Theorem lattice_zero_pairing_product_almost_zero (R : realType) (X : choiceType)
    (L : set (X -> R)) (hL : is_function_lattice L) (F : (X -> R) -> R)
    (mu : set X -> \bar R) (hm : is_measure mu) (w : X -> R) :
  is_real_integral_functional mu L F -> is_function_lattice_regular L mu ->
  is_measure_measurable_function mu (total_scalar_function w) ->
  (forall h, L h -> is_measure_integral mu (real_total_integrand (fun x => (h x*w x)%R)) 0) ->
  forall f, positive_function_lattice L f ->
    measure_almost_everywhere mu [set x | (f x*w x)%R=0%R].
Proof.
move=> hrep hr hw hzero f hf.
pose E := [set x | (0 <= w x)%R].
pose s := @CharacteristicFunction.value R X E.
have hs := @CharacteristicFunction.laws R X E.
have hzm := @measurable_total_constant R X
  [the topologicalType of real_norm_metric_space (scalar_absolute_value_norm R)] mu hm 0%R.
have hE : measure_measurable mu E := @total_scalar_measurable_comparison R X mu hm (fun _ => 0%R) w hzm hw.
have hip := @lattice_zero_pairing_characteristic_piece R X L hL F mu hm w hrep hr hw hzero f E s hf hE hs.
have hi := hzero f hf.1.
have hdouble := @real_total_integral_scale R X mu hm (fun x => (f x*s x*w x)%R) 0%R 2%R hip.
rewrite mulr0 in hdouble.
have habs := @real_total_integral_subtract R X mu hm _ (fun x => (f x*w x)%R) 0%R 0%R hdouble hi.
rewrite subrr in habs.
have he : (fun x => (2*(f x*s x*w x)-f x*w x)%R)=(fun x => `|f x*w x|%R).
  apply: funext=> x; case: (pselect (E x))=> hx.
  - have hw0 : (0 <= w x)%R := hx.
    by rewrite /s (characteristic_on_set hs hx) mulr1 mulr_natl mulr2n addrK (ger0_norm (mulr_ge0 (hf.2 x) hw0)).
  - have hw0 : (w x <= 0)%R by rewrite leNgt; apply/negP=> hp; apply: hx; exact: ltW hp.
    by rewrite /s (characteristic_off_set hs hx) !mulr0 !mul0r mulr0 sub0r (ler0_norm (mulr_ge0_le0 (hf.2 x) hw0)).
rewrite he in habs.
have hfm : total_scalar_lp mu 1 (fun x => (f x*w x)%R).
  apply: (@summable_real_total_lone R X mu hm); by exists 0%R.
have hnorm := @total_lone_norm_from_absolute_integral R X mu hm _ 0%R hfm.2.1 habs.
exact: (@total_scalar_lp_zero_norm_almost_zero R X mu hm 1 _ hfm hnorm).
Qed.
