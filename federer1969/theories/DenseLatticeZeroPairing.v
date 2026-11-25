(** Federer (1969), 2.5.14, p. 108: supporting local uniqueness of Radon
    densities. This is the positive lattice-test portion of the uniqueness
    argument of 2.5.9, p. 100, with a proved density premise in place of
    lattice regularity. Dominated convergence is 2.4.9, p. 85. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric MeasureUP MeasurableFunctionUP FunctionLatticeUP
  RealIntegralFunctionalUP MeasureIntegralUP SummableRealFunctionUP TotalScalarLpUP
  TotalScalarLpCharacteristic CharacteristicFunctionUP RegularLatticeLoneDensity
  DensePositiveLatticeApproximation DominatedZeroPairingLimit MeasureAlmostUP MeasurableTotalBasic
  SummableRealArithmetic TotalScalarComparison TotalScalarLpZeroCriterion TotalLoneSummability
  CharacteristicFunctionSealed ScalarLipschitzExtensionUP FunctionSeminormDistance
  TotalScalarLpFiniteSeminorm.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [dense_lattice_zero_pairing_characteristic_piece]:
    supporting localization of the almost-uniqueness assertion in
    Federer 2.5.14, p. 108, by the argument of 2.5.9, p. 100. The arbitrary measurable
    weight need not have finite essential norm. *)
Theorem dense_lattice_zero_pairing_characteristic_piece (R : realType) (X : choiceType)
    (L : set (X -> R)) (hL : is_function_lattice L) (F : (X -> R) -> R)
    (mu : set X -> \bar R) (hm : is_measure mu) (w : X -> R) :
  is_real_integral_functional mu L F -> is_pseudometric_dense_subset (positive_function_lattice (total_scalar_lp mu 1))
    (positive_function_lattice L) (function_seminorm_distance (finite_total_scalar_lp_norm mu 1)) ->
  is_measure_measurable_function mu (total_scalar_function w) ->
  (forall h, L h -> is_measure_integral mu (real_total_integrand (fun x => (h x*w x)%R)) 0) ->
  forall f E s, positive_function_lattice L f -> measure_measurable mu E ->
    is_characteristic_function E s ->
    is_measure_integral mu (real_total_integrand (fun x => (f x*s x*w x)%R)) 0.
Proof.
move=> hrep hdense hw hzero f E s hf hE hs.
have hfm := @represented_lattice_in_total_lone R X mu hm L F hrep f hf.1.
have hg := (@positive_lp_characteristic_pieces R X mu hm 1 E s f hs hE (conj hfm hf.2)).1.
have hgf x : (f x*s x <= f x)%R.
  case: (pselect (E x))=> hx.
  - by rewrite (characteristic_on_set hs hx) mulr1.
  - by rewrite (characteristic_off_set hs hx) mulr0; exact: hf.2.
have [u [hu hlim]] := @dense_positive_lattice_almost_approximation R X L hL F mu hm hrep hdense
  f (fun x => (f x*s x)%R) hf hg hgf.
have hbound n x : (0 <= u n x <= f x)%R by apply/andP; split; [exact: (hu n).1.2|exact: (hu n).2].
apply: (@dominated_zero_pairing_limit R X mu hm u f (fun x => (f x*s x)%R) w
  hbound hf.2 hg.1.2.1 hw _ _ hlim).
- exists 0%R; exact: hzero f hf.1.
- move=> n; exact: hzero _ (hu n).1.1.
Qed.

(** Source for [dense_lattice_zero_pairing_product_almost_zero]:
    supporting consequence of positive density for Federer 2.5.9,
    p. 100: each positive lattice test times the difference
    of representing densities vanishes almost everywhere. *)
Theorem dense_lattice_zero_pairing_product_almost_zero (R : realType) (X : choiceType)
    (L : set (X -> R)) (hL : is_function_lattice L) (F : (X -> R) -> R)
    (mu : set X -> \bar R) (hm : is_measure mu) (w : X -> R) :
  is_real_integral_functional mu L F -> is_pseudometric_dense_subset (positive_function_lattice (total_scalar_lp mu 1))
    (positive_function_lattice L) (function_seminorm_distance (finite_total_scalar_lp_norm mu 1)) ->
  is_measure_measurable_function mu (total_scalar_function w) ->
  (forall h, L h -> is_measure_integral mu (real_total_integrand (fun x => (h x*w x)%R)) 0) ->
  forall f, positive_function_lattice L f ->
    measure_almost_everywhere mu [set x | (f x*w x)%R=0%R].
Proof.
move=> hrep hdense hw hzero f hf.
pose E := [set x | (0 <= w x)%R].
pose s := @CharacteristicFunction.value R X E.
have hs := @CharacteristicFunction.laws R X E.
have hzm := @measurable_total_constant R X
  [the topologicalType of real_norm_metric_space (scalar_absolute_value_norm R)] mu hm 0%R.
have hE : measure_measurable mu E := @total_scalar_measurable_comparison R X mu hm (fun _ => 0%R) w hzm hw.
have hip := @dense_lattice_zero_pairing_characteristic_piece R X L hL F mu hm w hrep hdense hw hzero f E s hf hE hs.
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
