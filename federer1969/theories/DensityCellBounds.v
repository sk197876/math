(** Integral bounds on the geometric cells in Federer (1969), 2.9.7, p. 156.
    A density bounded between two finite nonnegative constants on a
    measurable cell has integral between those constants times the cell's
    measure. This follows from the step-function bounds of 2.4.2, p. 81, and
    the subset-integral convention 2.4.10, p. 85. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealMetricBackground ExtendedRealOrderTopology PartialFunctionUP
  PartialFunctionBasic PartialZeroExtension MeasureUP MeasureAlmostUP MeasureAlmostBasic
  CharacteristicFunctionUP CharacteristicFunctionSealed MeasureStepFunctionUP MeasureStepCharacteristic
  MeasureStepScalarOperation MeasureStepScaling MeasureIntegralUP MeasureIntegralBounds
  MeasureIntegralBoundsOrder MeasureSubsetIntegral MeasureDensityUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [density_measurable_cell_bounds]: supporting
    inequalities between the constant multiples and the
    integrals over P^n in Federer 2.9.7, p. 156.
    Cells may have infinite measure. Only the
    sealed density formula and abstract characteristic laws
    are used; the integrand's partial graph is retained. *)
Lemma density_measurable_cell_bounds (R : realType) (X : choiceType)
    (phi nu : set X -> \bar R) (g : partial_function X (extended_real_line R))
    (A : set X) (c d : R) :
  is_measure phi -> is_measure_density phi g nu -> measure_measurable phi A ->
  (0<=c)%R -> (0<=d)%R ->
  (forall x, A x -> exists y, partial_function_graph g x y /\ c%:E<=y /\ y<=d%:E) ->
  c%:E*phi A<=nu A /\ nu A<=d%:E*phi A.
Proof.
move=> hm hnu hA hc hd hvalues.
pose s := @CharacteristicFunction.value R X A.
have hs := @CharacteristicFunction.laws R X A.
have hu := @measure_characteristic_step_function R X phi hm A s hs hA.
have ha := @characteristic_step_assigned_sum R X phi hm A s hs.
have [hcu hca] := @measure_step_function_scale R X phi hm (partial_function_total s) c (phi A) hu ha.
have [hdu hda] := @measure_step_function_scale R X phi hm (partial_function_total s) d (phi A) hu ha.
pose f := partial_function_zero_extension (0 : extended_real_line R) A g.
have hpoint x : exists y, partial_function_graph f x y /\ (c*s x)%R%:E<=y /\ y<=(d*s x)%R%:E.
  case: (pselect (A x))=> hx.
  - have [y [hy [hcy hyd]]] := hvalues x hx.
    exists y; split.
    + apply/partial_function_zero_extension_graph; left; by split.
    + by rewrite /s (characteristic_on_set hs hx) !mulr1; split.
  - exists 0; split.
    + apply/partial_function_zero_extension_graph; right; by split.
    + by rewrite /s (characteristic_off_set hs hx) !mulr0; split.
have hlf : is_measure_lower_function phi f (partial_real_function_scale c (partial_function_total s)).
  split=> //.
  apply: (@measure_almost_everywhere_mono R X phi hm setT _ _ (measure_almost_everywhere_true hm))=> x _.
  have [y [hy [hcy _]]] := hpoint x.
  exists (c*s x)%R,y; split; first by exists (s x); split.
  by split.
have huf : is_measure_upper_function phi f (partial_real_function_scale d (partial_function_total s)).
  split=> //.
  apply: (@measure_almost_everywhere_mono R X phi hm setT _ _ (measure_almost_everywhere_true hm))=> x _.
  have [y [hy [_ hyd]]] := hpoint x.
  exists (d*s x)%R,y; split; first by exists (s x); split.
  by split.
have hl := @measure_lower_integral_bound R X phi f _ _ hlf hca.
have hh := @measure_upper_integral_bound R X phi f _ _ huf hda.
rewrite (hnu A); split; last exact hh.
exact: le_trans hl (@measure_lower_integral_le_upper R X phi hm f).
Qed.
