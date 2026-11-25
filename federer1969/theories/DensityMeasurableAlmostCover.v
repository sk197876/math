(** Regularity of the density measure used in Federer (1969), 2.9.8, p. 156.
    We use a nonnegative approximant from the existing 2.4.10 development,
    so domination also holds off the covering set. This is a supporting
    regularity proof, not an additional hypothesis on Federer's density. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP PartialZeroExtension
  PartialExtendedOrderLoci MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasureFiniteClosure
  MeasurableFunctionUP MeasurableExtendedComparisons ZeroExtensionNonnegative
  MeasureIntegralUP MeasureIntegralBounds MeasureIntegralUniqueness MeasureSubsetIntegral
  MeasureDensityUP MeasureNonnegativeUpperApproximation MeasureUpperIntegralMonotone.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [density_measurable_almost_cover]: supporting regularity for
    the measure psi introduced in Federer 2.9.8, p. 156 Every
    finite-density-mass target has a measurable superset with arbitrarily
    small excess mass. The target itself need not be measurable. *)
Lemma density_measurable_almost_cover (R : realType) (X : choiceType)
    (phi nu : set X -> \bar R) (f : partial_function X (extended_real_line R))
    (S : set X) (e : R) :
  is_measure phi -> is_measure_density phi f nu -> is_measure_measurable_function phi f ->
  measure_almost_everywhere phi (partial_extended_nonnegative_locus f) ->
  nu S< +oo -> (0<e)%R ->
  exists B, measure_measurable phi B /\ S `<=` B /\ nu B<nu S+e%:E.
Proof.
move=> hm hnu hf hp hSf he.
pose fS := partial_function_zero_extension (0 : extended_real_line R) S f.
have hfp := @zero_extension_nonnegative_almost R X phi hm S f hp.
have hfinite : measure_upper_integral phi fS< +oo.
  change (measure_subset_upper_integral phi S f< +oo); by rewrite -(hnu S).
have [v [a [hvpos [hvi [hfv herr]]]]] := @measure_nonnegative_upper_approximation R X phi hm fS e hfp hfinite he.
pose C := partial_extended_le_locus f v.
pose E := S `\` C.
have hCm : measure_measurable phi C := @measurable_extended_weak_comparison R X phi f v hm hf hvi.1.
have hE0 : phi E=0.
  apply: (@measure_null_subset R X phi hm E (~` partial_extended_le_locus fS v)) hfv.
  move=> x [hx hnC] [y [z [hy [hz hyz]]]].
  have [[_ hfx]|[hnS _]] := (partial_function_zero_extension_graph (0 : extended_real_line R) S f x y).1 hy.
  - apply: hnC; exists y,z; by split=> //; split.
  - exact: hnS hx.
pose B := C `|` E.
have hBm : measure_measurable phi B := @measure_measurable_union R X phi hm C E hCm
  (@measure_null_measurable R X phi hm E hE0).
have hSB : S `<=` B.
  move=> x hx; case: (pselect (C x))=> hc; [by left|right; by split].
have hnE : measure_almost_everywhere phi (~` E) by rewrite /measure_almost_everywhere setCK.
have hgood := @measure_almost_everywhere_and R X phi hm (~` E) (partial_function_domain v) hnE
  (measurable_function_domain hvi.1).
have hcompare : measure_almost_everywhere phi (partial_extended_le_locus
    (partial_function_zero_extension (0 : extended_real_line R) B f) v).
  apply: (@measure_almost_everywhere_mono R X phi hm _ _ _ hgood)=> x [hnEx [z hz]].
  case: (pselect (B x))=> hx.
  - have hCx : C x by case: hx=> // hx; exfalso; exact: hnEx hx.
    have [y [w [hy [hw hyw]]]] := hCx.
    exists y,w; split.
    + apply/partial_function_zero_extension_graph; left; by split.
    + by split.
  - exists 0,z; split.
    + apply/partial_function_zero_extension_graph; right; by split.
    + split=> //; exact: hvpos x z hz.
have hval := @measure_upper_integral_unique R X phi v (measure_upper_integral phi v) a%:E
  (measure_upper_integral_specification phi v) hvi.2.1.
have hbound : nu B<=a%:E.
  rewrite (hnu B) /measure_subset_upper_integral -hval.
  exact (@measure_upper_integral_monotone R X phi hm
    (partial_function_zero_extension (0 : extended_real_line R) B f) v hcompare).
have herr' : a%:E<nu S+e%:E by rewrite (hnu S); exact herr.
exists B; split=> //; split=> //; exact: le_lt_trans hbound herr'.
Qed.
