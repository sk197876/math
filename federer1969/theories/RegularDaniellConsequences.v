(** Federer (1969), 2.5.3, p. 94, four further conditions, proofs p. 95.
    These public consequences use only the abstract representing-integral
    and Federer L-regularity laws. The suiting-envelope property is derived
    from uniqueness. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP PartialExtendedOrderLoci
  PartialExtendedArithmetic PartialAbsolutePartsGraph SummableRealFunctionUP
  FunctionLatticeUP FunctionLatticeLaws FunctionLatticeRegularityUP RegularDaniellEnvelope
  RealIntegralFunctionalUP DaniellInnerDifferenceSupremum DaniellPositiveL1Density
  LatticeSeriesCoverUP DaniellCountableFiniteCover DaniellMeasurabilityCriterion
  ExtendedRealBoundsUP MeasureUP MeasureIntegralUP MeasureAlmostUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [regular_daniell_inner_supremum]: first further condition of
    Federer 2.5.3, p. 94 *)
Theorem regular_daniell_inner_supremum (R : realType) (X : choiceType)
    (L : set (X -> R)) (A : (X -> R) -> R) (hL : is_function_lattice L)
    (mu : set X -> \bar R) (hm : is_measure mu) (hA : is_real_integral_functional mu L A)
    (hr : is_function_lattice_regular L mu) (S : set X) :
  measure_measurable mu S -> mu S < +oo ->
  is_extended_real_supremum (function_lattice_inner_difference_values L mu S) (mu S).
Proof.
exact: (@daniell_inner_difference_supremum R X L A hL mu hm hA
  (@regular_representing_measure_envelope R X L A hL mu hm hA hr) S).
Qed.

(** Source for [regular_daniell_positive_l1_density]: second further
    condition of Federer 2.5.3, p. 94 The printed 4 delta is retained, with
    a witness for the error's actual integral and the original
    partial-domain convention. *)
Theorem regular_daniell_positive_l1_density (R : realType) (X : choiceType)
    (L : set (X -> R)) (A : (X -> R) -> R) (hL : is_function_lattice L)
    (mu : set X -> \bar R) (hm : is_measure mu) (hA : is_real_integral_functional mu L A)
    (hr : is_function_lattice_regular L mu) (f : partial_function X (extended_real_line R)) (d : R) :
  is_measure_summable mu f ->
  measure_almost_everywhere mu (partial_extended_nonnegative_locus f) -> (0 < d)%R ->
  exists (h : X -> R) (q : R), positive_function_lattice L h /\
    is_measure_integral mu
      (partial_extended_function_absolute_value (partial_extended_function_subtract (real_total_integrand h) f)) q%:E /\
    (q < 4*d)%R.
Proof.
exact: (@daniell_nonnegative_summable_four_delta R X L A hL mu hm hA
  (@regular_representing_measure_envelope R X L A hL mu hm hA hr) f d).
Qed.

(** Source for [regular_daniell_countably_finite_iff]: third further
    condition of Federer 2.5.3, p. 94 Arbitrary countable covering families
    and the empty set are included. *)
Theorem regular_daniell_countably_finite_iff (R : realType) (X : choiceType)
    (L : set (X -> R)) (A : (X -> R) -> R) (hL : is_function_lattice L)
    (mu : set X -> \bar R) (hm : is_measure mu) (hA : is_real_integral_functional mu L A)
    (hr : is_function_lattice_regular L mu) (T : set X) :
  is_countably_finite_measure_set mu T <-> exists f, is_positive_lattice_series_cover L T f.
Proof.
have [g hg] := @function_lattice_regular_nonempty R X L mu hm hr.
exact: (@daniell_countably_finite_series_iff R X L A hL mu hm hA
  (@regular_representing_measure_envelope R X L A hL mu hm hA hr) T
  (@function_lattice_zero R X L hL g hg)).
Qed.

(** Source for [regular_daniell_measurability_iff]: fourth further condition
    of Federer 2.5.3, p. 94 It tests every subset B against all closed unit
    levels of positive lattice functions. *)
Theorem regular_daniell_measurability_iff (R : realType) (X : choiceType)
    (L : set (X -> R)) (A : (X -> R) -> R) (hL : is_function_lattice L)
    (mu : set X -> \bar R) (hm : is_measure mu) (hA : is_real_integral_functional mu L A)
    (hr : is_function_lattice_regular L mu) (B : set X) :
  measure_measurable mu B <-> forall f, positive_function_lattice L f ->
    measure_measurable mu (B `&` [set x | (1 <= f x)%R]).
Proof.
exact: (@daniell_measurable_iff_unit_level_intersections R X L A hL mu hm hA
  (@regular_representing_measure_envelope R X L A hL mu hm hA hr) B).
Qed.
