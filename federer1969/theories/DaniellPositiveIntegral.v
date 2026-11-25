(** Federer (1969), proof of 2.5.2, p. 93: nonnegative lattice members are
    measurable and consequently integrable by 2.4.4(2), before their
    integral is identified with the functional value. Infinite values are
    allowed here; finiteness is a later conclusion. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import FunctionLatticeUP FunctionLatticeLaws MonotoneDaniellIntegralUP
  DaniellCoverUP DaniellCoverMeasure DaniellLatticeMeasurable RealTotalCharacteristicBounds
  SummableRealFunctionUP ExtendedRealOrderTopology MeasureUP MeasurableFunctionUP
  MeasurableFunctionBorel CountableOrderIntervals TopologicalBorel
  MeasureIntegralUP MeasureIntegralBounds MeasureNonnegativeIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [daniell_positive_lattice_integral]: existence of the
    nonnegative integral used in Federer 2.5.2, p. 93 *)
Lemma daniell_positive_lattice_integral (R : realType) (X : choiceType)
    (L : set (X -> R)) (A : (X -> R) -> R) (hL : is_function_lattice L)
    (hA : is_monotone_daniell_integral L A) (mu : set X -> \bar R)
    (hm : is_daniell_cover_envelope L A mu) (f : X -> R) :
  positive_function_lattice L f ->
  is_measure_integral mu (real_total_integrand f) (measure_lower_integral mu (real_total_integrand f)) /\
    0 <= measure_lower_integral mu (real_total_integrand f).
Proof.
move=> hf; have hmeasure := daniell_cover_is_measure hL hA hm (function_lattice_zero hL hf.1).
apply: (@nonnegative_measurable_function_integral R X mu hmeasure _).
- exact: (@daniell_positive_lattice_measurable R X L A hL hA mu hm f hf).
- exact: (@real_total_nonnegative_almost R X mu hmeasure f hf.2).
Qed.

(** Source for [daniell_positive_upper_level_measurable]: the measurable
    closed upper levels used in the layer estimates of Federer 2.5.2, p. 93 *)
Lemma daniell_positive_upper_level_measurable (R : realType) (X : choiceType)
    (L : set (X -> R)) (A : (X -> R) -> R) (hL : is_function_lattice L)
    (hA : is_monotone_daniell_integral L A) (mu : set X -> \bar R)
    (hm : is_daniell_cover_envelope L A mu) (f : X -> R) b :
  positive_function_lattice L f -> measure_measurable mu [set x | (b <= f x)%R].
Proof.
move=> hf; have hmeasure := daniell_cover_is_measure hL hA hm (function_lattice_zero hL hf.1).
have hmeas := daniell_positive_lattice_measurable hL hA hm hf.
rewrite -real_total_upper_level.
apply: (@measurable_function_borel_preimage R X (extended_real_line R) mu hmeasure _ hmeas).
apply: closed_borel_set; exact: order_closed_upper_ray_closed.
Qed.
