(** Federer (1969), 2.5.14, p. 107: alpha(V) is bounded by the associated
    K(X)-regular measure, hence Phi(A) is bounded by that measure on every
    set. Consult the erratum p. 2, book p. 107 line 24, for the corrected
    measure symbol in this passage. We use its measurable positive locus, so
    no measurability of a compact support is assumed. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import CompactSupportFunctionUP CompactOpenContentUP CompactSupportMeasureRegularity
  FunctionLatticeLevelMeasurability FunctionLatticeRegularityUP RealIntegralFunctionalUP
  RealTotalCharacteristicBounds SummableRealFunctionUP PartialFunctionUP ExtendedRealOrderTopology
  MeasurableFunctionBorel CountableOrderIntervals TopologicalBorel OpenCoverContentUP
  ExtendedRealBoundsUP ExtendedRealBounds MeasureUP MeasureBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [compact_open_test_representing_measure_bound]: each test
    integral is at most the measure of V, supporting alpha(V) <= phi(V) in
    Federer 2.5.14, p. 107 V itself need not be measurable: comparison is
    through the measurable positive locus. *)
Lemma compact_open_test_representing_measure_bound (R : realType) (X : topologicalType)
    (mu : set X -> \bar R) (A : (X -> R) -> R) (hm : is_measure mu)
    (hA : is_real_integral_functional mu (@compactly_supported_continuous_functions R X) A) V f :
  is_compact_open_test_function V f -> (A f)%:E <= mu V.
Proof.
move=> [hf [hb hs]]; pose P := [set x | (0 < f x)%R].
have hi := hA f hf.
have hP : measure_measurable mu P.
  rewrite /P -real_total_strict_upper_level.
  apply: (@measurable_function_borel_preimage R X (extended_real_line R) mu hm _ hi.1).
  apply: open_borel_set; exact: order_strict_upper_ray_open.
have hbound : (A f)%:E <= 1%:E * mu P.
  apply: (@real_total_integral_supported_upper_bound R X mu hm P f (A f)%:E 1%R hP (@ltr01 R) hi).
  - move=> x _; exact: (andP (hb x)).2.
  - move=> x hx; apply/eqP; rewrite eq_le (andP (hb x)).1 andbT leNgt.
    apply/negP; exact hx.
rewrite mul1e in hbound; apply: le_trans hbound _.
apply: (@measure_mono R X mu hm P V)=> x hx; apply: hs; apply: subset_closure=> hz.
change (is_true ((0 < f x)%R)) in hx; by move: hx; rewrite hz ltxx.
Qed.

(** Source for [compact_open_content_representing_measure_bound]: alpha(V)
    <= phi(V) in Federer 2.5.14, p. 107 The representing measure need not
    yet be known regular for this inequality. *)
Lemma compact_open_content_representing_measure_bound (R : realType) (X : topologicalType)
    (mu : set X -> \bar R) (A : (X -> R) -> R) (a : set X -> \bar R)
    (hm : is_measure mu)
    (hA : is_real_integral_functional mu (@compactly_supported_continuous_functions R X) A)
    (ha : is_compact_open_content A a) V : open V -> a V <= mu V.
Proof.
move=> hV; apply: (extended_real_supremum_least (ha V hV))=> c [f [hf ->]].
exact: (@compact_open_test_representing_measure_bound R X mu A hm hA V f hf).
Qed.

(** Source for [compact_open_envelope_below_regular_measure]: Phi(A) <=
    phi(A) for every A in Federer 2.5.14, p. 107 Outer approximation by open
    measurable sets supplies the comparison for arbitrary, possibly
    nonmeasurable or infinite-measure sets. *)
Theorem compact_open_envelope_below_regular_measure (R : realType) (X : topologicalType)
    (mu nu : set X -> \bar R) (A : (X -> R) -> R) (a : set X -> \bar R)
    (hm : is_measure mu)
    (hA : is_real_integral_functional mu (@compactly_supported_continuous_functions R X) A)
    (hr : is_function_lattice_regular (@compactly_supported_continuous_functions R X) mu)
    (ha : is_compact_open_content A a) (hn : is_open_cover_envelope a nu) S : nu S <= mu S.
Proof.
rewrite (@compact_support_regular_open_infimum R X mu A hm hA hr S).
apply: extended_real_inf_greatest=> c [V [hV [_ [hSV ->]]]].
exact (le_trans (@open_cover_envelope_lower R X a nu hn S V hV hSV)
  (@compact_open_content_representing_measure_bound R X mu A a hm hA ha V hV)).
Qed.
