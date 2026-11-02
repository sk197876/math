(** Federer (1969), 2.5.14, p. 107: Phi and the associated measure agree on
    positive strict levels. Here we obtain the stronger F1 agreement
    directly from the compact closed-level approximants of 2.5.3 and
    localized cutoffs. This is an explicit proof variation, using results
    already established in the first paragraph of 2.5.14. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import CompactSupportFunctionUP CompactSupportFunctionLattice CompactSupportLevels
  CompactOpenContentUP CompactOpenContentMeasureBound CompactCutoffUP LocalizedCompactCutoffUP LocalizedCompactCutoff
  FunctionLatticeUP FunctionLatticeLevelFamilies FunctionLatticeUnionInnerApproximation RepresentedLatticeClosedLevels
  RealIntegralFunctionalUP RealTotalCharacteristicBounds ExtendedRealBoundsUP OpenCoverContentUP OpenCoverContentLaws
  MeasureUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [compact_open_content_increasing_level_value]: agreement on
    F1 extending the strict-level equality in Federer 2.5.14, p. 107 The
    compact unit-level supremum and localized cutoffs replace the two
    successive right limits used in the printed proof. *)
Theorem compact_open_content_increasing_level_value (R : realType) (X : topologicalType)
    (mu : set X -> \bar R) (A : (X -> R) -> R) (a : set X -> \bar R)
    (hm : is_measure mu)
    (hA : is_real_integral_functional mu (@compactly_supported_continuous_functions R X) A)
    (ha : is_compact_open_content A a) : hausdorff_space X -> locally_compact (@setT X) ->
  forall V, function_lattice_increasing_levels (@compactly_supported_continuous_functions R X) V -> a V=mu V.
Proof.
move=> hh hl V hV.
have ho := @compact_support_increasing_level_open R X V hV.
apply/eqP; rewrite eq_le; apply/andP; split.
- exact: (@compact_open_content_representing_measure_bound R X mu A a hm hA ha V ho).
- have hs := @represented_lattice_union_inner_supremum R X _ A
    (@compactly_supported_continuous_functions_lattice R X) mu hm hA V hV.
  apply: (extended_real_supremum_least hs)=> c [h [hh' [hCV ->]]].
  pose C := [set x | (1 <= h x)%R].
  have hC : compact C := @compact_support_positive_closed_level_compact R X h 1%R hh'.1 (@ltr01 R).
  pose u := @localized_compact_cutoff R X C V hh hl hC ho hCV.
  have hu := @localized_compact_cutoff_specification R X C V hh hl hC ho hCV.
  have hcut := localized_compact_cutoff_laws hu.
  have huf := compact_cutoff_function hcut.
  have hCm := @represented_lattice_closed_upper_level_measurable R X _ A mu hm hA h 1%R hh'.1.
  have hub : 1%:E*mu C <= (A u)%:E.
    apply: (@real_total_integral_level_lower_bound R X mu hm C u (A u)%:E 1%R hCm (@ltr01 R) (hA u huf)).
    + move=> x; exact: (andP (compact_cutoff_range hcut x)).1.
    + move=> x hx; rewrite /u (compact_cutoff_on_set hcut hx); exact: lexx.
  rewrite mul1e in hub; apply: le_trans hub _.
  apply: (extended_real_supremum_upper (ha V ho)); exists u; split=> //.
  split=> //; split; [exact: compact_cutoff_range hcut|exact: localized_compact_cutoff_support hu].
Qed.

(** Source for [compact_open_envelope_increasing_level_value]: equality of
    Phi and phi on F1, extending the positive strict-level equality in
    Federer 2.5.14, p. 107 This conclusion includes F1 sets of infinite
    measure. *)
Theorem compact_open_envelope_increasing_level_value (R : realType) (X : topologicalType)
    (mu nu : set X -> \bar R) (A : (X -> R) -> R) (a : set X -> \bar R)
    (hm : is_measure mu)
    (hA : is_real_integral_functional mu (@compactly_supported_continuous_functions R X) A)
    (ha : is_compact_open_content A a) (hc : is_open_cover_content a)
    (hn : is_open_cover_envelope a nu) : hausdorff_space X -> locally_compact (@setT X) ->
  forall V, function_lattice_increasing_levels (@compactly_supported_continuous_functions R X) V -> nu V=mu V.
Proof.
move=> hh hl V hV.
rewrite (@open_cover_envelope_open_value R X a nu hc hn V (@compact_support_increasing_level_open R X V hV)).
exact: (@compact_open_content_increasing_level_value R X mu A a hm hA ha hh hl V hV).
Qed.
