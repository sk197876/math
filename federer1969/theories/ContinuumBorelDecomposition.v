(** Federer (1969), 2.5.10, p. 101, second paragraph: CH supplies a disjoint
    finite-measure decomposition for every Borel regular measure over a
    separable metric space. The continuum bound for the closed family is
    2.2.4, p. 62; the almost-cover property is 2.2.3, pp. 61–62. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets functions cardinality reals constructive_ereal topology.
From Federer Require Import MeasureUP BorelRegularMeasureUP TopologicalBorel CardinalInjection
  CountableBaseCardinality SeparableMetricBaseSealed CardinalSuccessorUP
  ContinuumHypothesisUP ContinuumCountablePrefixes BorelRegularFiniteClosedCover
  FiniteCoverReindexing OrderedFamilyDisjointification OrderedFiniteDecomposition FiniteMeasureDecompositionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope card_scope.
Local Open Scope ereal_scope.

(** Source for [continuum_borel_regular_finite_decomposition]:
    direct conditional assertion in Federer 2.5.10, p. 101.
    CH remains a premise. Code the finite closed family into a
    continuum representative with countable prefixes, then subtract
    the preceding sets. Empty unused codes contribute empty pieces.
    The result covers every finite-measure set up to a null remainder. *)
Theorem continuum_borel_regular_finite_decomposition (R : realType) (T : metricType R)
    (mu : set T -> \bar R) (hm : is_measure mu) (hr : is_borel_regular_measure mu) :
  continuum_hypothesis -> (exists S : set T, countable S /\ dense S) ->
  exists (C : set (set nat)) (B : set nat -> set T), is_finite_measure_decomposition mu C B.
Proof.
move=> hCH [S [hc hd]].
pose U := @SeparableMetricBase.value R T S hc hd.
have hU := @SeparableMetricBase.laws R T S hc hd.
pose D := finite_closed_measure_family mu.
have hD : D #<= (@setT (set nat)).
  apply: card_le_trans _ (countable_base_closed_cardinality_bound hU).
  apply: subset_card_le=> K [hk _]; exact: hk.
have [C [r [hw [hcard hprefix]]]] := continuum_countable_prefix_representative hCH.
have [f [hf hi]] := @cardinal_injection_with_default [the choiceType of set T]
  [the choiceType of set nat] D C set0 (card_le_trans hD hcard).
have hfinite K : D K -> measure_measurable mu K /\ mu K < +oo.
  move=> [hk hfin]; split=> //.
  exact (@borel_regular_borel_measurable R T mu hm hr K (closed_borel_set hk)).
have [H [hH hcover]] := @finite_measure_cover_reindexing R T [the choiceType of set T]
  [the choiceType of set nat] mu hm D C (fun K => K) f hf hi hfinite
  (borel_regular_finite_closed_countable_cover hm hr).
exists C, (ordered_family_piece C r H).
exact (@ordered_finite_measure_decomposition R T [the choiceType of set nat] mu hm C r H hw hprefix hH hcover).
Qed.
