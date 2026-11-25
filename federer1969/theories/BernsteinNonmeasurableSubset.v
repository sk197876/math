(** Federer (1969), 2.2.4, p. 62: a set of positive finite measure, all of
    whose singletons are null, has a nonmeasurable subset for a Borel
    regular measure on a complete separable metric space. We derive every
    cardinal premise and use the sealed disjoint-selection interface. If A
    itself is not measurable, choose A, as in the final sentence of the
    printed proof. Source context: SeparableMetricBaseConstruction.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import MeasureUP MeasureBasic MeasureSplit MeasureFiniteClosure
  BorelRegularMeasureUP CompleteMetricUP PositiveClosedSubsets PositiveClosedCardinality
  SequenceSpace DisjointSelectionsUP DisjointSelectionsSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope card_scope.
Local Open Scope ereal_scope.

(** Source for [borel_regular_nonmeasurable_subset]: direct theorem in
    Federer 2.2.4, p. 62 All printed hypotheses are retained. The
    cardinality and transfinite-selection facts are proved prerequisites,
    not extra hypotheses or project axioms. *)
Theorem borel_regular_nonmeasurable_subset (R : realType) (T : metricType R)
    (mu : set T -> \bar R) (hm : is_measure mu)
    (hr : is_borel_regular_measure mu) (A : set T) :
  is_complete_metric_space T ->
  (exists D : set T, countable D /\ dense D) ->
  0 < mu A -> mu A < +oo -> (forall x, A x -> mu [set x] = 0) ->
  exists B, B `<=` A /\ ~ measure_measurable mu B.
Proof.
move=> hT hsep hp hf hz.
case: (pselect (measure_measurable mu A))=> hA; last by exists A; split=> // x hx.
have [C0 [hC0 [hC0A hp0]]] := positive_measurable_closed_subset hm hr hA hp hf.
pose G := positive_closed_family mu A.
pose I := [the choiceType of set_type G].
have hC0G : G C0 by split=> //; split.
pose i0 : I := @exist (set T) (fun C => C \in G) C0 (mem_set hC0G).
pose E (i : I) : set T := val i.
have hI : (@setT I) #<= (@setT (positive_sequence_space R)).
  apply: card_le_trans _ (positive_closed_family_cardinality_bound mu A hsep).
  exact: (proj1 (@card_eqPle _ _ (@setT I) G) (card_setT G)).1.
have hE i : (@setT (positive_sequence_space R)) #<= E i.
  have [hC [hCA hpos]] : G (val i) := set_valP i.
  have hzero x : E i x -> mu [set x] = 0 by move=> hx; exact: hz x (hCA x hx).
  have he := @positive_closed_sequence_cardinality R T mu hm (E i) hT hsep hC hpos hzero.
  exact: (proj1 (@card_eqPle _ _ (E i) (@setT (positive_sequence_space R))) he).2.
pose pair := @DisjointSelections.value R I T E i0 hI hE.
pose f := pair.1; pose g := pair.2.
have hfg : is_disjoint_family_selection E f g := @DisjointSelections.laws R I T E i0 hI hE.
pose B := f @` setT.
have hBA : B `<=` A.
  move=> x [i _ <-]; have hi : G (val i) := set_valP i.
  exact: hi.2.1 _ (disjoint_selection_left_member hfg i).
have hnoB C : closed C -> C `<=` B -> ~ (0 < mu C).
  move=> hC hCB hpos.
  have hCG : G C by split=> //; split=> //; exact: subset_trans hCB hBA.
  pose i : I := @exist (set T) (fun C => C \in G) C (mem_set hCG).
  have hgi : C (g i) := disjoint_selection_right_member hfg i.
  have [j _ he] := hCB _ hgi; exact: disjoint_selection_separated hfg j i he.
have hnoD C : closed C -> C `<=` A `\` B -> ~ (0 < mu C).
  move=> hC hCD hpos.
  have hCG : G C by split=> //; split=> // x hx; exact: (hCD x hx).1.
  pose i : I := @exist (set T) (fun C => C \in G) C (mem_set hCG).
  have hfi : C (f i) := disjoint_selection_left_member hfg i.
  apply: (hCD _ hfi).2; by exists i.
exists B; split=> // hB.
have hBf : mu B < +oo := le_lt_trans (@measure_mono R T mu hm B A hBA) hf.
have hDz : mu (A `\` B) = 0.
  apply: (@measurable_without_positive_closed_subset_null R T mu hm hr (A `\` B)).
  - exact: (@measure_measurable_difference R T mu hm A B hA hB).
  - apply: le_lt_trans (_ : mu (A `\` B) <= mu A) hf.
    apply: (@measure_mono R T mu hm)=> x [hx _]; exact hx.
  - exact hnoD.
have hBz := @measurable_without_positive_closed_subset_null R T mu hm hr B hB hBf hnoB.
have hcover : A `<=` B `|` (A `\` B).
  move=> x hx; case: (pselect (B x))=> hb; [by left|right; by split].
have hb := @measure_binary_cover R T mu hm A B (A `\` B) hcover.
rewrite hBz hDz add0e in hb; by have := lt_le_trans hp hb; rewrite ltxx.
Qed.
