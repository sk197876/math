(** Supporting containing-generator proof for Federer (1969),
    2.10.19(3)–(5), p. 181. This is an additional supporting theorem, not a
    silent change to the numbered 2.10.18 statements. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import MetricDiameterUP MetricDiameter CoveringFamilyUP
  CountablyClosedFamilyUP DiametricRegularityUP DiameterWeightLaws WeightedCoverSelectionUP
  WeightedCoverSelection FiniteRemainderEnlargements DiameterEnlargements CaratheodoryWeakEnlargementUP.
From Federer Require Import WeakCaratheodoryDensityQuotient.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [weak_caratheodory_enlargement_selection_exists]: supporting
    weak-cost enlargement argument for 2.10.19(3)–(5), p. 181 Zero costs and
    the corrected covering quotient are explicit; the printed strict 2.10.18
    is unchanged. *)
Theorem weak_caratheodory_enlargement_selection_exists (R : realType) (X : metricType R)
    (F P : set (set X)) (c : set X -> \bar R) (E : set X -> set X)
    (k D : R) (B : set X) :
  is_weak_caratheodory_enlargement F c E k -> P `<=` F ->
  (forall S, P S -> closed S) -> (forall S, P S -> S<>set0) ->
  (forall S, P S -> extended_metric_diameter S<=D%:E) ->
  family_covers_finely P B -> exists G,
    G `<=` P /\ set_family_disjoint G /\
    forall H, finite_set H -> H `<=` G ->
      (B `\` \bigcup_(S in H) S) `<=` \bigcup_(S in G `\` H) E S.
Proof.
move=> hE hPF hclosed hne hD hf.
have hbounded S (hS : P S) : metric_set_bounded S := le_lt_trans (hD S hS) (@ltry R D).
have [d hd] := @real_diameter_weight_exists R X P hbounded.
have hn := @diameter_weight_nonnegative R X P d hd.
have hb : exists M : R, forall S, P S -> (d S<=M)%R.
  exists D=> S hS.
  have he := metric_diameter_unique (extended_metric_diameter_specification S) (hd S hS).
  have hh := hD S hS; by rewrite he lee_fin in hh.
have ht : (1<2 :> R)%R by rewrite ltr1n.
pose G := @weighted_cover_selection R X P d 2 hne hn hb ht.
have hG := @weighted_cover_selection_specification R X P d 2 hne hn hb ht.
exists G; split; first exact: weighted_selection_members hG.
split; first exact: weighted_selection_disjoint hG.
move=> H hH hHG x hx.
have [S [hS hnot] hxS] := @weighted_selection_finite_remainder_cover R X P d 2 G B
  hclosed hf hG H hH hHG x hx.
exists S; first by split.
have hSP : P S := weighted_selection_members hG hS.
apply: (@weak_enlargement_contains R X F c E k hE S (hPF S hSP) x).
exact: (@weighted_enlargement_diameter_subset R X P F d S hPF hd hSP x hxS).
Qed.
