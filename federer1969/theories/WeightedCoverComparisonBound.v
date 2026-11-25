(** Federer (1969), 2.9.15, pp. 160–161: the exceptional sets for
    centered-ball differentiation. The standing context of 2.9.1, p. 152,
    includes an existing phi Vitali relation. Supporting Federer 2.9.5.
    Erratum p. 3, book p. 161 line 11, corrects the later directional
    covering citation to 2.8.14. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology lra.
From Federer Require Import MeasureUP MeasureBasic MeasureDisjointSupport
  CountablyClosedFamilyUP WeightedCoverSelectionUP WeightedCoverSelection WeightedEnlargements
  BallCoverMeasureBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(** Source for [weighted_cover_comparison_bound]: supporting
    covering-to-mass estimate in the first proof case of
    Federer 2.9.15, p. 161. Apply 2.8.4–2.8.5 to
    nonempty bounded-weight members, prove the selected family
    countable from its disjoint positive reference masses inside
    finite-mass E, and sum the numerator bounds on their
    enlargements. The enlarged covering sets may overlap. *)
Lemma weighted_cover_comparison_bound (R : realType) (X : choiceType)
    (phi psi : set X -> \bar R) (T E : set X) (F : set (set X))
    (w : set X -> R) (tau c : R) :
  is_measure phi -> is_measure psi -> (1<tau)%R -> (0<=c)%R -> phi E< +oo ->
  (forall S, F S -> S<>set0) -> (forall S, F S -> (0<=w S)%R) ->
  (exists b, forall S, F S -> (w S<=b)%R) ->
  (forall S, F S -> S `<=` E) ->
  (forall S, F S -> measure_measurable phi S) ->
  (forall S, F S -> 0<phi S) -> T `<=` \bigcup_(S in F) S ->
  (forall S, F S -> psi (weighted_enlargement F w tau S)<=c%:E*phi S) ->
  psi T<=c%:E*phi E.
Proof.
move=> hphi hpsi ht hc hE hnonempty hwn hwb hFE hFm hpos hTF hhat.
pose G := @weighted_cover_selection R X F w tau hnonempty hwn hwb ht.
have hG := @weighted_cover_selection_specification R X F w tau hnonempty hwn hwb ht.
have hGF : G `<=` F := weighted_selection_members hG.
have hdis : set_family_disjoint G := weighted_selection_disjoint hG.
have hGE S : G S -> S `<=` E by move=> hS; exact: hFE S (hGF S hS).
have hGm S : G S -> measure_measurable phi S by move=> hS; exact: hFm S (hGF S hS).
have hcountpos := @measure_disjoint_positive_countable R X [the choiceType of set X]
  phi hphi E G idfun hE hGE hGm hdis.
have hcount : countable G.
  apply: sub_countable _ hcountpos; apply: subset_card_le=> S hS.
  split=> //; exact: hpos S (hGF S hS).
have hcover : T `<=` \bigcup_(S in G) weighted_enlargement F w tau S :=
  subset_trans hTF (@weighted_selection_enlargement_cover R X F w tau G hG).
exact: (@disjoint_reference_cover_measure_bound R X [the choiceType of set X]
  phi psi T E G idfun (weighted_enlargement F w tau) c hphi hpsi hc hcount
  hcover hGE hGm hdis (fun S hS => hhat S (hGF S hS))).
Qed.
