(** Federer (1969), 2.10.1, p. 170: split an admissible
    refined cover when none of its generators can meet both
    target pieces. This is the alternative-cover counterpart
    of the displayed separated-set argument for size cutoffs.
    Independent coarse covers are retained for taking the two
    suprema in the corrected topological extension. Source
    editions and convention: TopologicalCaratheodoryUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal.
From Federer Require Import NonnegativeSum NonnegativeSumRestriction OpenRefiningEnvelopeUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [open_refining_envelope_separated_bound]:
    supporting split-cover inequality for the corrected
    topological measurability assertion in Federer 2.10.1,
    p. 170. The fine generators obey both coarse constraints
    and cannot meet A and B simultaneously; splitting by those
    meeting A gives covers of A and B with disjoint index sets. *)
Lemma open_refining_envelope_separated_bound (R : realType) (X J : choiceType)
    (S : J -> set X) (cost : J -> \bar R) (H K L : set (set X))
    (nu xi omega : set X -> \bar R) (A B T : set X) :
  is_open_refining_envelope S cost H nu -> is_open_refining_envelope S cost K xi ->
  is_open_refining_envelope S cost L omega -> (forall j, 0<=cost j) ->
  (forall j, generator_refines_cover S L j -> generator_refines_cover S H j) ->
  (forall j, generator_refines_cover S L j -> generator_refines_cover S K j) ->
  (forall j, generator_refines_cover S L j ->
    forall x, A x -> S j x -> forall y, B y -> S j y -> False) ->
  A `|` B `<=` T -> nu A+xi B<=omega T.
Proof.
move=> hn hx hw hc hLH hLK hsep hT.
apply: (open_refining_envelope_greatest hw)=> G hGc hr hcov.
pose P := [set j | exists x, A x /\ S j x].
have hGa : countable (G `&` P).
  apply: (sub_countable _ hGc); apply: subset_card_le=> j hj; exact: hj.1.
have hGb : countable (G `\` P).
  apply: (sub_countable _ hGc); apply: subset_card_le=> j hj; exact: hj.1.
have hAcover : A `<=` \bigcup_(j in G `&` P) S j.
  move=> x hAx; have [j hj hs] := hcov x (hT x (or_introl hAx)).
  exists j=> //; split=> //; by exists x.
have hBcover : B `<=` \bigcup_(j in G `\` P) S j.
  move=> y hBy; have [j hj hs] := hcov y (hT y (or_intror hBy)).
  exists j; last exact hs.
  split; first exact hj.
  move=> [x [hAx hsx]].
  exact: hsep j (hr j hj) x hAx hsx y hBy hs.
have hA := @open_refining_envelope_lower R X J S cost H nu hn A (G `&` P)
  hGa (fun j hj => hLH j (hr j hj.1)) hAcover.
have hB := @open_refining_envelope_lower R X J S cost K xi hx B (G `\` P)
  hGb (fun j hj => hLK j (hr j hj.1)) hBcover.
have hb := leeD hA hB.
by rewrite -(@nonnegative_sum_split R J G P cost (fun j _ => hc j)) in hb.
Qed.
