(** Federer (1969), 2.5.10, p. 101: under CH, continuum admits a
    well-ordering whose proper initial segments are countable. We use the
    sealed small-prefix representative, already justified for 2.2.4, p. 62. *)
From mathcomp Require Import all_boot boolp classical_sets cardinality wochoice.
From Federer Require Import CardinalSuccessorUP SmallPrefixWellOrderUP SmallPrefixWellOrderSealed
  ContinuumHypothesisUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope card_scope.

(** Source for [continuum_countable_prefix_representative]:
    supporting well-ordering in Federer 2.5.10, p. 101.
    The carrier C represents the continuum by an equipollent
    subset of its power-set representative. CH forces every
    strictly smaller prefix to be countable. *)
Lemma continuum_countable_prefix_representative : continuum_hypothesis ->
  exists (C : set (set nat)) (r : rel (set nat)),
    well_order r /\ (@setT (set nat)) #<= C /\
    forall x, C x -> countable (well_order_prefix C r x).
Proof.
move=> [_ [_ hs]].
pose e := @SmallPrefixWellOrder.value [the choiceType of set nat] setT.
have h := @SmallPrefixWellOrder.laws [the choiceType of set nat] setT.
exists e.1, e.2; split; first exact: small_prefix_well_order_law h.
split; first exact: small_prefix_representative_cardinal h.
move=> x hx; apply: contrapT=> hn.
apply: (@small_prefix_strict_cardinal [the choiceType of set nat] _ _ _ h x hx).
apply: hs _ _ _ hn; exact: subset_card_le (fun y hy => Logic.I).
Qed.
