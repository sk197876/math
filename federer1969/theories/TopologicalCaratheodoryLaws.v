(** Consequences of the abstract corrected topological construction
    supporting Federer (1969), 2.10.1, p. 170. These arguments use only the
    supremum and refined-cover specifications. Source context, corrected
    reference and the necessary whole-space convention:
    TopologicalCaratheodoryUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import TopologicalCaratheodoryUP OpenRefiningEnvelopeUP
  OpenRefiningEnvelopeLaws OpenRefiningEnvelope.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [whole_space_singleton_open_cover]: supporting
    nonempty family of admissible covers for the corrected
    topological extension of Federer 2.10.1, p. 170. *)
Lemma whole_space_singleton_open_cover (X : topologicalType) :
  is_whole_space_open_cover [set (@setT X)].
Proof.
split; first by move=> U ->; exact: openT.
by move=> x _; exists setT.
Qed.

(** Source for [topological_caratheodory_unique]: supporting
    uniqueness from the supremum laws in the corrected
    topological version of Federer 2.10.1, p. 170. *)
Lemma topological_caratheodory_unique (R : realType) (X : topologicalType)
    (J : choiceType) (S : J -> set X) (cost : J -> \bar R)
    (mu xi : set X -> \bar R) :
  is_topological_caratheodory S cost mu -> is_topological_caratheodory S cost xi ->
  forall A, mu A=xi A.
Proof.
move=> hm hx A; apply/eqP; rewrite eq_le; apply/andP; split.
- apply: (topological_caratheodory_least hm)=> H nu hH hn.
  exact (@topological_caratheodory_upper R X J S cost xi hx A H nu hH hn).
- apply: (topological_caratheodory_least hx)=> H nu hH hn.
  exact (@topological_caratheodory_upper R X J S cost mu hm A H nu hH hn).
Qed.

(** Source for [topological_caratheodory_nonnegative]: supporting
    nonnegativity in the corrected topological measure assertion
    of Federer 2.10.1, p. 170. The one-member whole-space
    open cover supplies a nonnegative envelope below the supremum. *)
Lemma topological_caratheodory_nonnegative (R : realType) (X : topologicalType)
    (J : choiceType) (S : J -> set X) (cost : J -> \bar R)
    (mu : set X -> \bar R) :
  is_topological_caratheodory S cost mu -> forall A, 0<=mu A.
Proof.
move=> hm A.
have hn := open_refining_envelope_specification S cost [set (@setT X)].
apply: le_trans (open_refining_envelope_nonnegative hn A) _.
exact (@topological_caratheodory_upper R X J S cost mu hm A _ _
  (whole_space_singleton_open_cover X) hn).
Qed.

(** Source for [topological_caratheodory_add_bound]: supporting
    passage to the supremum after adding a fixed nonnegative
    extended value in the corrected topological extension of
    Federer 2.10.1, p. 170. Include infinite summands;
    no finite-measure restriction is imposed. *)
Lemma topological_caratheodory_add_bound (R : realType) (X : topologicalType)
    (J : choiceType) (S : J -> set X) (cost : J -> \bar R)
    (mu : set X -> \bar R) (A : set X) (z b : \bar R) :
  is_topological_caratheodory S cost mu -> 0<=z ->
  (forall H nu, is_whole_space_open_cover H -> is_open_refining_envelope S cost H nu -> nu A+z<=b) ->
  mu A+z<=b.
Proof.
move=> hm; case: z=> [r| |] hz hb; last by [].
- rewrite -leeBrDr //; apply: (topological_caratheodory_least hm)=> H nu hH hn.
  rewrite leeBrDr //; exact: hb H nu hH hn.
- have hn := open_refining_envelope_specification S cost [set (@setT X)].
  have hbase := hb _ _ (whole_space_singleton_open_cover X) hn.
  have hnon := open_refining_envelope_nonnegative hn A.
  have hi := leeD hnon (lexx (+oo : \bar R)); rewrite add0e in hi.
  exact: le_trans (leey _) (le_trans hi hbase).
Qed.
