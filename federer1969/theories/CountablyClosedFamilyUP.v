(** Federer (1969), 2.2.1, p. 60, two smallest-family constructions: closure
    under (2),(3), and under (2)',(3). The boolean parameter only selects
    whether the union law requires disjointness. Both classes contain the
    empty set, as follows from Federer's empty union. Source context:
    BorelFamilyUP.v. *)
From mathcomp Require Import all_boot boolp classical_sets cardinality.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [set_family_disjoint]: Federer 2.1.6, p. 58, definition used
    in 2.2.1(2)', p. 60: distinct members of a family have empty
    intersection. *)
Definition set_family_disjoint (I : choiceType) (G : set (set I)) :=
  forall A B, G A -> G B -> A <> B -> A `&` B = set0.

(** Source for [is_countably_closed_family]: Federer 2.2.1,
    p. 60, closure under countable unions and nonempty countable
    intersections. When disjoint_only is true, the union clause is
    the weaker (2)'; when false, it is (2). This common specification
    records both printed classes without assuming complement closure. *)
Record is_countably_closed_family (disjoint_only : bool) (I : choiceType)
    (X : set I) (F : set (set I)) := {
  countably_closed_family_empty : F set0;
  countably_closed_family_within : forall A, F A -> A `<=` X;
  countably_closed_family_union : forall G : set (set I),
    G `<=` F -> countable G -> (disjoint_only -> set_family_disjoint G) ->
    F (\bigcup_(A in G) A);
  countably_closed_family_intersection : forall G : set (set I),
    G `<=` F -> countable G -> (exists A, G A) -> F (\bigcap_(A in G) A)
}.

(** Source for [is_generated_closed_family]: Federer 2.2.1, p. 60: the
    smallest containing family satisfying the selected pair of closure
    clauses. This is an abstract specification, not an axiom. *)
Record is_generated_closed_family (disjoint_only : bool) (I : choiceType)
    (X : set I) (S F : set (set I)) := {
  generated_closed_family_laws : is_countably_closed_family disjoint_only X F;
  generated_closed_family_contains : S `<=` F;
  generated_closed_family_least : forall G,
    is_countably_closed_family disjoint_only X G -> S `<=` G -> F `<=` G
}.

(** Source for [generated_closed_family_unique]: Federer
    2.2.1, p. 60, supporting uniqueness of each smallest containing
    family. Mutual inclusion follows from the two minimality laws. *)
Lemma generated_closed_family_unique (d : bool) (I : choiceType)
    (X : set I) (S F G : set (set I)) :
  is_generated_closed_family d X S F -> is_generated_closed_family d X S G -> F = G.
Proof.
move=> hF hG; apply/seteqP; split.
- exact: (generated_closed_family_least hF (generated_closed_family_laws hG)
    (generated_closed_family_contains hG)).
- exact: (generated_closed_family_least hG (generated_closed_family_laws hF)
    (generated_closed_family_contains hF)).
Qed.
