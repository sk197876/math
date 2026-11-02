(** Federer (1969), 2.2.1, pp. 59-60: Borel families relative to X,
    including all three printed closure conditions. Federer allows empty
    countable unions directly. *)
From mathcomp Require Import all_boot boolp classical_sets cardinality.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [is_borel_family]: Federer 2.2.1, pp. 59-60,
    definition, paraphrased: a family of subsets of X contains the
    empty set and is closed under relative complements, countable
    unions, and nonempty countable intersections. The redundant
    intersection law is retained to match all three printed clauses. *)
Record is_borel_family (I : choiceType) (X : set I) (F : set (set I)) := {
  borel_family_empty : F set0;
  borel_family_within : forall A, F A -> A `<=` X;
  borel_family_complement : forall A, F A -> F (X `\` A);
  borel_family_countable_union : forall G : set (set I),
    G `<=` F -> countable G -> F (\bigcup_(A in G) A);
  borel_family_countable_intersection : forall G : set (set I),
    G `<=` F -> countable G -> (exists A, G A) -> F (\bigcap_(A in G) A)
}.

(** Source for [is_generated_borel_family]: Federer 2.2.1,
    pp. 59-60, the smallest Borel family containing S. This
    universal specification records the Borel laws, containment of
    the generators, and inclusion in every other such family. *)
Record is_generated_borel_family (I : choiceType) (X : set I)
    (S F : set (set I)) := {
  generated_borel_family_laws : is_borel_family X F;
  generated_borel_family_contains : S `<=` F;
  generated_borel_family_least : forall G, is_borel_family X G -> S `<=` G -> F `<=` G
}.

(** Source for [generated_borel_family_unique]: Federer 2.2.1, pp. 59-60,
    supporting uniqueness of the smallest containing Borel family *)
Lemma generated_borel_family_unique (I : choiceType) (X : set I)
    (S F G : set (set I)) :
  is_generated_borel_family X S F -> is_generated_borel_family X S G -> F = G.
Proof.
move=> hF hG; apply/seteqP; split.
- exact: (generated_borel_family_least hF (generated_borel_family_laws hG)
    (generated_borel_family_contains hG)).
- exact: (generated_borel_family_least hG (generated_borel_family_laws hF)
    (generated_borel_family_contains hF)).
Qed.
