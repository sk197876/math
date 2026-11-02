(** Federer (1969), 2.10.1, p. 170, alternative open-cover characterisation.
    The local erratum, page 3, book p. 170 lines 24 and 35, changes [F11] to
    [F12]: Federer, On Lebesgue area (1955) Specify the printed refinement
    property without constructing a cover or a measure. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import NonnegativeSum.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [is_open_refinement_bound]: direct property
    of a threshold t in the alternative infimum in Federer
    2.10.1, p. 170, corrected reference Federer1955
    Theorem 2.5, pp. 291–292. Every open cover of A
    has a countable generator refinement covering A with
    total cost strictly below t. Repeated generator indices
    are handled by the established nonnegative-sum laws. *)
Definition is_open_refinement_bound (R : realType) (X : topologicalType)
    (J : choiceType) (S : J -> set X) (cost : J -> \bar R)
    (A : set X) (t : \bar R) := forall H : set (set X),
  (forall U, H U -> open U) -> A `<=` \bigcup_(U in H) U ->
  exists G : set J, countable G /\ A `<=` \bigcup_(j in G) S j /\
    (forall j, G j -> exists U, H U /\ S j `<=` U) /\ nonnegative_sum G cost<t.

(** Source for [open_refinement_bound_monotone_threshold]:
    supporting order consequence of the strict cost bound in
    Federer 2.10.1, p. 170. Increasing the threshold
    preserves the property, including an infinite threshold. *)
Lemma open_refinement_bound_monotone_threshold (R : realType) (X : topologicalType)
    (J : choiceType) (S : J -> set X) (cost : J -> \bar R)
    (A : set X) (t u : \bar R) :
  is_open_refinement_bound S cost A t -> t<=u -> is_open_refinement_bound S cost A u.
Proof.
move=> ht htu H hopen hcover.
have [G [hc [hG [href hb]]]] := ht H hopen hcover.
exists G; split=> //; split=> //; split=> //; exact: lt_le_trans hb htu.
Qed.
