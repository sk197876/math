(** Federer (1969), 2.10.8, p. 175: a nonnegative covering cost on Borel
    sets which is countably subadditive under coverings. The indexed version
    permits repeated cover members, as in the project's measure laws. This
    supports 2.10.10, p. 176, and the example of 2.5.10, p. 101. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import NonnegativeSum TopologicalBorel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [borel_metric_sets]: the family of all
    Borel subsets in Federer 2.10.8, p. 175,
    and 2.10.10, p. 176. Empty members are
    permitted, unlike the Hausdorff family of 2.10.2. *)
Definition borel_metric_sets (R : realType) (X : metricType R) : choiceType :=
  [the choiceType of set_type (@borel_set X)].

(** Source for [is_borel_cover_cost]: abstract nonnegativity
    and the displayed covering inequality of Federer 2.10.8,
    p. 175. The indexed formulation allows repetitions;
    the numerical-sum image inequality gives the equivalence
    with the book's countable family formulation. *)
Record is_borel_cover_cost (R : realType) (X : topologicalType)
    (c : set X -> \bar R) : Prop := {
  (** Source for [borel_cover_cost_nonnegative]: the
      nonnegative cost requirement inherited by 2.10.8,
      p. 175, from 2.10.1, pp. 169–170. *)
  borel_cover_cost_nonnegative : forall A, borel_set A -> 0<=c A;
  (** Source for [borel_cover_cost_cover]: the displayed
      covering inequality in Federer 2.10.8, p. 175,
      with an arbitrary countable index family. *)
  borel_cover_cost_cover : forall (J : choiceType) (D : set J)
    (S : J -> set X) A, countable D -> borel_set A ->
    (forall j, D j -> borel_set (S j)) ->
    A `<=` \bigcup_(j in D) S j -> c A<=nonnegative_sum D (fun j => c (S j))
}.
