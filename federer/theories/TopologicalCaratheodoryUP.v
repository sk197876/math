(** Federer (1969), 2.10.1, p. 170, proposed topological version of the
    alternative construction. This specification uses the corrected
    quantifier over open covers of the whole space. The literal printed
    A-cover quantifier need not give a measure outside metric spaces; the
    sealed two-point counterexample is proved in
    OpenRefinementNonmonotonicity.v. The original metric construction
    satisfies both versions. The paper reference is [F12], Federer1955
    Theorem 2.5, pp. 291–292, by the local erratum p. 3, book p. 170 lines
    24 and 35. The whole-space convention is a local correction, not an
    entry in Federer's erratum. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import OpenRefiningEnvelopeUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [is_whole_space_open_cover]: corrected covering
    convention for the arbitrary-topological extension discussed
    in Federer 2.10.1, p. 170. Every point of X is covered;
    individual members are open. This is a proved necessary
    distinction from literal open covers only of the target A. *)
Definition is_whole_space_open_cover (X : topologicalType) (H : set (set X)) :=
  (forall U, H U -> open U) /\ setT `<=` \bigcup_(U in H) U.

(** Source for [is_topological_caratheodory]: abstract supremum
    specification of the corrected topological construction
    supporting Federer 2.10.1, p. 170. Take all whole-space
    open covers and all fixed-cover infima satisfying their
    abstract laws. Its equivalence with the strict-threshold
    infimum and its measure laws are proved separately. *)
Record is_topological_caratheodory (R : realType) (X : topologicalType)
    (J : choiceType) (S : J -> set X) (cost : J -> \bar R)
    (mu : set X -> \bar R) : Prop := {
  (** Source for [topological_caratheodory_upper]: every whole-
      space open-cover envelope is below the final supremum
      in the corrected extension of Federer 2.10.1, p. 170. *)
  topological_caratheodory_upper : forall A H nu, is_whole_space_open_cover H ->
    is_open_refining_envelope S cost H nu -> nu A<=mu A;
  (** Source for [topological_caratheodory_least]: least-upper-
      bound clause in the corrected topological extension of
      the alternative construction, Federer 2.10.1, p. 170. *)
  topological_caratheodory_least : forall A b,
    (forall H nu, is_whole_space_open_cover H -> is_open_refining_envelope S cost H nu -> nu A<=b) ->
    mu A<=b
}.
