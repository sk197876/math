(** Federer (1969), 2.10.1, p. 170, final paragraph: supporting topological
    specification for checking the proposed extension beyond metric spaces.
    This is elementary general topology, not a separate claim made in
    Federer. A two-point space has one open singleton and one point whose
    only open neighbourhood is the whole space. The local erratum corrects
    only the references on book p. 170, lines 24 and 35; it does not address
    this topological issue. *)
From mathcomp Require Import all_boot classical_sets topology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [is_two_point_open_topology]: abstract laws for
    a local counterexample to the arbitrary-topological-space
    remark in Federer 2.10.1, p. 170. The distinct points
    exhaust X and a subset is open precisely when containing
    the first point forces it to contain the second. This
    is a specification; existence is proved separately. *)
Definition is_two_point_open_topology (X : topologicalType) (p q : X) :=
  p<>q /\ (forall x : X, x=p \/ x=q) /\
  forall U : set X, open U <-> (U p -> U q).

(** Source for [two_point_first_neighbourhood_whole]: supporting
    consequence of the finite topology used to test Federer
    2.10.1, p. 170. Every open neighbourhood of the first
    point is the whole space; no separation axiom is presumed. *)
Lemma two_point_first_neighbourhood_whole (X : topologicalType) (p q : X)
    (U : set X) : is_two_point_open_topology p q -> open U -> U p -> U=setT.
Proof.
move=> [_ [hx ho]] hU hp.
have hq := (ho U).1 hU hp.
apply/seteqP; split=> x // _; have [->|->] := hx x; by [].
Qed.

(** Source for [two_point_second_singleton_open]: supporting
    proper open cover in the local test of Federer 2.10.1,
    p. 170. The second singleton is open and excludes the
    first point, so the printed A-cover quantifier sees it. *)
Lemma two_point_second_singleton_open (X : topologicalType) (p q : X) :
  is_two_point_open_topology p q -> open [set q].
Proof.
move=> [hne [_ ho]]; apply/(ho [set q])=> hp.
by exfalso; apply: hne.
Qed.
