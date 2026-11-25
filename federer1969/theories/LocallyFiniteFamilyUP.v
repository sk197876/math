(** General topology used in Federer (1969),
    3.1.13, p. 225: local finiteness
    is specified by neighborhoods meeting only
    finitely many indexed members. *)
From mathcomp Require Import all_boot finmap classical_sets cardinality topology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [is_locally_finite_family_on]:
    the locally finite refinement assertion in
    Federer 3.1.13, p. 225.
    Indices are restricted to I, and
    neighborhoods are required at points of U. *)
Definition is_locally_finite_family_on (X : topologicalType) (J : choiceType)
    (U : set X) (I : set J) (F : J->set X) :=
  forall x, U x -> exists V : set X,
    open V /\ V x /\ finite_set (I `&` [set i | exists y, V y /\ F i y]).

(** Source for [locally_finite_family_subsets]:
    shrinking indexed members preserves local
    finiteness, supporting the support assertion
    in Federer 3.1.13, p. 225. *)
Lemma locally_finite_family_subsets (X : topologicalType) (J : choiceType)
    (U : set X) (I : set J) (F G : J->set X) :
  (forall i, I i -> G i `<=` F i) ->
  is_locally_finite_family_on U I F ->
  is_locally_finite_family_on U I G.
Proof.
move=>hGF hf x hx; have [V [ho [hV hfin]]] := hf x hx.
exists V; split; first exact ho.
split; first exact hV.
apply: sub_finite_set _ hfin.
move=>i [hi [y [hy hGy]]]; split; first exact hi.
exists y; split; first exact hy.
exact: hGF i hi y hGy.
Qed.

(** Source for [locally_finite_family_domain_restriction]:
    local finiteness remains valid on a
    smaller target domain, supporting Federer
    3.1.13, p. 225. *)
Lemma locally_finite_family_domain_restriction (X : topologicalType) (J : choiceType)
    (U V : set X) (I : set J) (F : J->set X) :
  V `<=` U -> is_locally_finite_family_on U I F ->
  is_locally_finite_family_on V I F.
Proof. by move=>hVU hF x hx; exact: hF x (hVU x hx). Qed.
