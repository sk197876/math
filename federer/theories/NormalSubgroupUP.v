(** Federer (1969), 2.7.12, printed p. 129: "In particular, this equation
    holds whenever S is normal". Federer uses the normal subgroups of G
    without definition. A subgroup S of G is normal when g s g^{-1} belongs
    to S whenever g in G and s in S. The predicate is stated for the group
    structure of TopologicalGroupUP.v. *)
From mathcomp Require Import all_boot boolp classical_sets topology.
From Federer Require Import TopologicalGroupUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [is_normal_subgroup]: "whenever S is normal", Federer
    2.7.12, p. 129. Definition: S is a subgroup, and g s g^{-1} belongs
    to S whenever g in G and s in S. *)
Record is_normal_subgroup (G : Type) (mul : G -> G -> G) (inv : G -> G) (e : G) (S : set G) : Prop := {
  (** Source for [normal_subgroup_subgroup]: S is a subgroup of G,
      Federer 2.7.12, p. 129. *)
  normal_subgroup_subgroup : is_subgroup mul inv e S;
  (** Source for [normal_subgroup_conjugate]: g s g^{-1} belongs to S
      whenever g in G and s in S, Federer 2.7.12, p. 129. *)
  normal_subgroup_conjugate : forall g s, S s -> S (mul (mul g s) (inv g))
}.
