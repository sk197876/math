(** Federer (1969), 4.1.22, p. 379: integral polyhedral
    chains form an abelian group included in the actual current
    space. Give the carrier the same independent exact-image
    specification used for the existing real subspace carriers. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [is_additive_subgroup_representation]: an
    injective additive carrier whose image is exactly the
    prescribed original subgroup, supporting Federer 4.1.22,
    p. 379. No subtype construction is part of this law. *)
Record is_additive_subgroup_representation (V W:zmodType)
    (S:set V) (inc:{additive W->V}):Prop:={
  (** Source: subgroup inclusion is injective,
      supporting Federer 4.1.22, p. 379. *)
  additive_subgroup_representation_injective:injective inc;
  (** Source: every carrier member is in the original subgroup,
      supporting Federer 4.1.22, p. 379. *)
  additive_subgroup_representation_member:forall w,S (inc w);
  (** Source: every member of the original subgroup is included,
      supporting Federer 4.1.22, p. 379. *)
  additive_subgroup_representation_full:forall v,S v->exists w,inc w=v
}.
