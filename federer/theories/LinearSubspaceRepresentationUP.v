(** Federer (1969), 4.1.1, pp. 344–345: independent carrier
    laws for the fixed-support and compactly supported subspaces.
    The existing algebraic subspace predicate is reused. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import Hom ModuleQuotient.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [is_linear_subspace_representation]: injective
    linear inclusion with exactly the prescribed image, supporting
    the spaces D_K(U,Y), D(U,Y) and the continuous duals in
    Federer 4.1.1, pp. 344–345. No carrier construction is imposed. *)
Record is_linear_subspace_representation (K:fieldType)
    (V W:lmodType K) (S:subspace V) (inc:Hom W V) : Prop := {
  (** Source for [subspace_representation_injective]: distinct
      members remain distinct under inclusion, supporting the
      subspaces of Federer 4.1.1, pp. 344–345. *)
  subspace_representation_injective : injective inc;
  (** Source for [subspace_representation_member]: inclusion
      takes values in the specified subspace, supporting Federer
      4.1.1, pp. 344–345. *)
  subspace_representation_member : forall w,S (inc w);
  (** Source for [subspace_representation_full]: every element
      of the specified subspace is represented, supporting Federer
      4.1.1, pp. 344–345. *)
  subspace_representation_full : forall v,S v -> exists w,inc w=v
}.
