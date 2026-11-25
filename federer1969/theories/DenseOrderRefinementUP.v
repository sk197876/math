(** Federer (1969), 2.3.2(2), p. 73: replacement of the rational thresholds
    by any dense subset. We specify a countable order-dense family lying
    inside that subset. The construction is private and downstream proofs
    use these laws. *)
From mathcomp Require Import all_boot all_order classical_sets topology.
From Federer Require Import CountableOrderIntervals.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [is_dense_order_refinement]: abstract supporting
    specification for the dense-subset replacement in Federer
    2.3.2(2), p. 73. It asserts membership and order
    density of a family with the prescribed index type. *)
Record is_dense_order_refinement disp (Y : orderType disp) (J : Type)
    (D : set Y) (e : J -> Y) : Prop := {
  (** Source for [dense_order_refinement_member]: the selected
      thresholds lie in the dense subset of Federer 2.3.2(2), p. 73. *)
  dense_order_refinement_member : forall j, D (e j);
  (** Source for [dense_order_refinement_dense]: the selected
      thresholds suffice for all interval tests in Federer 2.3.2(2), p. 73. *)
  dense_order_refinement_dense : is_order_dense_family e
}.
