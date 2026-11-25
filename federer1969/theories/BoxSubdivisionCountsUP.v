(** Federer (1969), 2.10.39, printed p. 199: choose counts k_i satisfying
    k_i/2<c_i/c_m<=k_i on the first m-1 axes, and leave all later axes
    unsplit. This supporting specification permits the weak upper count
    bound needed by the final non-strict inequality. Existence follows from
    the stronger strict scalar bracket in ScalarSubdivisionCount.v; no count
    or covering inequality is postulated as an axiom. Source context:
    ScalarSubdivisionCount.v. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [is_box_subdivision_counts]: supporting
    intrinsic integer-count laws for the first p=m-1
    subdivided axes in 2.10.39, p. 199.
    The remaining axes have one cell each. *)
Record is_box_subdivision_counts (R : realType) n (c : 'I_n -> R)
    (p : nat) (h : R) (count : 'I_n -> nat) : Prop := {
  (** Source for [box_subdivision_mesh_positive_law]: supporting
      positive mesh c_m for the initial box argument
      of 2.10.39, p. 199. Zero-width limits
      are handled separately from this positive-mesh law. *)
  box_subdivision_mesh_positive_law : 0<h;
  (** Source for [box_subdivision_count_positive_law]: direct
      positive integer choices in 2.10.39, p. 199. *)
  box_subdivision_count_positive_law : forall i, (0<count i)%N;
  (** Source for [box_subdivision_count_bracket_law]: supporting
      weak form of the integer bracket printed in
      2.10.39, p. 199, expressed without division. *)
  box_subdivision_count_bracket_law : forall i : 'I_n, (i<p)%N ->
    c i<=(count i)%:R*h /\ (count i)%:R*h<=2*c i;
  (** Source for [box_subdivision_unsplit_law]: supporting
      unchanged final axes of the small boxes in
      2.10.39, p. 199. *)
  box_subdivision_unsplit_law : forall i : 'I_n, (p<=i)%N -> count i= 1%N
}.
