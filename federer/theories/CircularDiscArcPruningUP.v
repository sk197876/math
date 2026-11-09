(** Federer (1969), 3.3.19, p. 305: independent
    recurrence of the original exceptional-stage families K_n.
    They remain local auxiliary families, not globally chosen
    parts of the original example. *)
From mathcomp Require Import all_boot all_order all_algebra finmap reals boolp classical_sets.
From Federer Require Import EuclideanInnerProduct InnerMetric FactorialDiscScalesSealed
  CircularDiscRefinement CircularDiscBadChildCount PartialFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Section Families.
Variable R:realType.
Local Notation E:=(inner_metric_space (@euclidean_inner_productP R 2)).

(** Source for [circular_disc_arc_pruned_step]: keep precisely
    the original children whose actual eta_n image meets the
    complement of the tested arc, as in K_n of 3.3.19,
    p. 305. Original centres and radii are unchanged. *)
Definition circular_disc_arc_pruned_step j (eta:partial_function E E)
    (F:{fset E}) (a b:R):{fset E}:=
  (\bigcup_(z<-F) [fset circular_disc_child_center z (@FactorialDiscScales.radius R j) k |
    k in @circular_disc_bad_child_indices R j eta z a b])%fset.

(** Source for [is_circular_disc_arc_pruning]: independent
    original K_v=G_v and child-selection recursion from
    3.3.19, p. 305. Mass decay, nullity and angular
    visitation are conclusions rather than specification fields. *)
Record is_circular_disc_arc_pruning (H:nat->{fset E})
    (eta:nat->partial_function E E) s (a b:R) (K:nat->{fset E}):Prop:={
  (** Source for [circular_arc_pruning_root]: the actual
      initial K_v=G_v in 3.3.19, p. 305. *)
  circular_arc_pruning_root:K 0%N=H s;
  (** Source for [circular_arc_pruning_step]: the actual
      exceptional child recursion in 3.3.19, p. 305. *)
  circular_arc_pruning_step:forall l,K l.+1=
    circular_disc_arc_pruned_step (s+l)%N (eta (s+l)%N) (K l) a b
}.
End Families.
