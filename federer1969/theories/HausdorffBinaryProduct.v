(** Federer (1969), 2.5.20, p. 114: X times Y is Hausdorff when the compact
    metric factors are Hausdorff. This general topology lemma supports the
    closed-support and graph-image arguments. It uses the actual product
    topology and requires no additional metric structure on the product.
    Source context: CompactFunctionSpaceUP.v. *)
From mathcomp Require Import all_boot classical_sets topology.
From Federer Require Import TopologicalProductMaps.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [hausdorff_binary_product]: supporting general
    topology for the product and graph constructions in
    Federer 2.5.20, p. 114. Projections transfer any
    cluster relation to the two Hausdorff factors. *)
Lemma hausdorff_binary_product (X Y : topologicalType) :
  hausdorff_space X -> hausdorff_space Y -> hausdorff_space (X*Y)%type.
Proof.
move=> hX hY [a b] [c d] h.
have hac : a=c.
  apply: hX=> U V hU hV.
  have [z [hzU hzV]] := h (fst @^-1` U) (fst @^-1` V)
    (@first_projection_continuous X Y (a,b) U hU)
    (@first_projection_continuous X Y (c,d) V hV).
  by exists z.1.
have hbd : b=d.
  apply: hY=> U V hU hV.
  have [z [hzU hzV]] := h (snd @^-1` U) (snd @^-1` V)
    (@second_projection_continuous X Y (a,b) U hU)
    (@second_projection_continuous X Y (c,d) V hV).
  by exists z.2.
by rewrite hac hbd.
Qed.
