(** Federer (1969), 2.2.10, p. 66, first paragraph: continuous inverse
    images of Suslin sets are Suslin. The closed witness is pulled back by
    (x,n) to (f(x),n). Source context: SuslinSetUP.v. *)
From mathcomp Require Import all_boot classical_sets reals topology.
From Federer Require Import SequenceSpace SuslinSetUP TopologicalProductMaps.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [continuous_preimage_suslin]: direct inverse-image
    assertion in Federer 2.2.10, p. 66: if f is continuous
    and S is Suslin, then f inverse of S is Suslin. Neither
    topology needs to be Hausdorff or metrizable for this claim. *)
Theorem continuous_preimage_suslin (R : realType) (X Y : topologicalType)
    (f : X -> Y) (S : set Y) :
  continuous f -> is_suslin_set R S -> is_suslin_set R (f @^-1` S).
Proof.
move=> hf [C [hC himg]].
pose F (p : X * positive_sequence_space R) := (f p.1,p.2).
exists (F @^-1` C); split.
- apply: (proj1 (continuous_closedP F) _ C hC).
  exact: first_factor_map_continuous hf.
- apply/seteqP; split.
  + move=> x [[y n] hc <-]; rewrite /= -himg.
    by exists (f y,n).
  + move=> x hx; rewrite /preimage -himg in hx.
    have [[y n] hc heq] := hx.
    exists (x,n)=> //; rewrite /preimage /F /= -heq; exact hc.
Qed.
