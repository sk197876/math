(** Federer (1969), 3.4.8(5), p. 328:
    finite coefficient maps combine continuous operations
    with a common source. This is supporting general
    topology for the original compact-image argument. *)
From mathcomp Require Import all_boot boolp classical_sets topology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [continuous_common_domain_pair]: two
    continuous functions on the same source give a
    continuous pair, supporting the finite coefficient map
    in 3.4.8(5), p. 328. *)
Lemma continuous_common_domain_pair (T U V:topologicalType) (f:T->U) (g:T->V):
  continuous f ->continuous g ->continuous (fun x=>(f x,g x)).
Proof.
move=>hf hg x W [[A B] [hA hB] hW].
have hF:=hf x A hA;have hG:=hg x B hB.
change (nbhs x (fun y=>A (f y))) in hF.
change (nbhs x (fun y=>B (g y))) in hG.
have hBoth:=@filterI T (nbhs x) (nbhs_filter x) _ _ hF hG.
change (nbhs x (fun y=>W (f y,g y))).
apply:(@filterS T (nbhs x) (nbhs_filter x) _ _ _ hBoth)=>y [hyA hyB].
apply:hW;by split.
Qed.
