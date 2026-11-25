(** Federer (1969), 3.4.12, p. 339:
    the actual commuting equations determine a unique
    subset, without assuming any topological group conclusion. *)
From mathcomp Require Import all_boot classical_sets.
From Federer Require Import PointwiseCommutingLocusUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [pointwise_commuting_locus_exists]: existence
    of the original complex-linear locus used in
    3.4.12, p. 339, specified only by
    its actual scalar-commutation equations. *)
Theorem pointwise_commuting_locus_exists (G X I:Type) (action:G->X->X) (P:I->X->X):
  exists S,is_pointwise_commuting_locus action P S.
Proof. exists [set g|forall i x,action g (P i x)= P i (action g x)]=>g;by []. Qed.

(** Source for [pointwise_commuting_locus_unique]: the original
    equations determine a unique locus, supporting 3.4.12,
    p. 339. *)
Theorem pointwise_commuting_locus_unique (G X I:Type) (action:G->X->X)
    (P:I->X->X) (S T:set G):
  is_pointwise_commuting_locus action P S ->is_pointwise_commuting_locus action P T ->S = T.
Proof.
move=>hS hT;apply/seteqP;split=>g;[rewrite hS hT|rewrite hT hS];by [].
Qed.
