(** Federer (1969), 3.4.8(4), p. 326:
    the exact original fixed-vector equations determine
    a unique subset. No group law is assumed here. *)
From mathcomp Require Import all_boot all_order boolp classical_sets.
From Federer Require Import PointwiseFixingLocusUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [pointwise_fixing_locus_exists]: existence
    of the sets specified in 3.4.8(4), p. 326. *)
Theorem pointwise_fixing_locus_exists (G X:Type) (action:G->X->X) n
  (e:'I_n->X) (J:set 'I_n):exists S,is_pointwise_fixing_locus action e J S.
Proof. exists [set g|forall i,J i ->action g (e i) = e i]=>g;by []. Qed.

(** Source for [pointwise_fixing_locus_unique]: the original
    membership equations determine the subset uniquely,
    3.4.8(4), p. 326. *)
Lemma pointwise_fixing_locus_unique (G X:Type) (action:G->X->X) n
  (e:'I_n->X) (J:set 'I_n) (S T:set G):
  is_pointwise_fixing_locus action e J S ->is_pointwise_fixing_locus action e J T ->S = T.
Proof. move=>hS hT;apply/seteqP;split=>g;[rewrite hS hT|rewrite hT hS];by []. Qed.
