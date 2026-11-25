(** Federer (1969), 1.6.5, pp. 25-26, supporting spanning
    argument for arbitrary basis pairs. The ambient basis indices
    are partitioned into missing, first-only, common, and second-only
    blocks. The adapted computation applies when the missing block
    is empty; otherwise its first dual form gives the checked zero
    case. This partition argument is not spelled out in the book. *)

From mathcomp Require Import all_boot all_order all_algebra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module BasisPairPartition.
Section Partition.
Variable I : finType.
Variables u v : seq I.
Hypotheses (hu : uniq u) (hv : uniq v).

(** Source for [missing]: Federer 1.6.5, pp. 25-26, supporting
    partition of basis pairs. Definition of the indices occurring in neither word. *)
Definition missing := filter (predC (mem u)) (filter (predC (mem v)) (enum I)).

(** Source for [first_only]: Federer 1.6.5, pp. 25-26, supporting
    partition of basis pairs. Definition of the indices occurring only in the first word. *)
Definition first_only := filter (mem u) (filter (predC (mem v)) (enum I)).

(** Source for [common]: Federer 1.6.5, pp. 25-26, supporting
    partition of basis pairs. Definition of the indices common to the two words. *)
Definition common := filter (mem u) (filter (mem v) (enum I)).

(** Source for [second_only]: Federer 1.6.5, pp. 25-26, supporting
    partition of basis pairs. Definition of the indices occurring only in the second word. *)
Definition second_only := filter (predC (mem u)) (filter (mem v) (enum I)).

(** Source for [all_indices]: Federer 1.6.5, pp. 25-26, supporting
    partition of basis pairs. Definition of the complete adapted ordering, with missing indices first. *)
Definition all_indices := missing ++ first_only ++ common ++ second_only.

(** Source for [missing_mem]: Federer 1.6.5, pp. 25-26, supporting
    partition of basis pairs. The membership condition for this block. *)
Lemma missing_mem i : (i \in missing) = (~~ (i \in u) && ~~ (i \in v)).
Proof. by rewrite /missing mem_filter mem_filter mem_enum andbT. Qed.

(** Source for [first_only_mem]: Federer 1.6.5, pp. 25-26, supporting
    partition of basis pairs. The membership condition for this block. *)
Lemma first_only_mem i : (i \in first_only) = ((i \in u) && ~~ (i \in v)).
Proof. by rewrite /first_only mem_filter mem_filter mem_enum andbT. Qed.

(** Source for [common_mem]: Federer 1.6.5, pp. 25-26, supporting
    partition of basis pairs. The membership condition for this block. *)
Lemma common_mem i : (i \in common) = ((i \in u) && (i \in v)).
Proof. by rewrite /common mem_filter mem_filter mem_enum andbT. Qed.

(** Source for [second_only_mem]: Federer 1.6.5, pp. 25-26, supporting
    partition of basis pairs. The membership condition for this block. *)
Lemma second_only_mem i : (i \in second_only) = (~~ (i \in u) && (i \in v)).
Proof. by rewrite /second_only mem_filter mem_filter mem_enum andbT. Qed.

(** Source for [filtered_first]: Federer 1.6.5, pp. 25-26, supporting
    partition of basis pairs. The first word is a permutation of the corresponding filtered ambient enumeration. *)
Lemma filtered_first : perm_eq (filter (mem u) (enum I)) u.
Proof.
apply: uniq_perm; [exact: filter_uniq (enum_uniq I)|exact: hu|].
by move=> i; rewrite mem_filter mem_enum andbT.
Qed.

(** Source for [filtered_second]: Federer 1.6.5, pp. 25-26, supporting
    partition of basis pairs. The second word is a permutation of its filtered ambient enumeration. *)
Lemma filtered_second : perm_eq (filter (mem v) (enum I)) v.
Proof.
apply: uniq_perm; [exact: filter_uniq (enum_uniq I)|exact: hv|].
by move=> i; rewrite mem_filter mem_enum andbT.
Qed.

(** Source for [missing_first_permutation]: Federer 1.6.5, pp. 25-26, supporting
    partition of basis pairs. The missing and first-only blocks exhaust the indices absent from the second word. *)
Lemma missing_first_permutation :
  perm_eq (missing ++ first_only) (filter (predC (mem v)) (enum I)).
Proof. by rewrite /missing /first_only perm_catC perm_filterC. Qed.

(** Source for [common_second_permutation]: Federer 1.6.5, pp. 25-26, supporting
    partition of basis pairs. The common and second-only blocks exhaust the second word. *)
Lemma common_second_permutation : perm_eq (common ++ second_only) v.
Proof. by rewrite /common /second_only perm_filterC; exact: filtered_second. Qed.

(** Source for [first_common_permutation]: Federer 1.6.5, pp. 25-26, supporting
    partition of basis pairs. The first-only and common blocks exhaust the first word. *)
Lemma first_common_permutation : perm_eq (first_only ++ common) u.
Proof.
have hp : perm_eq (filter (predC (mem v)) (enum I) ++ filter (mem v) (enum I)) (enum I).
  by rewrite perm_catC perm_filterC.
have h := perm_filter (mem u) hp.
rewrite filter_cat in h.
exact: perm_trans h filtered_first.
Qed.

(** Source for [all_indices_permutation]: Federer 1.6.5, pp. 25-26, supporting
    partition of basis pairs. The complete adapted ordering is a permutation of the ambient basis indices. *)
Lemma all_indices_permutation : perm_eq all_indices (enum I).
Proof.
have hp : perm_eq ((missing ++ first_only) ++ (common ++ second_only))
  (filter (predC (mem v)) (enum I) ++ filter (mem v) (enum I)).
  apply: perm_cat missing_first_permutation _.
  by rewrite /common /second_only perm_filterC.
have hq : perm_eq (filter (predC (mem v)) (enum I) ++ filter (mem v) (enum I)) (enum I).
  by rewrite perm_catC perm_filterC.
rewrite /all_indices catA; exact: perm_trans hp hq.
Qed.

(** Source for [all_indices_unique]: Federer 1.6.5, pp. 25-26, supporting
    partition of basis pairs. No basis index is repeated in the four blocks. *)
Lemma all_indices_unique : uniq all_indices.
Proof. rewrite (perm_uniq all_indices_permutation); exact: enum_uniq. Qed.

(** Source for [all_indices_cover]: Federer 1.6.5, pp. 25-26, supporting
    partition of basis pairs. Every ambient basis index occurs in one of the four blocks. *)
Lemma all_indices_cover i : i \in all_indices.
Proof. rewrite (perm_mem all_indices_permutation); exact: mem_enum. Qed.

(** Source for [first_common_unique]: Federer 1.6.5, pp. 25-26, supporting
    partition of basis pairs. The adapted first word has no repeated index. *)
Lemma first_common_unique : uniq (first_only ++ common).
Proof. by rewrite (perm_uniq first_common_permutation). Qed.

(** Source for [common_second_unique]: Federer 1.6.5, pp. 25-26, supporting
    partition of basis pairs. The adapted second word has no repeated index. *)
Lemma common_second_unique : uniq (common ++ second_only).
Proof. by rewrite (perm_uniq common_second_permutation). Qed.

End Partition.
End BasisPairPartition.
