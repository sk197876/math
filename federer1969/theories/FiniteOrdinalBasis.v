(** Federer (1969), 1.7.5, p. 33: supporting finite indexing for the
    polarity and its induced dual metric on an exterior power. Reindexing is
    bookkeeping, not a new assertion of the book. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import LinearBasis.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [finite_ordinal_basis]: Federer 1.7.5,
    p. 33, supporting transfer from a basis with finite index
    set I to a basis indexed by the ordinals below card(I). *)
Lemma finite_ordinal_basis (R : fieldType) (I : finType) (V : lmodType R)
    (e : I -> V) (he : is_basis e) :
  is_basis (fun i : 'I_#|I| => e (enum_val i)).
Proof.
exact (@basis_reindex R (Choice.clone I _) (Choice.clone 'I_#|I| _) V e he
  (@enum_rank I) (@enum_val I predT) (@enum_rankK I) (@enum_valK I)).
Qed.
