(** Federer (1969), 3.2.39, p. 276: the
    first multiplicity layer is exactly the original image union. *)
From mathcomp Require Import all_boot classical_sets.
From Federer Require Import FiniteFamilyMultiplicity FiniteFamilyLayersUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [finite_family_layer_subset_union]: every
    positive layer lies in the image union in Federer
    3.2.39, pp. 275--276. *)
Lemma finite_family_layer_subset_union (X:Type) (I:finType) (K:I->set X)
    (S:'I_(#|I|)->set X):is_finite_family_layers K S ->
  forall j,S j `<=` \bigcup_i K i.
Proof.
move=>hS j y hy; apply:(finite_family_hit_count_positive K y).1.
exact:leq_ltn_trans (leq0n j) ((hS j y).1 hy).
Qed.

(** Source for [finite_family_zero_layer_union]: S_1=W
    in Federer 3.2.39, p. 276, with the printed
    positive layer represented by the zero ordinal. *)
Lemma finite_family_zero_layer_union (X:Type) (I:finType) (K:I->set X)
    (S:'I_(#|I|)->set X) (j0:'I_(#|I|)):
  is_finite_family_layers K S ->(j0:nat)=0%N ->S j0=\bigcup_i K i.
Proof.
move=>hS hZero; apply/seteqP; split=>y.
- move=>hy; apply:(finite_family_hit_count_positive K y).1.
  have h:=(hS j0 y).1 hy; by rewrite hZero in h.
- move=>hy; apply:(hS j0 y).2.
  rewrite hZero; exact:(finite_family_hit_count_positive K y).2 hy.
Qed.
