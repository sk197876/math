(** Federer (1969), 3.2.39, pp. 275--276: independent
    laws for the finite multiplicity layers S_1,...,S_v. *)
From mathcomp Require Import all_boot classical_sets.
From Federer Require Import FiniteFamilyMultiplicity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [is_finite_family_layers]: the definition of
    S_j in Federer 3.2.39, p. 275. The zero-based
    ordinal index represents the printed positive layer j+1.
    Existence is proved separately; no global family is chosen. *)
Definition is_finite_family_layers (X:Type) (I:finType)
    (K:I->set X) (S:'I_(#|I|)->set X):Prop:=
  forall (j:'I_(#|I|)) y,S j y <->(j<finite_family_hit_count K y)%N.

(** Source for [finite_family_layers_exist]: supporting local
    existence of the layer family defined in Federer 3.2.39,
    p. 275, including the empty original index family. *)
Lemma finite_family_layers_exist (X:Type) (I:finType) (K:I->set X):
  exists S,is_finite_family_layers K S.
Proof. exists (fun j=>[set y|(j<finite_family_hit_count K y)%N]); by move=>j y. Qed.

(** Source for [finite_family_layers_nested]: the nested
    positive layers used in Federer 3.2.39, p. 276. *)
Lemma finite_family_layers_nested (X:Type) (I:finType) (K:I->set X)
    (S:'I_(#|I|)->set X):is_finite_family_layers K S ->
  forall (j k:'I_(#|I|)),(j<=k)%N ->S k `<=` S j.
Proof.
move=>hS j k hjk y hy; apply:(hS j y).2.
exact:leq_ltn_trans hjk ((hS k y).1 hy).
Qed.
