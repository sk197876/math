(** Federer (1969), 3.1.11, p. 223: the ordered
    coordinate derivative as evaluation of the symmetric differential. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom HomogeneousHom RealNormUP SymmetricAlgebra
  SymmetricForms SymmetricFormWords SymmetricFormExtension ContinuousMultilinearUP
  NormHigherDifferentialUP NormHigherSymmetricFormUP NormIteratedDirectionalUP
  NormHigherIteratedDirections IteratedDirectionalArguments MultilinearArgumentSequence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [norm_higher_form_iterated_directions]: the
    ordered derivative is the pairing with the reversed word,
    Federer 3.1.11, p. 223. This theorem does not assume
    a class-k neighbourhood, only differentiability of order k at a. *)
Theorem norm_higher_form_iterated_directions (R : realType)
    (X Y : lmodType R) (NX : X->R) (NY : Y->R)
    (hNX : is_real_norm NX) (hNY : is_real_norm NY)
    (Z : nat->lmodType R)
    (ev : forall i, {ffun 'I_i->X}->Hom (Z i) Y) (ZN : forall i, Z i->R)
    (hZ : forall i, is_continuous_multilinear_space NX NY (@ev i) (@ZN i))
    (A : X->Prop) (f : X->Y) k (s : seq X) a (phi : S_m X Y k) :
  size s=k -> is_norm_higher_differential_form NX ev ZN A f k a phi ->
  has_norm_iterated_directional NY A f s a
    (sform_homogeneous phi (symmetric_word (rev s))).
Proof.
move=>hs; subst k; move=>[z [hz he]].
have hh := @norm_higher_differential_iterated_directions R X Y NX NY hNX hNY
  Z ev ZN hZ A f s a z hz.
rewrite he in hh.
pose t := [tuple iterated_directional_arguments s i | i<size s].
have ht : (t : seq X)=rev s.
  change (multilinear_argument_sequence (iterated_directional_arguments s)=rev s).
  exact: iterated_directional_arguments_sequence.
rewrite -ht sform_homogeneousE sform_extensionE sform_wordsE.
exact hh.
Qed.
