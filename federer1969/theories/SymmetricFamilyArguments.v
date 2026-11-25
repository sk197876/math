(** Federer (1969), 1.10.5, p. 47, the shuffle argument for product norms;
    supporting iterated form of the binary formula in 1.10.2, p. 45. The
    unsigned formula uses ordered coefficient multiplication.
    Right-associated products let the proof work for any bilinear
    multiplication; in an associative algebra this is the unparenthesized
    product in the sources. Nonempty products do not require a coefficient
    unit. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra fingroup perm.
From Federer Require Import TensorUP Bilinear AlgebraUP Graded GradedComponents
  Hom HomogeneousHom BoundedHom SymmetricAlgebra SymmetricGrading
  SymmetricForms SymmetricFormWords SymmetricFormExtension SymmetricFormIsomorphism
  SymmetricFormSum SymmetricFormProduct SymmetricFormShuffle NonemptyProduct
  Shuffles AlternatingShuffle MultipleShuffles PermutationArguments ShuffleComposition SingleBlockShuffle
  MultipleShuffleBijection MultipleShuffleSums OneDegreeShuffles.
From Federer Require Import SymmetricFormFamily.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

Section FamilyArguments.
Variable K : fieldType.
Variables V W : lmodType K.

(** Source for [symmetric_family_values]: Federer 1.10.5, p. 47, supporting
    iterated shuffle calculation from 1.10.2, p. 45. In words: List the
    evaluations of the factors on their permuted argument blocks, in order. *)
Definition symmetric_family_values degrees (alpha : symmetric_form_family V W degrees) n
    (t : n.-tuple V) (sigma : 'S_n) : seq W :=
  [seq sform_words (alpha i) (block_arguments degrees i t sigma)
    | i <- enum 'I_(size degrees)].

(** Source for [symmetric_family_values_size]: Federer 1.10.5, p. 47,
    supporting iterated shuffle calculation from 1.10.2, p. 45. In words:
    The list of block evaluations retains the number of factors. *)
Lemma symmetric_family_values_size degrees (alpha : symmetric_form_family V W degrees) n (t : n.-tuple V) sigma :
  size (symmetric_family_values alpha t sigma) = size degrees.
Proof. by rewrite /symmetric_family_values size_map size_enum_ord. Qed.

(** Source for [symmetric_family_values_nonempty]: Federer 1.10.5, p. 47,
    supporting iterated shuffle calculation from 1.10.2, p. 45. In words:
    The block-evaluation list is nonempty for a nonempty family. *)
Lemma symmetric_family_values_nonempty degrees (alpha : symmetric_form_family V W degrees) n (t : n.-tuple V) sigma :
  degrees != [::] -> symmetric_family_values alpha t sigma != [::].
Proof. by rewrite -!size_eq0 symmetric_family_values_size. Qed.

(** Source for [symmetric_family_values_cons]: Federer 1.10.5, p. 47,
    supporting iterated shuffle calculation from 1.10.2, p. 45. In words:
    Composing block shuffles separates the first block evaluation from the
    tail. *)
Lemma symmetric_family_values_cons p ds (alpha : symmetric_form_family V W (p::ds))
    (t : (p+sumn ds).-tuple V) (tau : Sh p (sumn ds)) sigma :
  symmetric_family_values alpha t (shuffle_compose tau sigma) =
    symmetric_form_family_head alpha (shuffle_left_tuple t (val tau)) ::
    symmetric_family_values (symmetric_form_family_tail alpha) (shuffle_right_tuple t (val tau)) sigma.
Proof.
rewrite /symmetric_family_values enum_ordSl map_cons.
congr (_ :: _).
- rewrite block_arguments_head; exact: sform_wordsE.
- rewrite -(map_comp
    (fun i => sform_words (alpha i) (block_arguments (p::ds) i t (shuffle_compose tau sigma)))
    (lift ord0) (enum 'I_(size ds))).
  apply: eq_map => i; change (sform_words (symmetric_form_family_tail alpha i)
      (block_arguments (p::ds) i.+1 t (shuffle_compose tau sigma)) =
      sform_words (symmetric_form_family_tail alpha i) (block_arguments ds i (shuffle_right_tuple t (val tau)) sigma)).
  by rewrite block_arguments_tail.
Qed.

(** Source for [symmetric_family_values_single]: Federer 1.10.5, p. 47,
    supporting iterated shuffle calculation from 1.10.2, p. 45. In words: A
    single block and the identity permutation return the original form
    value. *)
Lemma symmetric_family_values_single p (alpha : symmetric_form_family V W [::p]) (t : (sumn [::p]).-tuple V) :
  symmetric_family_values alpha t 1%g = [:: sform_words (symmetric_form_family_head alpha) t].
Proof.
rewrite /symmetric_family_values enum_ordSl enum_ord0 /= /block_arguments /s /= drop0 permuted_values_identity.
congr [:: _]; congr (sform_words _ _); apply: take_oversize; by rewrite size_tuple /= addn0.
Qed.

(** Source for [symmetric_family_values_tuples]: Federer 1.10.5, p. 47,
    supporting iterated shuffle calculation from 1.10.2, p. 45. In words:
    The word-based block evaluations equal evaluations on the typed block
    tuples. *)
Lemma symmetric_family_values_tuples degrees (alpha : symmetric_form_family V W degrees)
    (t : (sumn degrees).-tuple V) sigma :
  symmetric_family_values alpha t sigma = [seq alpha i (block_tuple i t sigma) | i <- enum 'I_(size degrees)].
Proof.
apply: eq_map => i; exact (@sform_wordsE K V W (nth 0%N degrees i) (alpha i) (block_tuple i t sigma)).
Qed.
End FamilyArguments.
