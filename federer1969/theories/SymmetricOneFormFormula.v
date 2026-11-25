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
  MultipleShuffles PermutationArguments ShuffleComposition SingleBlockShuffle
  ShuffleSums MultipleShuffleBijection MultipleShuffleSums OneDegreeShuffles.
From Federer Require Import SymmetricFormFamily SymmetricFamilyArguments SymmetricIteratedShuffle.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

Section OneForms.
Variable K : fieldType.
Variables V W : lmodType K.
Variable mu : W -> W -> W.
Hypothesis hmu : bilinear mu.
Variable degrees : seq nat.
Hypothesis hone : all (pred1 1%N) degrees.
Variable alpha : symmetric_form_family V W degrees.

(** Source for [symmetric_one_family_values]: Federer 1.10.5, p. 47,
    supporting iterated shuffle calculation from 1.10.2, p. 45. In words:
    When all degrees are one, each factor receives its single permuted
    argument. *)
Definition symmetric_one_family_values (t : (sumn degrees).-tuple V) (sigma : 'S_(sumn degrees)) : seq W :=
  [seq sform_words (alpha i) [:: tnth t (sigma (cast_ord (one_degrees_sum hone) i))]
    | i <- enum 'I_(size degrees)].

(** Source for [symmetric_family_values_one]: Federer 1.10.5, p. 47,
    supporting iterated shuffle calculation from 1.10.2, p. 45. In words:
    The block-evaluation formula reduces to single-argument evaluations for
    one-forms. *)
Lemma symmetric_family_values_one t sigma : symmetric_family_values alpha t sigma = symmetric_one_family_values t sigma.
Proof. apply: eq_map => i; by rewrite (one_degree_argument hone). Qed.

(** Source for [symmetric_one_form_permutation_formula]: Federer 1.10.5, p.
    47, supporting iterated shuffle calculation from 1.10.2, p. 45. In
    words: Every permutation is a shuffle of singleton blocks, giving the
    unsigned permutation sum for products of one-forms. *)
Theorem symmetric_one_form_permutation_formula (t : (sumn degrees).-tuple V) : degrees != [::] ->
  symmetric_iterated_form hmu alpha t = \sum_(sigma : 'S_(sumn degrees))
    nonempty_product mu 0 (symmetric_one_family_values t sigma).
Proof.
move=> hd; rewrite symmetric_iterated_formE (symmetric_family_product_shuffle hmu alpha t hd).
under eq_bigr do rewrite /symmetric_multiple_shuffle_term symmetric_family_values_one.
rewrite -(sum_subtype (@multiple_shuffle_in degrees (sumn degrees))
  (fun sigma => nonempty_product mu 0 (symmetric_one_family_values t sigma))).
apply: eq_bigl => sigma; exact (@one_degrees_shuffle degrees hone (sumn degrees) sigma).
Qed.
End OneForms.
