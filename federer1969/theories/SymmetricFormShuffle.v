(** Federer (1969), 1.10.2, p. 45: the unsigned shuffle formula for
    symmetric forms. The argument tuple infrastructure is shared with the
    project's alternating shuffle formula; no signs occur. *)
From mathcomp Require Import all_boot all_order ssralg fingroup perm.
From Federer Require Import Graded Hom HomogeneousHom Convolution ExteriorIndices
  Shuffles ShuffleSums AlternatingShuffle SymmetricAlgebra SymmetricGrading
  SymmetricDiagonal SymmetricShuffleFormula SymmetricForms SymmetricFormWords
  SymmetricFormExtension SymmetricFormIsomorphism SymmetricFormProduct.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section BinaryFormula.
Variable K : fieldType.
Variables V W : lmodType K.
Variable mu : W -> W -> W.
Hypothesis hmu : bilinear mu.
Variables p q : nat.
Variables (a : S_m V W p) (b : S_m V W q).
Local Notation A := (sform_homogeneous a).
Local Notation B := (sform_homogeneous b).
Local Notation T := (paired_tensor hmu A B).
(** Source for [paired_symmetric_shuffle_term]: Federer 1.10.2, p. 45,
    displayed shuffle formula. In words: Evaluating a shuffle summand gives the coefficient product of the two block evaluations, without a permutation sign. *)
Lemma paired_symmetric_shuffle_term s i n (sigma : 'S_n) :
  T (symmetric_shuffle_term_fun s i sigma) = mu (sform_words a [seq nth 0 s j | j <- take i (map val (permutation_sequence sigma))])
       (sform_words b [seq nth 0 s j | j <- drop i (map val (permutation_sequence sigma))]).
Proof.
rewrite /symmetric_shuffle_term_fun paired_tensorE !sform_homogeneousE !sform_extensionE.
by [].
Qed.
(** Source for [paired_symmetric_shuffle_wrong]: Federer 1.10.2, p. 45,
    displayed shuffle formula. In words: Supporting degree selection: the summand is zero unless the first block has the first form's degree. *)
Lemma paired_symmetric_shuffle_wrong s n (i : 'I_n.+1) (sigma : 'S_n) :
  (i : nat) != p -> T (symmetric_shuffle_term_fun s i sigma) = 0.
Proof.
move=> hi; rewrite paired_symmetric_shuffle_term.
have hs : size [seq nth 0 s j | j <- take i (map val (permutation_sequence sigma))] != p.
  have hin : (i <= n)%N by move: (ltn_ord i); rewrite ltnS.
  by rewrite size_map size_take_min size_map size_tuple (minn_idPl hin).
by rewrite (sform_words_wrong a hs) (bil0l hmu).
Qed.
(** Source for [sform_product_shuffle]: Federer 1.10.2, p. 45,
    displayed shuffle formula. In words: The displayed binary shuffle formula for the symmetric product of a p-form and a q-form, including empty blocks. *)
Theorem sform_product_shuffle (t : (p+q).-tuple V) :
  sform_product hmu a b t = \sum_(sigma : Sh p q)
    mu (a (shuffle_left_tuple t (val sigma))) (b (shuffle_right_tuple t (val sigma))).
Proof.
rewrite sform_productE symmetric_diagonal_shuffle_frame linear_sum.
under eq_bigr do rewrite linear_sum.
rewrite size_tuple.
have hp : (p < (p+q).+1)%N by rewrite ltnS leq_addr.
pose ip : 'I_(p+q).+1 := Ordinal hp.
rewrite (bigD1 ip) //=.
have hz : (\sum_(i : 'I_(p+q).+1 | i != ip)
    \sum_(sigma : {sigma : 'S_(p+q) | shuffle_in i sigma})
      T (symmetric_shuffle_term_fun t i (val sigma))) = 0.
  apply: big1 => i hi; apply: big1 => sigma _.
  apply: paired_symmetric_shuffle_wrong; by move: hi; rewrite -val_eqE.
rewrite hz addr0; apply: eq_bigr => sigma _; rewrite paired_symmetric_shuffle_term.
change (mu (sform_words a (shuffle_left_tuple t (val sigma)))
       (sform_words b (shuffle_right_tuple t (val sigma))) =
  mu (a (shuffle_left_tuple t (val sigma))) (b (shuffle_right_tuple t (val sigma)))).
by rewrite !sform_wordsE.
Qed.
End BinaryFormula.
