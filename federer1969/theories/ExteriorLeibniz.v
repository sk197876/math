(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order ssralg finfun finmap fingroup perm.
From Federer Require Import ExteriorBases Shuffles InversionCount.
From Federer Require Import ExteriorExpansion ExteriorPermutation ExteriorDeterminant.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Infrastructure for Federer 1.3.4: an injective self-map of a finite
    index set is a permutation, with no repeated terms in the reindexing. *)
(** Source for [sum_permutations]: Federer (1969), 1.3.4, p. 16, basis
    expansion and signed permutation formula. In words: Expanding the images
    of a basis in the top exterior power yields the determinant as the
    signed sum of products of coefficients, indexed by permutations.
    Supporting lemma for this passage; not separately stated in the book. *)
Lemma sum_permutations (Z : zmodType) (I : finType) (F : {ffun I -> I} -> Z) :
  \sum_(f : {ffun I -> I} | injectiveb f) F f =
    \sum_(sigma : {perm I}) F (val sigma).
Proof.
rewrite (reindex_omap (fun sigma : {perm I} => (val sigma : {ffun I -> I}))
  (insub : {ffun I -> I} -> option {perm I})).
- apply: eq_bigl => sigma.
  have hi : injectiveb (val sigma : {ffun I -> I}) := valP sigma.
  have hk : (insub (val sigma : {ffun I -> I}) : option {perm I}) = Some sigma := valK sigma.
  by rewrite hi hk eqxx.
- move=> f hf; by rewrite (insubT (fun f : {ffun I -> I} => injectiveb f) hf) /=.
Qed.

Section CoefficientExpansion.
Variable K : fieldType.
Variable n : nat.
Variable V : lmodType K.
Variable e : 'I_n -> V.
Variable a : 'I_n -> 'I_n -> K.

(** Federer 1.3.4, displayed expansion before substituting the index:
    only permutations survive the multilinear expansion. *)
(** Source for [exterior_permutation_expansion]: Federer (1969), 1.3.4, p.
    16, basis expansion and signed permutation formula. In words: Expanding
    the images of a basis in the top exterior power yields the determinant
    as the signed sum of products of coefficients, indexed by permutations.
    Formalises the indicated part of the passage under the hypotheses in the
    statement below. *)
Theorem exterior_permutation_expansion :
  exterior_word [seq \sum_(j < n) a i j *: e j | i <- enum 'I_n] =
    \sum_(sigma : 'S_n) (\prod_(i < n) a i (sigma i)) *:
      exterior_word [seq e (sigma i) | i <- enum 'I_n].
Proof.
rewrite exterior_word_expansion (bigID (fun f : {ffun 'I_n -> 'I_n} => injectiveb f)) /=.
have hz : (\sum_(f : {ffun 'I_n -> 'I_n} | ~~ injectiveb f)
    (\prod_(i < n) a i (f i)) *: exterior_word [seq e (f i) | i <- enum 'I_n]) = 0.
  apply: big1 => f hf.
  have hu : ~~ uniq [seq f i | i <- enum 'I_n] := hf.
  have hw := @exterior_word_map_nonuniq K V (Equality.clone 'I_n _) e
    [seq f i | i <- enum 'I_n] hu.
  rewrite -(map_comp e f (enum 'I_n)) in hw.
  by rewrite hw scaler0.
rewrite hz addr0 sum_permutations.
apply: eq_bigr => sigma _; by rewrite pvalE.
Qed.

(** Source for [exterior_permutation_word]: Federer (1969), 1.3.4, p. 16,
    basis expansion and signed permutation formula. In words: Expanding the
    images of a basis in the top exterior power yields the determinant as
    the signed sum of products of coefficients, indexed by permutations.
    Supporting lemma for this passage; not separately stated in the book. *)
Lemma exterior_permutation_word (sigma : 'S_n) :
  exterior_word [seq e (sigma i) | i <- enum 'I_n] =
    FedererPermutation.index K sigma *: exterior_word [seq e i | i <- enum 'I_n].
Proof.
rewrite (map_comp e sigma (enum 'I_n)); exact: exterior_word_permutation.
Qed.

(** Source for [e_lambda_permutation]: Federer (1969), 1.3.4, p. 16, basis
    expansion and signed permutation formula. In words: Expanding the images
    of a basis in the top exterior power yields the determinant as the
    signed sum of products of coefficients, indexed by permutations.
    Formalises the indicated part of the passage under the hypotheses in the
    statement below. *)
Lemma e_lambda_permutation (sigma : 'S_n) :
  e_lambda e (permutation_sequence sigma) =
    FedererPermutation.index K sigma *: e_lambda e (ord_tuple n).
Proof.
apply: val_inj; exact (@exterior_word_permutation K V n e sigma).
Qed.

(** Source for [exterior_Leibniz]: Federer (1969), 1.3.4, p. 16, basis
    expansion and signed permutation formula. In words: Expanding the images
    of a basis in the top exterior power yields the determinant as the
    signed sum of products of coefficients, indexed by permutations.
    Supporting lemma for this passage; not separately stated in the book. *)
Theorem exterior_Leibniz :
  exterior_word [seq \sum_(j < n) a i j *: e j | i <- enum 'I_n] =
    (\sum_(sigma : 'S_n) FedererPermutation.index K sigma *
      \prod_(i < n) a i (sigma i)) *: exterior_word [seq e i | i <- enum 'I_n].
Proof.
rewrite exterior_permutation_expansion scaler_suml.
apply: eq_bigr => sigma _; rewrite exterior_permutation_word scalerA.
congr (_ *: _); exact: mulrC.
Qed.
End CoefficientExpansion.

(** Source for [finite_free_extend]: Federer (1969), 1.3.4, p. 16, basis
    expansion and signed permutation formula. In words: Expanding the images
    of a basis in the top exterior power yields the determinant as the
    signed sum of products of coefficients, indexed by permutations.
    Supporting lemma for this passage; not separately stated in the book. *)
Lemma finite_free_extend (K : fieldType) (I : finType) (V : lmodType K)
    (e : I -> V) (c : free_vector K (Choice.clone I _)) :
  free_extend e c = \sum_(i : I) c i *: e i.
Proof.
rewrite /free_extend big_uniq; last exact: fset_uniq.
rewrite big_mkcond; apply: eq_bigr => i _.
case: ifP => hi; first by [].
have hni : i \notin finsupp c by rewrite hi.
by rewrite (fsfun_dflt hni) scale0r.
Qed.

Section DeterminantFormula.
Variable K : fieldType.
Hypothesis h2 : (1 + 1 : K) != 0.
Variable n : nat.
Variable V : lmodType K.
Variable e : 'I_n -> V.
Hypothesis he : is_basis e.
Variable f : {linear V -> V}.

(** Federer 1.3.4: the coefficients a_(i,j) are the coordinates of f(e_i).
    The formula below also accepts any family satisfying the displayed
    coefficient equation in the book. *)
(** Source for [a]: Federer (1969), 1.3.4, p. 16, basis expansion and signed
    permutation formula. In words: Expanding the images of a basis in the
    top exterior power yields the determinant as the signed sum of products
    of coefficients, indexed by permutations. Definition or construction
    used to formalise this passage. *)
Definition a i j : K := basis_coordinates he (f (e i)) j.

(** Source for [coefficientsE]: Federer (1969), 1.3.4, p. 16, basis
    expansion and signed permutation formula. In words: Expanding the images
    of a basis in the top exterior power yields the determinant as the
    signed sum of products of coefficients, indexed by permutations.
    Formalises the indicated part of the passage under the hypotheses in the
    statement below. *)
Lemma coefficientsE i : f (e i) = \sum_(j < n) a i j *: e j.
Proof.
rewrite -{1}[f (e i)](basis_coordinatesK he).
exact: finite_free_extend.
Qed.

(** Source for [top_map_word]: Federer (1969), 1.3.4, p. 16, basis expansion
    and signed permutation formula. In words: Expanding the images of a
    basis in the top exterior power yields the determinant as the signed sum
    of products of coefficients, indexed by permutations. Formalises the
    indicated part of the passage under the hypotheses in the statement
    below. *)
Lemma top_map_word : component_val (exterior_power_map f n (top_vector e)) =
  exterior_word [seq f (e i) | i <- enum 'I_n].
Proof.
change (exterior_algebra_map f (exterior_word [seq e i | i <- enum 'I_n]) =
  exterior_word [seq f (e i) | i <- enum 'I_n]).
by rewrite exterior_algebra_map_word -(map_comp f e (enum 'I_n)).
Qed.

(** Source for [top_map_expansion]: Federer (1969), 1.3.4, p. 16, basis
    expansion and signed permutation formula. In words: Expanding the images
    of a basis in the top exterior power yields the determinant as the
    signed sum of products of coefficients, indexed by permutations.
    Formalises the indicated part of the passage under the hypotheses in the
    statement below. *)
Lemma top_map_expansion : component_val (exterior_power_map f n (top_vector e)) =
  \sum_(sigma : 'S_n) (\prod_(i < n) a i (sigma i)) *:
    exterior_word [seq e (sigma i) | i <- enum 'I_n].
Proof.
rewrite top_map_word.
have hm := eq_map coefficientsE (enum 'I_n).
rewrite hm; exact: exterior_permutation_expansion.
Qed.

(** Source for [det_formula]: Federer (1969), 1.3.4, p. 16, basis expansion
    and signed permutation formula. In words: Expanding the images of a
    basis in the top exterior power yields the determinant as the signed sum
    of products of coefficients, indexed by permutations. Formalises the
    indicated part of the passage under the hypotheses in the statement
    below. *)
Theorem det_formula (b : 'I_n -> 'I_n -> K)
    (hb : forall i, f (e i) = \sum_(j < n) b i j *: e j) :
  det h2 he f = \sum_(sigma : 'S_n) FedererPermutation.index K sigma *
    \prod_(i < n) b i (sigma i).
Proof.
apply: (@top_scalar_injective K h2 n V e he).
rewrite -detE; apply: val_inj.
change (exterior_algebra_map f (exterior_word [seq e i | i <- enum 'I_n]) =
  (\sum_(sigma : 'S_n) FedererPermutation.index K sigma *
    \prod_(i < n) b i (sigma i)) *: exterior_word [seq e i | i <- enum 'I_n]).
rewrite exterior_algebra_map_word -(map_comp f e (enum 'I_n)).
have hm : [seq f (e i) | i <- enum 'I_n] =
    [seq \sum_(j < n) b i j *: e j | i <- enum 'I_n].
  exact (eq_map hb (enum 'I_n)).
rewrite hm; exact: exterior_Leibniz.
Qed.

(** Source for [det_coordinates]: Federer (1969), 1.3.4, p. 16, basis
    expansion and signed permutation formula. In words: Expanding the images
    of a basis in the top exterior power yields the determinant as the
    signed sum of products of coefficients, indexed by permutations.
    Formalises the indicated part of the passage under the hypotheses in the
    statement below. *)
Corollary det_coordinates :
  det h2 he f = \sum_(sigma : 'S_n) FedererPermutation.index K sigma *
    \prod_(i < n) a i (sigma i).
Proof. exact: det_formula coefficientsE. Qed.
End DeterminantFormula.
