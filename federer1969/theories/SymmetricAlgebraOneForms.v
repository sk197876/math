(** Federer (1969), 1.10.5, p. 47: supporting permutation calculation for
    the inner product. This module retains a general bilinear coefficient
    multiplication, without requiring a unit or commutativity. *)
From mathcomp Require Import all_boot all_order all_algebra fingroup perm.
From Federer Require Import TensorUP Bilinear Hom BoundedHom Graded HomogeneousHom
  SymmetricAlgebra SymmetricGrading SymmetricForms SymmetricFormWords
  SymmetricFormExtension SymmetricFormSum SymmetricFormProduct SymmetricFormUnit
  ScalarCoefficients NonemptyProduct OneDegreeShuffles SymmetricFormFamily
  SymmetricFamilyArguments SymmetricIteratedShuffle SymmetricOneFormFormula SymmetricOneFormProductFormula.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

Section Uniform.
Variable K : fieldType.
Variables V W : lmodType K.
Variable mu : W -> W -> W.
Hypothesis hmu : bilinear mu.
Variable degrees : seq nat.
Hypothesis hone : all (pred1 1%N) degrees.
Variable omega : 'I_(size degrees) -> S_m V W 1.

(** Source for [algebra_uniform_one_forms]: Federer 1.10.5,
    p. 47, supporting specialization of the symmetric product to
    one-forms. The component operation merely transports the equal degrees. *)
Definition algebra_uniform_one_forms : symmetric_form_family V W degrees :=
  fun i => sform_component (nth 0%N degrees i) (sform_include (omega i)).

(** Source for [algebra_uniform_one_forms_include]: Federer 1.10.5,
    p. 47, supporting specialization: including each transported
    one-form recovers the original included form. *)
Lemma algebra_uniform_one_forms_include i :
  sform_include (algebra_uniform_one_forms i) = sform_include (omega i).
Proof.
by rewrite /algebra_uniform_one_forms (one_degrees_nth hone) sform_includeK.
Qed.

(** Source for [algebra_uniform_one_forms_words]: Federer 1.10.5,
    p. 47, supporting specialization: the transported form has
    exactly the same word evaluation as the original one-form. *)
Lemma algebra_uniform_one_forms_words i s :
  sform_words (algebra_uniform_one_forms i) s = sform_words (omega i) s.
Proof.
by rewrite /algebra_uniform_one_forms (one_degrees_nth hone) sform_includeK.
Qed.

(** Source for [algebra_uniform_one_forms_list]: Federer 1.10.5,
    p. 47, supporting specialization: the ordered list of included
    forms is the ordinary list of the given one-forms. *)
Lemma algebra_uniform_one_forms_list :
  symmetric_form_family_list algebra_uniform_one_forms =
    [seq sform_include (omega i) | i <- enum 'I_(size degrees)].
Proof. apply: eq_map=> i; exact: algebra_uniform_one_forms_include. Qed.

(** Source for [algebra_uniform_one_forms_formula]: Federer 1.10.5,
    p. 47, supporting permutation formula for products of one-forms
    with values in a possibly nonunital algebra. Each summand is the
    ordered product of the permuted values. *)
Lemma algebra_uniform_one_forms_formula (t : (sumn degrees).-tuple V) :
  degrees != [::] ->
  (nonempty_product (symmetric_forms_product hmu) 0
      [seq sform_include (omega i) | i <- enum 'I_(size degrees)])
        (symmetric_word t) =
    \sum_(sigma : 'S_(sumn degrees)) nonempty_product mu 0
      [seq sform_words (omega i)
        [:: tnth t (sigma (cast_ord (one_degrees_sum hone) i))]
        | i <- enum 'I_(size degrees)].
Proof.
move=> hd.
have hf := @symmetric_one_form_permutation_formula K V W mu hmu
  degrees hone algebra_uniform_one_forms t hd.
rewrite symmetric_iterated_formE /symmetric_family_product
  algebra_uniform_one_forms_list in hf.
rewrite hf; apply: eq_bigr=> sigma _; congr (nonempty_product _ _ _).
apply: eq_map=> i; exact: algebra_uniform_one_forms_words.
Qed.

(** Source for [algebra_uniform_one_forms_formula_degree]: Federer
    1.10.5, p. 47, supporting transport to an explicitly equal
    total degree in the permutation formula. *)
Lemma algebra_uniform_one_forms_formula_degree n (hn : sumn degrees = n)
    (t : n.-tuple V) : degrees != [::] ->
  (nonempty_product (symmetric_forms_product hmu) 0
      [seq sform_include (omega i) | i <- enum 'I_(size degrees)])
        (symmetric_word t) =
    \sum_(sigma : 'S_n) nonempty_product mu 0
      [seq sform_words (omega i)
        [:: tnth t (sigma (cast_ord (etrans (one_degrees_sum hone) hn) i))]
        | i <- enum 'I_(size degrees)].
Proof. case: n / hn in t *; exact: algebra_uniform_one_forms_formula. Qed.
End Uniform.

(** Source for [algebra_one_form_product_permutations]: Federer
    1.10.5, p. 47, supporting evaluation of a nonempty product
    of m one-forms as the sum of their m! ordered permutation products.
    In an associative algebra the chosen parentheses are immaterial. *)
Theorem algebra_one_form_product_permutations (K : fieldType)
    (V W : lmodType K) (mu : W -> W -> W) (hmu : bilinear mu)
    m (omega : 'I_m -> S_m V W 1) (t : m.-tuple V) :
  (0<m)%N ->
  (nonempty_product (symmetric_forms_product hmu) 0
      [seq sform_include (omega i) | i <- enum 'I_m]) (symmetric_word t) =
    \sum_(sigma : 'S_m) nonempty_product mu 0
      [seq sform_words (omega i) [:: tnth t (sigma i)] | i <- enum 'I_m].
Proof.
move=> hm.
have hone : all (pred1 1%N) (nseq m 1%N) by rewrite all_nseq /= eqxx orbT.
have hn : sumn (nseq m 1%N) = m by rewrite sumn_nseq mul1n.
have hd : nseq m 1%N != [::] by rewrite -size_eq0 size_nseq -lt0n.
pose hs := size_nseq m 1%N.
have hf := @algebra_uniform_one_forms_formula_degree K V W mu hmu
  (nseq m 1%N) hone (fun i => omega (cast_ord hs i)) m hn t hd.
rewrite (ordinal_cast_enum_map hs (fun i => sform_include (omega i))) in hf.
rewrite hf; apply: eq_bigr=> sigma _; congr (nonempty_product _ _ _).
rewrite -(ordinal_cast_enum_map hs
  (fun i => sform_words (omega i) [:: tnth t (sigma i)])).
apply: eq_map=> i; congr (sform_words _ [:: tnth t (sigma _)]); exact: val_inj.
Qed.
