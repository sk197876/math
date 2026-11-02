(** Federer (1969), 1.10.5, p. 47: supporting permutation calculation for
    the inner product. This module connects the nonempty shuffle formula
    with ordinary unital products. *)
From mathcomp Require Import all_boot all_order all_algebra fingroup perm.
From Federer Require Import Hom BoundedHom Graded HomogeneousHom
  SymmetricAlgebra SymmetricGrading SymmetricForms SymmetricFormWords
  SymmetricFormExtension SymmetricFormSum SymmetricFormProduct SymmetricFormUnit
  ScalarCoefficients NonemptyProduct OneDegreeShuffles SymmetricFormFamily
  SymmetricFamilyArguments SymmetricIteratedShuffle SymmetricOneFormFormula.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [nonempty_product_foldr_unit]: Federer 1.10.5,
    p. 47, supporting product calculation. A nonempty right-associated
    product agrees with a fold whose final value is a right unit. *)
Lemma nonempty_product_foldr_unit (T : eqType) (mu : T -> T -> T)
    z u (hu : right_id u mu) xs : xs != [::] ->
  nonempty_product mu z xs = foldr mu u xs.
Proof.
elim: xs=> [|x xs ih] //; case: xs ih=> [|y ys] ih _.
- by rewrite /= hu.
- change (mu x (nonempty_product mu z (y::ys)) = mu x (foldr mu u (y::ys))).
  by rewrite ih.
Qed.

Section Uniform.
Variable K : fieldType.
Variable V : lmodType K.
Variable degrees : seq nat.
Hypothesis hone : all (pred1 1%N) degrees.
Variable omega : 'I_(size degrees) -> S_m V K^o 1.

(** Source for [uniform_symmetric_one_forms]: Federer 1.10.5,
    p. 47, supporting specialization of the symmetric product to
    one-forms. The component operation merely transports the equal degrees. *)
Definition uniform_symmetric_one_forms : symmetric_form_family V K^o degrees :=
  fun i => sform_component (nth 0%N degrees i) (sform_include (omega i)).

(** Source for [uniform_symmetric_one_forms_include]: Federer 1.10.5,
    p. 47, supporting specialization: including each transported
    one-form recovers the original included form. *)
Lemma uniform_symmetric_one_forms_include i :
  sform_include (uniform_symmetric_one_forms i) = sform_include (omega i).
Proof.
by rewrite /uniform_symmetric_one_forms (one_degrees_nth hone) sform_includeK.
Qed.

(** Source for [uniform_symmetric_one_forms_words]: Federer 1.10.5,
    p. 47, supporting specialization: the transported form has
    exactly the same word evaluation as the original one-form. *)
Lemma uniform_symmetric_one_forms_words i s :
  sform_words (uniform_symmetric_one_forms i) s = sform_words (omega i) s.
Proof.
by rewrite /uniform_symmetric_one_forms (one_degrees_nth hone) sform_includeK.
Qed.

(** Source for [uniform_symmetric_one_forms_list]: Federer 1.10.5,
    p. 47, supporting specialization: the ordered list of included
    forms is the ordinary list of the given one-forms. *)
Lemma uniform_symmetric_one_forms_list :
  symmetric_form_family_list uniform_symmetric_one_forms =
    [seq sform_include (omega i) | i <- enum 'I_(size degrees)].
Proof. apply: eq_map=> i; exact: uniform_symmetric_one_forms_include. Qed.

(** Source for [uniform_symmetric_one_forms_product]: Federer 1.10.5,
    p. 47, supporting specialization: the nonempty product in the
    shuffle formula agrees with the actual unital symmetric product. *)
Lemma uniform_symmetric_one_forms_product : degrees != [::] ->
  symmetric_family_product (scalar_bilinear K) uniform_symmetric_one_forms =
    foldr (symmetric_forms_product (scalar_bilinear K))
      (@symmetric_coefficient_form K V K^o 1)
      [seq sform_include (omega i) | i <- enum 'I_(size degrees)].
Proof.
move=> hd; rewrite /symmetric_family_product uniform_symmetric_one_forms_list.
apply: nonempty_product_foldr_unit.
- exact (@symmetric_forms_unit_right K V K^o (fun x y => x*y) (scalar_bilinear K) 1 (@mulr1 K)).
- by rewrite -size_eq0 size_map size_enum_ord size_eq0.
Qed.

(** Source for [uniform_symmetric_one_forms_formula]: Federer 1.10.5, p. 47,
    supporting permutation formula. Evaluate an actual nonempty product of
    one-forms by summing the products of their permuted values. *)
Theorem uniform_symmetric_one_forms_formula (t : (sumn degrees).-tuple V) :
  degrees != [::] ->
  (foldr (symmetric_forms_product (scalar_bilinear K))
      (@symmetric_coefficient_form K V K^o 1)
      [seq sform_include (omega i) | i <- enum 'I_(size degrees)])
        (symmetric_word t) =
    \sum_(sigma : 'S_(sumn degrees)) \prod_(i < size degrees)
      sform_words (omega i) [:: tnth t (sigma (cast_ord (one_degrees_sum hone) i))].
Proof.
move=> hd; rewrite -(uniform_symmetric_one_forms_product hd)
  -(symmetric_iterated_formE (scalar_bilinear K)).
rewrite (symmetric_one_form_permutation_formula (scalar_bilinear K) hone _ _ hd).
apply: eq_bigr=> sigma _.
rewrite /symmetric_one_family_values.
have he : [seq sform_words (uniform_symmetric_one_forms i)
    [:: tnth t (sigma (cast_ord (one_degrees_sum hone) i))]
    | i <- enum 'I_(size degrees)] =
  [seq sform_words (omega i)
    [:: tnth t (sigma (cast_ord (one_degrees_sum hone) i))]
    | i <- enum 'I_(size degrees)].
  apply: eq_map=> i; exact: uniform_symmetric_one_forms_words.
rewrite he (@nonempty_product_foldr_unit K *%R 0 1 (@mulr1 K)); last first.
  by rewrite -size_eq0 size_map size_enum_ord size_eq0.
by rewrite foldrE big_map big_enum.
Qed.

(** Source for [uniform_symmetric_one_forms_formula_degree]: Federer
    1.10.5, p. 47, supporting reindexing of the permutation formula.
    A proved equality of total degree changes only the tuple index bound. *)
Lemma uniform_symmetric_one_forms_formula_degree n (hn : sumn degrees = n)
    (t : n.-tuple V) : degrees != [::] ->
  (foldr (symmetric_forms_product (scalar_bilinear K))
      (@symmetric_coefficient_form K V K^o 1)
      [seq sform_include (omega i) | i <- enum 'I_(size degrees)])
        (symmetric_word t) =
    \sum_(sigma : 'S_n) \prod_(i < size degrees)
      sform_words (omega i)
        [:: tnth t (sigma (cast_ord (etrans (one_degrees_sum hone) hn) i))].
Proof.
case: n / hn in t *.
exact: uniform_symmetric_one_forms_formula.
Qed.
End Uniform.
