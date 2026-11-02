(** Federer (1969), 1.10.5, p. 48: supporting factorial upper bound for
    products of unit one-forms, using the shuffle formula of 1.10.2, p. 45.
    The family here need not be biorthogonal. *)
From mathcomp Require Import all_boot all_order all_algebra fingroup perm reals constructive_ereal.
From Federer Require Import Hom BoundedHom ScalarCoefficients SymmetricAlgebra SymmetricGrading
  SymmetricForms SymmetricFormWords SymmetricFormSum SymmetricFormProduct SymmetricFormUnit
  SymmetricOneFormProductFormula RealNormUP SymmetricOperatorNormUP SymmetricOperatorNorm.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [symmetric_one_form_product_form]: Federer 1.10.5,
    p. 48, supporting degree-m form corresponding to the actual
    symmetric product of m scalar one-forms. The empty product is
    the scalar coefficient one. *)
Definition symmetric_one_form_product_form (K : fieldType) (V : lmodType K)
    m (omega : 'I_m -> S_m V K^o 1) : S_m V K^o m :=
  sform_component m (foldr (symmetric_forms_product (scalar_bilinear K))
    (@symmetric_coefficient_form K V K^o 1)
    [seq sform_include (omega i) | i <- enum 'I_m]).

(** Source for [symmetric_one_form_product_form_permutations]:
    Federer 1.10.5, p. 48, supporting unsigned permutation
    formula for the product of one-forms. In degree zero the
    single empty permutation and empty product both give one. *)
Lemma symmetric_one_form_product_form_permutations (K : fieldType) (V : lmodType K)
    m (omega : 'I_m -> S_m V K^o 1) (t : m.-tuple V) :
  symmetric_one_form_product_form omega t =
    \sum_(sigma : 'S_m) \prod_(i<m) sform_words (omega i) [:: tnth t (sigma i)].
Proof.
rewrite /symmetric_one_form_product_form sform_componentE.
case: m omega t=> [omega t|m omega t].
- rewrite enum_ord0 /=.
  change (@symmetric_coefficient_form K V K^o 1 (symmetric_word t) =
    \sum_(sigma : 'S_0) \prod_(i<0) sform_words (omega i) [:: tnth t (sigma i)]).
  rewrite symmetric_coefficient_formE (tuple0 t) symmetric_word_nil
    symmetric_augmentation_unit scale1r.
  under eq_bigr do rewrite big_ord0.
  by rewrite sumr_const card_Sn /=.
- exact: symmetric_one_form_product_permutations.
Qed.

(** Source for [symmetric_one_form_words_singleton]: Federer
    1.10.5, p. 48, supporting compatibility of list and
    tuple evaluation in the product formula. *)
Lemma symmetric_one_form_words_singleton (K : fieldType) (V W : lmodType K)
    (f : S_m V W 1) x : sform_words f [::x] = f [tuple x].
Proof. exact: (sform_wordsE f [tuple x]). Qed.

(** Source for [symmetric_unit_one_form_product_bound]: Federer
    1.10.5, p. 48, the upper bound ||omega^alpha||<=m!,
    here for any m scalar one-forms of norms at most one.
    The empty product has norm one, and the ambient dimension
    need not be finite. *)
Theorem symmetric_unit_one_form_product_bound (R : realType) (V : lmodType R)
    (N : V -> R) (hN : is_real_seminorm N) m (omega : 'I_m -> S_m V R^o 1)
    (hw : forall i, (symmetric_operator_norm (W:=R^o) hN (fun r:R=>(`|r|)%R) (omega i)<=1)%E) :
  (symmetric_operator_norm (W:=R^o) hN (fun r:R=>(`|r|)%R)
    (symmetric_one_form_product_form omega) <= ((m`!)%:R : R)%:E)%E.
Proof.
apply: (proj2 (symmetric_operator_norm_bound (W:=R^o) hN (fun r:R=>`|r|)
  (symmetric_one_form_product_form omega) ((m`!)%:R:R)))=> t ht.
rewrite symmetric_one_form_product_form_permutations.
apply: le_trans (ler_norm_sum _ _ _) _.
have he : (\sum_(sigma : 'S_m) (1:R)) = (m`!)%:R by rewrite sumr_const card_Sn.
rewrite -he; apply: ler_sum=> sigma _; rewrite normr_prod.
have hp : (\prod_(i<m) (1:R)) = 1 by rewrite prodr_const expr1n.
rewrite -[X in _<=X]hp; apply: ler_prod=> i _; apply/andP; split; first exact: normr_ge0.
rewrite symmetric_one_form_words_singleton.
apply: (proj1 (symmetric_operator_norm_bound (W:=R^o) hN (fun r:R=>`|r|) (omega i) 1) (hw i)).
move=> j; rewrite ord1 tnth0; exact: ht.
Qed.
