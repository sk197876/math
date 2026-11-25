(** Federer (1969), 1.10.6, p. 49: m! times squared Hilbert length of a
    symmetric form equals the sum of squared evaluations over all functions
    from m argument positions to n orthonormal basis indices. The local
    proof groups words by their occurrence counts and uses the proved
    multinomial fibre count. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import Hom InnerProductUP InnerNorm Bilinear LinearBasis
  OrthonormalFamilies SymmetricAlgebra SymmetricGrading SymmetricMultiIndices
  SymmetricIndexBounds SymmetricDividedMonomials SymmetricMonomialBasis
  SymmetricNormalizedMonomials SymmetricForms SymmetricFormIsomorphism SymmetricPairing
  SymmetricFormInner SymmetricFormInnerCoordinates SymmetricWordFibres SymmetricWordFibreCount.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [symmetric_normalized_pairing_square]: Federer 1.10.6,
    p. 49, supporting normalization: squared length of an
    evaluation on e^alpha/sqrt(alpha!) is its unnormalized squared
    length divided by alpha!. *)
Lemma symmetric_normalized_pairing_square (R : rcfType) (V W : lmodType R)
    (C : W -> W -> R) (hC : is_inner_product C)
    n (e : 'I_n -> V) m (a : symmetric_indices n m) (f : S_m V W m) :
  (inner_norm hC (symmetric_pairing (symmetric_normalized_monomial e a) f))^+2 =
    ((symmetric_multi_factorial (symmetric_indices_unbound a))%:R : R)^-1 *
      (inner_norm hC (symmetric_pairing (symmetric_finite_monomial e a) f))^+2.
Proof.
rewrite /symmetric_normalized_monomial /symmetric_pairing linearZ.
change ((inner_norm hC ((symmetric_factorial_root R (symmetric_indices_unbound a))^-1 *:
  sform_to_hom f (symmetric_finite_monomial e a)))^+2 =
  ((symmetric_multi_factorial (symmetric_indices_unbound a))%:R : R)^-1 *
  (inner_norm hC (sform_to_hom f (symmetric_finite_monomial e a)))^+2).
by rewrite inner_normZ exprMn normfV
  (ger0_norm (ltW (symmetric_factorial_root_positive R (symmetric_indices_unbound a))))
  exprVn symmetric_factorial_root_square.
Qed.

(** Source for [symmetric_form_word_square_grouping]: Federer 1.10.6,
    p. 49, grouping the word evaluations by their exponent
    tuples gives the multiplicity m!/alpha! for each monomial.
    This algebraic grouping does not require an orthonormal basis. *)
Lemma symmetric_form_word_square_grouping (R : rcfType) (V W : lmodType R)
    (C : W -> W -> R) (hC : is_inner_product C)
    n (e : 'I_n -> V) m (f : S_m V W m) :
  (\sum_(s : {ffun 'I_m -> 'I_n}) (inner_norm hC (f [tuple e (s i) | i<m]))^+2) =
    \sum_(a : symmetric_indices n m)
      ((m`!)%:R * ((symmetric_multi_factorial (symmetric_indices_unbound a))%:R)^-1) *
        (inner_norm hC (symmetric_pairing (symmetric_finite_monomial e a) f))^+2.
Proof.
rewrite (partition_big (@symmetric_function_occurrences n m) predT) //.
apply: eq_bigr=> a _.
transitivity (\sum_(s : {ffun 'I_m -> 'I_n} | symmetric_function_occurrences s == a)
  (inner_norm hC (symmetric_pairing (symmetric_finite_monomial e a) f))^+2).
- apply: eq_bigr=> s /eqP hs.
  by rewrite -(symmetric_pairing_tuple _ f) symmetric_function_word_component hs.
- by rewrite sumr_const -[LHS]mulr_natl symmetric_fibre_cardinality_scalar.
Qed.

(** Source for [symmetric_form_norm_word_squares]: Federer 1.10.6,
    p. 49, the displayed function-indexed norm formula:
    m! |phi|^2 is the sum over all choices of basis vector in
    each argument of the squared output length. Zero degree and zero
    dimension are included, with the unique empty function when m=0. *)
Theorem symmetric_form_norm_word_squares (R : rcfType) (V W : lmodType R)
    (B : V -> V -> R) (C : W -> W -> R)
    (hB : is_inner_product B) (hC : is_inner_product C)
    n (e : 'I_n -> V) (he : is_basis e) (ho : orthonormal_family B e)
    m (f : S_m V W m) :
  (m`!)%:R * (symmetric_form_norm hB hC he m f)^+2 =
    \sum_(s : {ffun 'I_m -> 'I_n}) (inner_norm hC (f [tuple e (s i) | i<m]))^+2.
Proof.
rewrite (@symmetric_form_norm_square_sum R V W B C hB hC n e he n e he ho m f) symmetric_form_word_square_grouping mulr_sumr.
apply: eq_bigr=> a _.
by rewrite symmetric_normalized_pairing_square mulrA.
Qed.
