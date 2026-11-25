(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order ssralg finmap.
From Federer Require Import Graded.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** The tensor algebra on a space with two independent generators is
    noncommutative. An extension to the free word algebra separates the words. *)
Section OrderedWords.
Variable K : fieldType.
Local Notation C := (Choice.clone bool _).
Local Notation V := (GRing.Lmodule.clone K (free_vector K C) _).
Local Notation A := (word_algebra K C).

(** Source for [letters]: Federer (1969), 1.2.3, p. 12, opening construction
    and multiplication paragraphs. In words: The tensor algebra is the
    direct sum of tensor powers, with degree zero equal to R and degree one
    equal to V; multiplication groups tensor factors, is associative, and
    has unit one. Local regression example for this passage; the example
    itself is not stated in the book. *)
Definition letters : {linear V -> A} := GRing.Linear.clone _ _ _ _
  (free_extend (fun b : bool => word_delta K [:: b])) _.

(** Source for [lettersE]: Federer (1969), 1.2.3, p. 12, opening
    construction and multiplication paragraphs. In words: The tensor algebra
    is the direct sum of tensor powers, with degree zero equal to R and
    degree one equal to V; multiplication groups tensor factors, is
    associative, and has unit one. Local regression example for this
    passage; the example itself is not stated in the book. *)
Lemma lettersE b : letters (delta K b) = word_delta K [:: b].
Proof. exact: free_extend_delta. Qed.

(** Source for [evaluate_pair]: Federer (1969), 1.2.3, p. 12, opening
    construction and multiplication paragraphs. In words: The tensor algebra
    is the direct sum of tensor powers, with degree zero equal to R and
    degree one equal to V; multiplication groups tensor factors, is
    associative, and has unit one. Local regression example for this
    passage; the example itself is not stated in the book. *)
Lemma evaluate_pair b c :
  word_eval letters [:: delta K b; delta K c] = word_delta K [:: b; c].
Proof.
change (alg_mul A (letters (delta K b))
  (alg_mul A (letters (delta K c)) (alg_one A)) = word_delta K [:: b; c]).
rewrite !lettersE.
change (word_mul (word_delta K [:: b])
  (word_mul (word_delta K [:: c]) (word_one K C)) = word_delta K [:: b; c]).
by rewrite word_unitr word_mulE.
Qed.

(** Source for [tensor_words_do_not_commute]: Federer (1969), 1.2.3, p. 12,
    opening construction and multiplication paragraphs. In words: The tensor
    algebra is the direct sum of tensor powers, with degree zero equal to R
    and degree one equal to V; multiplication groups tensor factors, is
    associative, and has unit one. Local regression example for this
    passage; the example itself is not stated in the book. *)
Example tensor_words_do_not_commute :
  tensor_word [:: delta K false; delta K true] !=
  tensor_word [:: delta K true; delta K false].
Proof.
apply/eqP=> h.
have e := congr1 (tensor_algebra_extension (A := A) letters) h.
have e0 := @tensor_algebra_extension_word K V A letters
  [:: delta K false; delta K true].
have e1 := @tensor_algebra_extension_word K V A letters
  [:: delta K true; delta K false].
have ew := eq_trans (esym (eq_trans e0 (evaluate_pair false true)))
  (eq_trans e (eq_trans e1 (evaluate_pair true false))).
have ec := congr1 (free_eval [:: false; true]) ew.
change (delta K [:: false; true] [:: false; true] =
  delta K [:: true; false] [:: false; true]) in ec.
rewrite !deltaE /= in ec.
by move/eqP: ec; rewrite oner_eq0.
Qed.

(** Source for [generator_is_faithful]: Federer (1969), 1.2.3, p. 12,
    opening construction and multiplication paragraphs. In words: The tensor
    algebra is the direct sum of tensor powers, with degree zero equal to R
    and degree one equal to V; multiplication groups tensor factors, is
    associative, and has unit one. Local regression example for this
    passage; the example itself is not stated in the book. *)
Example generator_is_faithful (u v : V) :
  tensor_generator u = tensor_generator v -> u = v.
Proof. exact: tensor_generator_injective. Qed.

(** Source for [degree_two_word]: Federer (1969), 1.2.3, p. 12, opening
    construction and multiplication paragraphs. In words: The tensor algebra
    is the direct sum of tensor powers, with degree zero equal to R and
    degree one equal to V; multiplication groups tensor factors, is
    associative, and has unit one. Local regression example for this
    passage; the example itself is not stated in the book. *)
Example degree_two_word (u v : V) :
  homogeneous (tensor_grading V) 2 (tensor_product (tensor_generator u) (tensor_generator v)).
Proof.
rewrite /tensor_generator tensor_product_words.
exact: (tensor_word_homogeneous [:: u; v]).
Qed.

(** Source for [unit_is_not_zero]: Federer (1969), 1.2.3, p. 12, opening
    construction and multiplication paragraphs. In words: The tensor algebra
    is the direct sum of tensor powers, with degree zero equal to R and
    degree one equal to V; multiplication groups tensor factors, is
    associative, and has unit one. Local regression example for this
    passage; the example itself is not stated in the book. *)
Example unit_is_not_zero : tensor_unit V != 0.
Proof. exact: tensor_unit_nonzero. Qed.
End OrderedWords.

(** Federer 1.2.1 and 1.2.3: boundaries of the actual component and
    grouping maps. In particular, an empty word represents the scalar unit. *)
Section TensorPowerBoundaries.
Variable K : fieldType.
Variable V : lmodType K.

(** Source for [tensor_empty_split]: Federer (1969), 1.2.3, p. 12, opening
    construction and multiplication paragraphs. In words: The tensor algebra
    is the direct sum of tensor powers, with degree zero equal to R and
    degree one equal to V; multiplication groups tensor factors, is
    associative, and has unit one. Local regression example for this
    passage; the example itself is not stated in the book. *)
Example tensor_empty_split :
  tensor_power_split V 0 0 (tensor_power_word 0 ([::] : seq V)) =
  tensor_inj (tensor_zeroth_inclusion V 1) (tensor_zeroth_inclusion V 1).
Proof.
rewrite tensor_power_splitE /tensor_split_word /=.
have he : tensor_power_word 0 ([::] : seq V) = tensor_zeroth_inclusion V 1.
  by rewrite /tensor_power_word /tensor_zeroth_inclusion /linear_comp /=
    /tensor_scalar scale1r.
by rewrite he.
Qed.

(** Source for [tensor_scalar_product]: Federer (1969), 1.2.3, p. 12,
    opening construction and multiplication paragraphs. In words: The tensor
    algebra is the direct sum of tensor powers, with degree zero equal to R
    and degree one equal to V; multiplication groups tensor factors, is
    associative, and has unit one. Local regression example for this
    passage; the example itself is not stated in the book. *)
Example tensor_scalar_product a b :
  component_val (tensor_power_join V 0 0
    (tensor_inj (tensor_zeroth_inclusion V a) (tensor_zeroth_inclusion V b))) =
  tensor_scalar V (a*b).
Proof.
rewrite tensor_power_joinE tensor_power_productE !tensor_zeroth_inclusionE.
rewrite /tensor_scalar (bilZl (tensor_product_bilinear V))
  (bilZr (tensor_product_bilinear V)) tensor_product_unitl scalerA.
by [].
Qed.

(** Source for [tensor_empty_left_block]: Federer (1969), 1.2.3, p. 12,
    opening construction and multiplication paragraphs. In words: The tensor
    algebra is the direct sum of tensor powers, with degree zero equal to R
    and degree one equal to V; multiplication groups tensor factors, is
    associative, and has unit one. Local regression example for this
    passage; the example itself is not stated in the book. *)
Example tensor_empty_left_block n (s : seq V) :
  tensor_power_split V 0 n (tensor_power_word (0+n) s) =
  tensor_inj (tensor_power_word 0 ([::] : seq V)) (tensor_power_word n s).
Proof. by rewrite tensor_power_splitE /tensor_split_word take0 drop0. Qed.

(** Source for [tensor_empty_right_block]: Federer (1969), 1.2.3, p. 12,
    opening construction and multiplication paragraphs. In words: The tensor
    algebra is the direct sum of tensor powers, with degree zero equal to R
    and degree one equal to V; multiplication groups tensor factors, is
    associative, and has unit one. Local regression example for this
    passage; the example itself is not stated in the book. *)
Example tensor_empty_right_block m (s : seq V) : size s = m ->
  tensor_power_split V m 0 (tensor_power_word (m+0) s) =
  tensor_inj (tensor_power_word m s) (tensor_power_word 0 ([::] : seq V)).
Proof.
move=> <-; rewrite tensor_power_splitE /tensor_split_word take_size.
by rewrite drop_oversize.
Qed.
End TensorPowerBoundaries.

Section ZeroDimensionalTensor.
Variable K : fieldType.
Local Notation Z := (GRing.Lmodule.clone K {ffun 'I_0 -> K^o} _).

(** Source for [empty_coordinate_zero]: Federer (1969), 1.2.3, p. 12,
    opening construction and multiplication paragraphs. In words: The tensor
    algebra is the direct sum of tensor powers, with degree zero equal to R
    and degree one equal to V; multiplication groups tensor factors, is
    associative, and has unit one. Local regression example for this
    passage; the example itself is not stated in the book. *)
Lemma empty_coordinate_zero (v : Z) : v = 0.
Proof. apply/ffunP=> i; by have := ltn_ord i; rewrite ltn0. Qed.

(** Source for [zero_space_positive_tensor_power]: Federer (1969), 1.2.3, p.
    12, opening construction and multiplication paragraphs. In words: The
    tensor algebra is the direct sum of tensor powers, with degree zero
    equal to R and degree one equal to V; multiplication groups tensor
    factors, is associative, and has unit one. Local regression example for
    this passage; the example itself is not stated in the book. *)
Example zero_space_positive_tensor_power n (x : tensor_power Z n.+1) : x = 0.
Proof.
move: x; apply: tensor_power_induction => [|x y -> ->|a x ->|s hs].
- by [].
- by rewrite add0r.
- by rewrite scaler0.
case: s hs => [|v s] hs; first by [].
apply/val_inj.
change (component_val (tensor_power_word n.+1 (v::s)) =
  component_val (0 : tensor_power Z n.+1)).
rewrite tensor_power_wordE hs eqxx linear0.
change (tensor_word ([:: v] ++ s) = 0).
rewrite -tensor_product_words.
change (tensor_product (tensor_generator v) (tensor_word s) = 0).
by rewrite (empty_coordinate_zero v) linear0 (bil0l (tensor_product_bilinear Z)).
Qed.

(** Source for [zero_space_scalar_survives]: Federer (1969), 1.2.3, p. 12,
    opening construction and multiplication paragraphs. In words: The tensor
    algebra is the direct sum of tensor powers, with degree zero equal to R
    and degree one equal to V; multiplication groups tensor factors, is
    associative, and has unit one. Local regression example for this
    passage; the example itself is not stated in the book. *)
Example zero_space_scalar_survives : tensor_zeroth_inclusion Z 1 != 0.
Proof.
apply/eqP=> he; have h := congr1 (tensor_zeroth_inverse Z) he.
rewrite tensor_zeroth_inclusionK linear0 in h.
by move/eqP: h; rewrite oner_eq0.
Qed.
End ZeroDimensionalTensor.

From Federer Require Import TensorUP Bilinear AlgebraUP GradedAlgebra
  GradedComponents FiniteCoordinates ScalarCoefficients SymmetricAlgebra
  SymmetricGrading SymmetricLowPowers SymmetricMaps SymmetricPowerFunctor.

(** Source for [symmetric_zero_ambient_empty_word]: Federer 1.9.1,
    p. 41, regression for the corrected degree-zero summand.
    Even when V=0, the empty product is nonzero and has degree zero. *)
Example symmetric_zero_ambient_empty_word (K : fieldType) :
  symmetric_word ([::] : seq (coordinate_space K 0)) != 0 /\
  symmetric_degree 0 (symmetric_word ([::] : seq (coordinate_space K 0))) =
    symmetric_word [::].
Proof.
split; first exact: symmetric_unit_nonzero.
by rewrite symmetric_degree_word /=.
Qed.

(** Source for [symmetric_zero_ambient_first_power]: Federer 1.9.1,
    p. 41, Sym_1(V)=V. Regression: the first symmetric power of
    the zero vector space is zero, whereas its zeroth power is not. *)
Example symmetric_zero_ambient_first_power (K : fieldType)
    (x : symmetric_power (coordinate_space K 0) 1) : x = 0.
Proof.
apply: val_inj; rewrite linear0.
have h := @symmetric_first_component K (coordinate_space K 0)
  (component_val x) (component_homogeneous x).
rewrite (coordinate_zero (symmetric_degree_one _ (component_val x))) linear0 in h.
exact: esym h.
Qed.

(** Source for [symmetric_repeated_generator_nonzero]: Federer 1.9.1,
    p. 41, the quotient imposes commutation, not vanishing squares.
    Regression over every field: the square of the generator of scalar
    one is nonzero, detected by the extension into the scalar algebra. *)
Example symmetric_repeated_generator_nonzero (K : fieldType) :
  symmetric_word [:: (1 : K^o); 1] != 0.
Proof.
pose ev := @symmetric_algebra_extension K K^o (scalar_algebra K)
  (linear_id K^o) (@mulrC K).
apply/eqP=> hz.
have h : ev (symmetric_word [:: (1 : K^o); 1]) = 1.
  by rewrite symmetric_algebra_extension_word /= !mulr1.
have h0 := congr1 ev hz.
rewrite linear0 h in h0.
by move: h0; apply/eqP; rewrite oner_eq0.
Qed.

(** Source for [symmetric_degree_zero_map_unit]: Federer 1.9.1,
    p. 42, the induced algebra map is unit-preserving. Regression:
    its degree-zero component fixes scalar one for every linear map. *)
Example symmetric_degree_zero_map_unit (K : fieldType) (V W : lmodType K)
    (f : {linear V -> W}) :
  symmetric_power_map f 0 (symmetric_zeroth_inclusion V 1) =
    symmetric_zeroth_inclusion W 1.
Proof.
apply: val_inj.
change (symmetric_algebra_map f (symmetric_degree 0 (symmetric_scalar V 1)) =
  symmetric_degree 0 (symmetric_scalar W 1)).
rewrite /symmetric_scalar !scale1r
  (@symmetric_unit_homogeneous K V) (@symmetric_unit_homogeneous K W).
exact: algebra_map_one.
Qed.

From Federer Require Import TensorUP FreeVector LinearBasis FiniteCoordinates
  SymmetricAlgebra SymmetricGrading SymmetricMultiIndices SymmetricIndexCardinality
  SymmetricLineBasis SymmetricZeroSpace SymmetricDimension.

(** Source for [symmetric_empty_index_regression]: Federer 1.9.2,
    p. 42, regression: the empty multiindex exists in degree zero
    and is absent in every positive degree. *)
Example symmetric_empty_index_regression m :
  #|{: symmetric_indices 0 0}| = 1%N /\
  #|{: symmetric_indices 0 m.+1}| = 0%N.
Proof. by split; rewrite card_symmetric_indices_zero. Qed.

(** Source for [symmetric_two_variable_quadratics]: Federer 1.9.2,
    p. 42, regression for the index count: two variables have
    exactly three quadratic monomials. *)
Example symmetric_two_variable_quadratics :
  #|{: symmetric_indices 2 2}| = 3%N.
Proof. by rewrite card_symmetric_indices. Qed.

(** Source for [symmetric_line_power_nonzero]: Federer 1.9.2,
    p. 42, regression: every power of the nonzero basis vector
    of a line is nonzero, including degrees above ambient dimension. *)
Example symmetric_line_power_nonzero (K : fieldType) m :
  symmetric_line_power K m != 0.
Proof.
apply/eqP=> hz.
have h := congr1 (symmetric_line_coordinates K) hz.
rewrite symmetric_line_coordinatesE linear0 in h.
have h1 := congr1 (fun c : free_vector K (Choice.clone nat _) => c m) h.
by rewrite deltaE eqxx free_zeroE in h1; move/eqP: h1; rewrite oner_eq0.
Qed.

(** Source for [symmetric_zero_space_second_power]: Federer
    1.9.2, p. 42, regression for the zero-dimensional boundary:
    its second symmetric power is zero. *)
Example symmetric_zero_space_second_power (K : fieldType)
    (x : symmetric_power (coordinate_space K 0) 2) : x = 0.
Proof. exact: (@zero_space_symmetric_power K (coordinate_space K 0) (@coordinate_zero K) 2 erefl x). Qed.

From Federer Require Import TensorUP SymmetricAlgebra SymmetricGrading
  SymmetricMultiIndices SymmetricIndexBounds SymmetricDividedMonomials
  SymmetricMultinomial SymmetricPolarizationCoefficients SymmetricPolarization.

(** Source for [symmetric_divided_power_zero_regression]: Federer
    1.9.3, p. 42, regression for the empty product extension:
    a divided zeroth power is the unit, including at the zero vector. *)
Example symmetric_divided_power_zero_regression (K : fieldType) (V : lmodType K) :
  symmetric_divided_vector_power (0 : V) 0 = symmetric_unit V.
Proof. by rewrite /symmetric_divided_vector_power /symmetric_vector_power /= invr1 scale1r. Qed.

(** Source for [symmetric_binary_linear_regression]: Federer
    1.9.3, p. 42, regression for the binomial formula in
    degree one, where no mixed higher-degree terms can occur. *)
Example symmetric_binary_linear_regression (K : fieldType) (V : lmodType K) (v w : V) :
  symmetric_divided_vector_power (v+w) 1 = symmetric_generator v + symmetric_generator w.
Proof.
by rewrite /symmetric_divided_vector_power /symmetric_vector_power
  symmetric_word_cons symmetric_product_unitr /= invr1 scale1r linearD.
Qed.

(** Source for [polarization_missing_coordinate_regression]:
    Federer 1.9.3, p. 43, regression for cancellation with
    a zero exponent: every positive-length all-zero tuple has
    zero polarization coefficient, even without characteristic zero. *)
Example polarization_missing_coordinate_regression (K : fieldType) m :
  polarization_coefficient K (symmetric_multi_zero m.+1) = 0.
Proof.
apply: (@polarization_coefficient_missing K m.+1 (symmetric_multi_zero m.+1) ord0).
by rewrite /symmetric_multi_zero ffunE.
Qed.

From Federer Require Import Graded FiniteCoordinates SymmetricAlgebra SymmetricGrading
  SymmetricDirectSum SymmetricDiagonal SymmetricDiagonalPowers SymmetricDividedMonomials.

(** Source for [symmetric_diagonal_empty_regression]: Federer
    1.9.4, p. 43, regression for the empty product in
    zero ambient dimension: the diagonal of one is one tensor one. *)
Example symmetric_diagonal_empty_regression (K : fieldType) :
  symmetric_diagonal (coordinate_space K 0) (symmetric_word [::]) =
    tensor_inj (symmetric_unit (coordinate_space K 0)) (symmetric_unit (coordinate_space K 0)).
Proof. exact: algebra_map_one. Qed.

(** Source for [symmetric_diagonal_zero_vector_regression]:
    Federer 1.9.4, p. 43, regression: inserting the zero
    vector as a positive-degree factor gives a zero diagonal. *)
Example symmetric_diagonal_zero_vector_regression (K : fieldType) (V : lmodType K) :
  symmetric_diagonal V (symmetric_vector_power (0 : V) 1) = 0.
Proof.
by rewrite /symmetric_vector_power symmetric_word_cons symmetric_word_nil
  symmetric_product_unitr !linear0.
Qed.

(** Source for [symmetric_diagonal_square_regression]: Federer
    1.9.4, p. 43, regression for a repeated generator:
    the mixed tensor term has coefficient two, as required by
    ordinary commutative multiplication. This holds over every field. *)
Example symmetric_diagonal_square_regression (K : fieldType) (V : lmodType K) (v : V) :
  symmetric_diagonal V (symmetric_vector_power v 2) =
    tensor_inj (symmetric_unit V) (symmetric_vector_power v 2) +
      (2%:R : K) *: tensor_inj (symmetric_generator v) (symmetric_generator v) +
      tensor_inj (symmetric_vector_power v 2) (symmetric_unit V).
Proof.
rewrite symmetric_diagonal_power_binomial !big_ord_recl big_ord0 /=.
rewrite /symmetric_vector_power !symmetric_word_cons symmetric_word_nil
  !symmetric_product_unitr !scale1r addr0 addrA.
by [].
Qed.

From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import TensorUP GradedComponents FiniteCoordinates
  SymmetricAlgebra SymmetricGrading SymmetricForms SymmetricFormWords
  SymmetricFormExtension SymmetricFormIsomorphism SymmetricFormZero
  SymmetricFormSum SymmetricPairing SymmetricFormDual.

(** Source for [symmetric_zero_ambient_constant_regression]:
    Federer 1.10.1, p. 44, degree-zero convention. Even when the
    input vector space is zero-dimensional, a zero-form can have
    the nonzero scalar value one on the empty tuple. *)
Example symmetric_zero_ambient_constant_regression (K : fieldType) :
  @zero_sform K (coordinate_space K 0) K^o (1 : K) [tuple] != 0.
Proof. by rewrite zero_sformE oner_eq0. Qed.

(** Source for [symmetric_zero_form_pullback_regression]:
    Federer 1.10.1, p. 44, degree-zero convention and induced map.
    Pullback preserves a coefficient independently of the map on inputs. *)
Example symmetric_zero_form_pullback_regression (K : fieldType)
    (V V' W : lmodType K) (f : {linear V -> V'}) (w : W) :
  S_m_dual f (zero_sform V' w) = zero_sform V w.
Proof. apply: sform_ext=> t; by rewrite S_m_dualE !zero_sformE. Qed.

(** Source for [symmetric_one_form_zero_argument_regression]:
    Federer 1.10.1, pp. 43-44, multilinearity in the defining
    actual tuple domain. A one-form evaluated on zero vanishes. *)
Example symmetric_one_form_zero_argument_regression (K : fieldType)
    (V W : lmodType K) (f : S_m V W 1) : f [tuple (0 : V)] = 0.
Proof.
rewrite -sform_wordsE -(sform_extensionE f).
change (sform_extension f (symmetric_word [:: (0 : V)]) = 0).
by rewrite symmetric_word_cons symmetric_word_nil symmetric_product_unitr !linear0.
Qed.

From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import Graded AlgebraUP Hom HomogeneousHom Convolution
  MixedTensorPairing MixedHomogeneousConvolution SymmetricAlgebra SymmetricGrading
  SymmetricMultiIndices SymmetricMonomials SymmetricDirectSum SymmetricDiagonal
  SymmetricForms SymmetricFormWords SymmetricFormExtension SymmetricFormIsomorphism
  SymmetricFormZero SymmetricFormSum SymmetricFormProduct SymmetricFormUnit
  SymmetricMixedProduct SymmetricDualMonomialProducts.

(** Source for [symmetric_constant_product_regression]: Federer
    1.10.2, pp. 44-45, multiplication and degree-zero convention.
    Multiplying two constant forms gives their coefficient product,
    including for a nonassociative coefficient multiplication. *)
Example symmetric_constant_product_regression (K : fieldType)
    (V W : lmodType K) (mu : W -> W -> W) (hmu : bilinear mu) (u v : W) :
  sform_product hmu (zero_sform V u) (zero_sform V v) = zero_sform V (mu u v).
Proof.
apply: sform_ext=> t; rewrite (tuple0 t) sform_productE symmetric_word_nil
  algebra_map_one paired_tensorE !sform_homogeneousE.
change (mu (sform_extension (zero_sform V u) (symmetric_unit V))
  (sform_extension (zero_sform V v) (symmetric_unit V)) = zero_sform V (mu u v) [tuple]).
rewrite -(symmetric_word_nil V) !sform_extensionE.
by rewrite !sform_wordsE !zero_sformE.
Qed.

(** Source for [symmetric_mixed_zero_regression]: Federer 1.10.2,
    p. 45, final paragraph. A zero form annihilates the mixed
    product even when the three coefficient spaces differ. *)
Example symmetric_mixed_zero_regression (K : fieldType)
    (V W1 W2 W3 : lmodType K) (mu : W1 -> W2 -> W3) (hmu : bilinear mu)
    p q (b : S_m V W2 q) : sform_mixed_product hmu (0 : S_m V W1 p) b = 0.
Proof. exact: (bil0l (@sform_mixed_product_bilinear K V W1 W2 W3 mu hmu p q) b). Qed.

(** Source for [symmetric_empty_dual_product_regression]: Federer
    1.10.2, p. 45, dual monomials in zero ambient dimension.
    The empty list of one-forms has product equal to the coefficient one. *)
Example symmetric_empty_dual_product_regression (K : fieldType) (V : lmodType K)
    (omega : 'I_0 -> S_m V K^o 1) :
  symmetric_one_form_monomial omega (symmetric_multi_zero 0) =
    @symmetric_coefficient_form K V K^o 1.
Proof.
by rewrite /symmetric_one_form_monomial /symmetric_one_form_word
  /symmetric_monomial_word enum_ord0.
Qed.

From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import Graded Hom HomogeneousHom SymmetricAlgebra
  SymmetricGrading SymmetricForms SymmetricFormWords SymmetricFormExtension
  SymmetricFormIsomorphism SymmetricPairing SymmetricRightInteriorHom
  SymmetricInteriorUP SymmetricRightInterior SymmetricLeftInteriorHom
  SymmetricLeftInteriorDegree SymmetricLeftInterior.

(** Source for [symmetric_right_zero_regression]: Federer 1.10.3,
    p. 45, the first bilinear operation. A zero symmetric vector
    contracts every coefficient-valued symmetric form to zero. *)
Example symmetric_right_zero_regression (K : fieldType) (V W : lmodType K)
    p q (hpq : (p<=q)%N) (f : S_m V W q) :
  symmetric_right_interior hpq (0 : symmetric_power V p) f = 0.
Proof. exact: (bil0l (@symmetric_right_interior_bilinear K V W p q hpq) f). Qed.

(** Source for [symmetric_left_zero_regression]: Federer 1.10.3,
    p. 45, the second bilinear operation. The zero covector
    contracts every symmetric vector to zero in the target component. *)
Example symmetric_left_zero_regression (K : fieldType) (V : lmodType K)
    p q (hpq : (p<=q)%N) (x : symmetric_power V q) :
  symmetric_left_interior hpq x (0 : S_m V K^o p) = 0.
Proof. exact: (bil0r (@symmetric_left_interior_bilinear K V p q hpq) x). Qed.

(** Source for [symmetric_right_empty_degree_regression]: Federer
    1.10.3, p. 45, the degree-zero boundary of the first
    characteristic pairing, including the empty symmetric product. *)
Example symmetric_right_empty_degree_regression (K : fieldType)
    (V W : lmodType K) (x y : symmetric_power V 0) (f : S_m V W 0) :
  symmetric_pairing x (symmetric_right_interior (leqnn 0) y f) =
    sform_homogeneous f (symmetric_product (component_val x) (component_val y)).
Proof. exact (@symmetric_right_interior_characteristic K V W 0 0 (leqnn 0) y f x). Qed.

From mathcomp Require Import all_boot all_order all_algebra.
From mathcomp.classical Require Import boolp functions.
From Federer Require Import FiniteCoordinates Graded Hom HomogeneousHom BoundedHom
  SymmetricAlgebra SymmetricGrading SymmetricDividedMonomials
  SymmetricForms SymmetricFormWords SymmetricFormExtension SymmetricFormIsomorphism
  SymmetricFormZero SymmetricFormSum HomogeneousPolynomialFunctions
  SymmetricPolynomialEvaluation SymmetricPolynomialInjectivity PolynomialFunctions
  PolynomialRepresentations PolynomialTaylorTransform PolynomialTaylor PolynomialTaylorDegree.

(** Source for [polynomial_zero_degree_regression]: Federer 1.10.4, p. 46,
    adjoining {0} in the degree definition gives zero, including in zero
    ambient dimension. This deliberately follows Federer. *)
Example polynomial_zero_degree_regression (K : fieldType)
    (h0 : [pchar K] =i pred0) :
  polynomial_degree (0 : PolynomialFunction (coordinate_space K 0) K^o) = 0%N.
Proof. exact: polynomial_degree_zero h0. Qed.

(** Source for [polynomial_zero_ambient_constant_regression]:
    Federer 1.10.4, pp. 45-46, a nonzero constant
    polynomial exists even on the zero-dimensional vector space.
    Its zero-form is evaluated on the empty product, which is the unit. *)
Example polynomial_zero_ambient_constant_regression (K : fieldType) :
  polynomial_from_forms (sform_include (@zero_sform K (coordinate_space K 0) K^o 1)) 0 = 1.
Proof.
rewrite polynomial_from_formsE symmetric_polynomial_value_include /sform_polynomial_value
  /symmetric_divided_vector_power /symmetric_vector_power /= invr1 scale1r.
change (sform_homogeneous (@zero_sform K (coordinate_space K 0) K^o 1)
  (symmetric_word [::]) = 1).
rewrite sform_homogeneousE sform_extensionE.
change (sform_words (@zero_sform K (coordinate_space K 0) K^o 1) [tuple] = 1).
by rewrite sform_wordsE zero_sformE.
Qed.

(** Source for [polynomial_zero_translation_regression]:
    Federer 1.10.4, pp. 46-47, translation of the
    zero polynomial has zero coefficients, including all zero-degree terms. *)
Example polynomial_zero_translation_regression (K : fieldType)
    (h0 : [pchar K] =i pred0) (V W : lmodType K) (x : V) :
  symmetric_taylor_transform (0 : S_star V W) x = 0.
Proof.
apply: (@symmetric_polynomial_injective K h0 V W); apply: funext=> v.
by rewrite (symmetric_taylor_transform_value h0) !linear0.
Qed.

(** Source for [polynomial_taylor_zero_degree_bound_regression]: Federer
    1.10.4, p. 46. Every Taylor coefficient of a polynomial of degree zero
    also has degree zero under Federer's convention. *)
Example polynomial_taylor_zero_degree_bound_regression (K : fieldType)
    (h0 : [pchar K] =i pred0) (V W : lmodType K)
    (P : PolynomialFunction V W) i : polynomial_degree P=0%N ->
  polynomial_degree (polynomial_taylor_coefficient_map P i) = 0%N.
Proof.
move=> hP; apply/eqP; rewrite -leqn0.
have h := polynomial_taylor_coefficient_degree h0 P i.
by move: h; rewrite hP sub0n.
Qed.

From mathcomp Require Import all_boot all_order all_algebra reals constructive_ereal.
From Federer Require Import FiniteCoordinates Graded ScalarCoefficients NonemptyProduct
  InnerProductUP InnerNorm SymmetricAlgebra SymmetricGrading SymmetricLowPowers
  SymmetricFormIsomorphism SymmetricForms SymmetricFormZero HomogeneousPolynomialFunctions
  RealNormUP SymmetricZeroDegreeDecomposition SymmetricOperatorNorm SymmetricOperatorBoundary
  SymmetricMass SymmetricMassConsequences SymmetricInnerNorm SymmetricInnerPurePowers
  SymmetricOneFormPowers SymmetricOneFormPowerNorm HilbertFormCompactness
  PolynomialNorm HilbertPolynomialNorm.

Import Order.TTheory Num.Theory.

(** Source for [symmetric_zero_degree_mass_boundary_regression]: Federer
    1.10.5, p. 48, local degree-zero clarification. The negative scalar unit
    has mass one, but no finite unweighted sum of empty products represents
    it. *)
Example symmetric_zero_degree_mass_boundary_regression (R : realType)
    (V : lmodType R) (N : V -> R) (hN : is_real_norm N) :
  symmetric_mass hN (symmetric_zeroth_inclusion V (-1))= 1 /\
  forall k, \sum_(i:'I_k) symmetric_word ([::]:seq V) != -symmetric_unit V.
Proof.
split.
- by rewrite symmetric_mass_degree_zero symmetric_zeroth_inclusionK normrN normr1.
- exact: symmetric_negative_unit_not_empty_sum.
Qed.

(** Source for [symmetric_constant_zero_ambient_norm_regression]:
    Federer 1.10.5, p. 47, the empty-tuple supremum.
    A nonzero constant zero-form has norm one even on the
    zero-dimensional input space. *)
Example symmetric_constant_zero_ambient_norm_regression (R : realType)
    (N : coordinate_space R 0 -> R) (hN : is_real_norm N) :
  (symmetric_operator_norm (W:=R^o) (proj1 hN) (fun r:R=>(`|r|)%R)
    (@zero_sform R (coordinate_space R 0) R^o (-1))= 1)%E.
Proof. by rewrite symmetric_operator_constant normrN normr1. Qed.

(** Source for [symmetric_square_mass_inner_norm_regression]:
    Federer 1.10.5, pp. 47-48, the distinction between
    the induced inner-product norm and the mass norm. The square of
    a unit vector has mass one and inner-product norm sqrt(2). *)
Example symmetric_square_mass_inner_norm_regression (R : realType)
    (V : lmodType R) (B : V -> V -> R) (hB : is_inner_product B)
    x (hx : inner_norm hB x= 1) :
  symmetric_mass (inner_norm_real_norm hB)
    (symmetric_tuple_component [tuple x | i<2])= 1 /\
  symmetric_inner_norm hB (symmetric_tuple_component [tuple x | i<2])=Num.sqrt (2:R).
Proof.
split.
- by rewrite (symmetric_mass_pure_power _ (isT : (0<2)%N)) hx expr1n.
- by rewrite symmetric_inner_pure_power_norm hx expr1n mulr1.
Qed.

(** Source for [symmetric_unbounded_one_form_square_regression]:
    Federer 1.10.5, p. 47, the exact power norm identity.
    An unbounded scalar one-form has an unbounded square; no implicit
    finite-dimensional or boundedness assumption may enter the proof. *)
Example symmetric_unbounded_one_form_square_regression (R : realType)
    (V : lmodType R) (N : V -> R) (hN : is_real_seminorm N)
    (f : S_m V R^o 1)
    (hf : symmetric_operator_norm (W:=R^o) hN (fun r:R=>(`|r|)%R) f= +oo%E) :
  symmetric_operator_norm (W:=R^o) hN (fun r:R=>(`|r|)%R)
    (symmetric_one_form_power (scalar_bilinear R) f 2)= +oo%E.
Proof.
have hsub (x y:R) : `|x*y|<=`|x|*`|y| by rewrite normrM.
have hp (w:R) : `|nonempty_product *%R 0 (nseq 2 w)|=`|w|^+2.
  by rewrite /= normrM expr2.
have hh := @symmetric_one_form_power_norm R V R^o N (fun r:R=>`|r|)
  hN (proj1 (scalar_absolute_value_norm R)) *%R (scalar_bilinear R) hsub f 2
  (isT : (0<2)%N) hp.
rewrite hh hf expe2 mulyy muleC gt0_mulye //; by rewrite lte_fin ltr0n fact_gt0.
Qed.

(** Source for [hilbert_constant_polynomial_norm_regression]:
    Federer 1.10.5, p. 48, the Hilbert equality in degree
    zero. The factorial and empty-product conventions retain the norm
    of a negative constant polynomial, including zero ambient dimension. *)
Example hilbert_constant_polynomial_norm_regression (R : realType)
    (V : lmodType R) (B : V -> V -> R) (hB : is_inner_product B) :
  polynomial_norm (W:=R^o) (proj1 (inner_norm_real_norm hB)) (fun r:R=>(`|r|)%R)
    (sform_polynomial_value (@zero_sform R V R^o (-1)))= 1%E.
Proof.
have hh := @hilbert_polynomial_norm_equality R V R^o B hB (fun r:R=>`|r|)
  (proj1 (scalar_absolute_value_norm R)) 0 (@zero_sform R V R^o (-1)).
by rewrite /= mul1e symmetric_operator_constant normrN normr1 in hh.
Qed.

From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InnerProductUP InnerNorm LinearBasis OrthonormalFamilies
  FiniteCoordinates SymmetricForms SymmetricFormZero SymmetricMultiIndices
  SymmetricIndexBounds SymmetricDividedMonomials SymmetricWordFibres SymmetricWordFibreCount
  SymmetricFormInner SymmetricFormWordSquares ScalarInnerProduct.

(** Source for [symmetric_empty_function_count_regression]: Federer 1.10.6,
    p. 49, the fibre-count formula includes the unique function
    from an empty set to an empty set. The empty factorial product is one. *)
Example symmetric_empty_function_count_regression (R : rcfType)
    (a : symmetric_indices 0 0) :
  #|[pred s : {ffun 'I_0 -> 'I_0} | symmetric_function_occurrences s == a]| = 1%N.
Proof.
by rewrite (symmetric_fibre_cardinality R a) fact0 /symmetric_multi_factorial big_ord0 divn1.
Qed.

(** Source for [symmetric_zero_form_hilbert_length_regression]: Federer
    1.10.6, p. 49, the Hilbert norm retains the coefficient
    length in degree zero, including zero input dimension. This checks
    both the factorial and the unique empty-function normalization. *)
Example symmetric_zero_form_hilbert_length_regression (R : rcfType)
    (V W : lmodType R) (B : V -> V -> R) (C : W -> W -> R)
    (hB : is_inner_product B) (hC : is_inner_product C)
    n (e : 'I_n -> V) (he : is_basis e) (ho : orthonormal_family B e) (w : W) :
  symmetric_form_norm hB hC he 0 (@zero_sform R V W w) = inner_norm hC w.
Proof.
have hs := @symmetric_form_norm_word_squares R V W B C hB hC n e he ho 0 (@zero_sform R V W w).
rewrite fact0 mul1r in hs.
have hv : (\sum_(s : {ffun 'I_0 -> 'I_n})
    (inner_norm hC ((@zero_sform R V W w) [tuple e (s i) | i<0]))^+2) = (inner_norm hC w)^+2.
  transitivity (\sum_(s : {ffun 'I_0 -> 'I_n}) (inner_norm hC w)^+2).
  - apply: eq_bigr=> s _; by rewrite zero_sformE.
  - by rewrite sumr_const card_ffun !card_ord expn0 mulr1n.
rewrite hv in hs.
apply: inner_norm_value; first exact: inner_norm_nonnegative.
rewrite -(@inner_norm_sqr R (S_m V W 0) _ (symmetric_form_inner_productP hB hC he 0)
  (@zero_sform R V W w)).
exact: esym hs.
Qed.

(** Source for [symmetric_zero_dimension_positive_length_regression]: Federer
    1.10.6, p. 49, a positive-degree form on a zero-dimensional
    domain has Hilbert length zero. The set of functions from a nonempty
    argument set to the empty basis set is empty, as the formula requires. *)
Example symmetric_zero_dimension_positive_length_regression (R : rcfType)
    (V W : lmodType R) (B : V -> V -> R) (C : W -> W -> R)
    (hB : is_inner_product B) (hC : is_inner_product C)
    (e : 'I_0 -> V) (he : is_basis e) (ho : orthonormal_family B e)
    m (hm : (0<m)%N) (f : S_m V W m) :
  symmetric_form_norm hB hC he m f = 0.
Proof.
have hs := @symmetric_form_norm_word_squares R V W B C hB hC 0 e he ho m f.
have hz : (\sum_(s : {ffun 'I_m -> 'I_0}) (inner_norm hC (f [tuple e (s i) | i<m]))^+2) = 0.
  apply: big1=> s _.
  have hi := ltn_ord (s (Ordinal hm)).
  by rewrite ltn0 in hi.
rewrite hz in hs.
have hf : ((m`!)%:R : R) != 0 by rewrite pnatr_eq0 -lt0n fact_gt0.
apply/eqP; rewrite -sqrf_eq0.
move/eqP: hs; by rewrite mulf_eq0 (negbTE hf) orFb.
Qed.
