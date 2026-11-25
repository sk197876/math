(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra finmap.
From Federer Require Import AlternatingCoordinates.
From Federer Require Import OneFormIdentification.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Federer 1.4.4: the unit-preserving homomorphism Omega, constructed
    by the universal mapping property of 1.3.1. The coefficient-valued
    variant below assumes commutativity; the printed parenthesis omits
    this necessary hypothesis. The scalar-valued assertion is unchanged. *)
Section CommutativeCoefficients.
Variable K : fieldType.
Hypothesis h2 : (1+1 : K) != 0.
Variable V : lmodType K.
Variable W : algebra K.
Hypothesis hcomm : commutative (alg_mul W).
Local Notation A := (alternating_unital_algebra h2 V W).
Local Notation G := (A_star_grading V W).
Local Notation f := (GRing.Linear.clone _ _ _ _ (@one_generator K V W) _).
(** Source for [one_generator_square_zero]: Federer (1969), 1.4.4, p. 20,
    first assertion of the coefficient-algebra parenthesis, with corrected
    hypothesis. In words: For commutative associative unital coefficients,
    the identity from linear maps to one-forms extends uniquely to a
    unit-preserving exterior-to-alternating homomorphism. Supporting result
    for the corrected coefficient statement; not an assertion of the printed
    book. Commutativity is required here: the printed assertion for
    arbitrary associative unital coefficients is false. *)
Lemma one_generator_square_zero a : alg_mul A (f a) (f a) = 0.
Proof.
exact (@degree_one_square_zero K A G (alg_mul A)
  (@alternating_wedge_anticommutative K h2 V W (alg_mul W) (alg_bilinear W) hcomm)
  h2 (f a) (one_generator_homogeneous a)).
Qed.
(** Source for [Omega_W]: Federer (1969), 1.4.4, p. 20, first assertion of
    the coefficient-algebra parenthesis, with corrected hypothesis. In
    words: For commutative associative unital coefficients, the identity
    from linear maps to one-forms extends uniquely to a unit-preserving
    exterior-to-alternating homomorphism. Definition or construction used to
    formalise this passage. Commutativity is required here: the printed
    assertion for arbitrary associative unital coefficients is false. *)
Definition Omega_W : algebra_map (exterior_algebra (Hom V W)) A :=
  exterior_algebra_extension one_generator_square_zero.
(** Source for [Omega_W_generator]: Federer (1969), 1.4.4, p. 20, first
    assertion of the coefficient-algebra parenthesis, with corrected
    hypothesis. In words: For commutative associative unital coefficients,
    the identity from linear maps to one-forms extends uniquely to a
    unit-preserving exterior-to-alternating homomorphism. Supporting result
    for the corrected coefficient statement; not an assertion of the printed
    book. Commutativity is required here: the printed assertion for
    arbitrary associative unital coefficients is false. *)
Lemma Omega_W_generator a : Omega_W (exterior_generator a) = one_generator a.
Proof. exact: exterior_algebra_extension_generator. Qed.
(** Source for [Omega_W_one]: Federer (1969), 1.4.4, p. 20, first assertion
    of the coefficient-algebra parenthesis, with corrected hypothesis. In
    words: For commutative associative unital coefficients, the identity
    from linear maps to one-forms extends uniquely to a unit-preserving
    exterior-to-alternating homomorphism. Supporting result for the
    corrected coefficient statement; not an assertion of the printed book.
    Commutativity is required here: the printed assertion for arbitrary
    associative unital coefficients is false. *)
Lemma Omega_W_one : Omega_W (exterior_unit (Hom V W)) = coefficient_form V (alg_one W).
Proof. exact: algebra_map_one. Qed.
(** Source for [Omega_W_wedge]: Federer (1969), 1.4.4, p. 20, first
    assertion of the coefficient-algebra parenthesis, with corrected
    hypothesis. In words: For commutative associative unital coefficients,
    the identity from linear maps to one-forms extends uniquely to a
    unit-preserving exterior-to-alternating homomorphism. Supporting result
    for the corrected coefficient statement; not an assertion of the printed
    book. Commutativity is required here: the printed assertion for
    arbitrary associative unital coefficients is false. *)
Lemma Omega_W_wedge x y : Omega_W (wedge x y) =
  alternating_wedge h2 (alg_bilinear W) (Omega_W x) (Omega_W y).
Proof. exact: algebra_map_mul. Qed.
(** Source for [Omega_W_graded]: Federer (1969), 1.4.4, p. 20, first
    assertion of the coefficient-algebra parenthesis, with corrected
    hypothesis. In words: For commutative associative unital coefficients,
    the identity from linear maps to one-forms extends uniquely to a
    unit-preserving exterior-to-alternating homomorphism. Supporting result
    for the corrected coefficient statement; not an assertion of the printed
    book. Commutativity is required here: the printed assertion for
    arbitrary associative unital coefficients is false. *)
Lemma Omega_W_graded : preserves_grading (exterior_grading (Hom V W)) G Omega_W.
Proof.
apply: (@exterior_algebra_extension_graded K (Hom V W) A G
  (@alternating_wedge_graded K h2 V W (alg_mul W) (alg_bilinear W)) f _
  one_generator_square_zero).
exact: one_generator_homogeneous.
Qed.
(** Source for [Omega_W_unique]: Federer (1969), 1.4.4, p. 20, first
    assertion of the coefficient-algebra parenthesis, with corrected
    hypothesis. In words: For commutative associative unital coefficients,
    the identity from linear maps to one-forms extends uniquely to a
    unit-preserving exterior-to-alternating homomorphism. Supporting result
    for the corrected coefficient statement; not an assertion of the printed
    book. Commutativity is required here: the printed assertion for
    arbitrary associative unital coefficients is false. *)
Theorem Omega_W_unique (g : algebra_map (exterior_algebra (Hom V W)) A) :
  (forall a, g (exterior_generator a) = one_generator a) -> forall x, g x = Omega_W x.
Proof. exact: exterior_algebra_extension_unique. Qed.
(** Source for [Omega_W_word]: Federer (1969), 1.4.4, p. 20, first assertion
    of the coefficient-algebra parenthesis, with corrected hypothesis. In
    words: For commutative associative unital coefficients, the identity
    from linear maps to one-forms extends uniquely to a unit-preserving
    exterior-to-alternating homomorphism. Supporting result for the
    corrected coefficient statement; not an assertion of the printed book.
    Commutativity is required here: the printed assertion for arbitrary
    associative unital coefficients is false. *)
Lemma Omega_W_word s : Omega_W (exterior_word s) =
  foldr (alternating_wedge h2 (alg_bilinear W)) (coefficient_form V (alg_one W))
    [seq one_generator a | a <- s].
Proof. rewrite /Omega_W exterior_algebra_extension_word; elim: s => //= a s ->; by []. Qed.
End CommutativeCoefficients.

(** Federer 1.4.4, the named map Omega has real (here field) coefficients. *)
Section ScalarCoefficients.
Variable K : fieldType.
Hypothesis h2 : (1+1 : K) != 0.
Variable V : lmodType K.
(** Source for [Omega]: Federer (1969), 1.4.4, p. 19, opening construction
    of Omega. In words: The identification of linear functionals with
    one-covectors extends uniquely to a unit-preserving algebra homomorphism
    from the exterior algebra of the dual to the alternating algebra.
    Definition or construction used to formalise this passage. *)
Definition Omega : algebra_map (exterior_algebra (Hom V K^o))
  (alternating_unital_algebra h2 V (scalar_algebra K)) :=
  @Omega_W K h2 V (scalar_algebra K) (@mulrC K).
(** Source for [Omega_generator]: Federer (1969), 1.4.4, p. 19, opening
    construction of Omega. In words: The identification of linear
    functionals with one-covectors extends uniquely to a unit-preserving
    algebra homomorphism from the exterior algebra of the dual to the
    alternating algebra. Formalises the indicated part of the passage under
    the hypotheses in the statement below. *)
Lemma Omega_generator a : Omega (exterior_generator a) = one_generator a.
Proof. exact: Omega_W_generator. Qed.
(** Source for [Omega_graded]: Federer (1969), 1.4.4, p. 19, opening
    construction of Omega. In words: The identification of linear
    functionals with one-covectors extends uniquely to a unit-preserving
    algebra homomorphism from the exterior algebra of the dual to the
    alternating algebra. Supporting lemma for this passage; not separately
    stated in the book. *)
Lemma Omega_graded : preserves_grading (exterior_grading (Hom V K^o))
  (A_star_grading V K^o) Omega.
Proof. exact (@Omega_W_graded K h2 V (scalar_algebra K) (@mulrC K)). Qed.
(** Source for [Omega_unique]: Federer (1969), 1.4.4, p. 19, opening
    construction of Omega. In words: The identification of linear
    functionals with one-covectors extends uniquely to a unit-preserving
    algebra homomorphism from the exterior algebra of the dual to the
    alternating algebra. Formalises the indicated part of the passage under
    the hypotheses in the statement below. *)
Theorem Omega_unique (g : algebra_map (exterior_algebra (Hom V K^o))
    (alternating_unital_algebra h2 V (scalar_algebra K))) :
  (forall a, g (exterior_generator a) = one_generator a) -> forall x, g x = Omega x.
Proof. exact (@Omega_W_unique K h2 V (scalar_algebra K) (@mulrC K) g). Qed.
(** Source for [Omega_m]: Federer (1969), 1.4.4, p. 19, opening construction
    of Omega. In words: The identification of linear functionals with
    one-covectors extends uniquely to a unit-preserving algebra homomorphism
    from the exterior algebra of the dual to the alternating algebra.
    Definition or construction used to formalise this passage. *)
Definition Omega_m m (x : exterior_power (Hom V K^o) m) : A_m V K^o m :=
  form_component m (Omega (component_val x)).
(** Source for [Omega_m_linear]: Federer (1969), 1.4.4, p. 19, opening
    construction of Omega. In words: The identification of linear
    functionals with one-covectors extends uniquely to a unit-preserving
    algebra homomorphism from the exterior algebra of the dual to the
    alternating algebra. Supporting lemma for this passage; not separately
    stated in the book. *)
Lemma Omega_m_linear m : linear (@Omega_m m).
Proof. move=> c x y; by rewrite /Omega_m !linearP. Qed.
HB.instance Definition _ m := GRing.isLinear.Build K (exterior_power (Hom V K^o) m)
  (A_m V K^o m) *:%R (@Omega_m m) (@Omega_m_linear m).
(** Source for [Omega_m_include]: Federer (1969), 1.4.4, p. 19, opening
    construction of Omega. In words: The identification of linear
    functionals with one-covectors extends uniquely to a unit-preserving
    algebra homomorphism from the exterior algebra of the dual to the
    alternating algebra. Supporting lemma for this passage; not separately
    stated in the book. *)
Lemma Omega_m_include m x : form_include (@Omega_m m x) = Omega (component_val x).
Proof. rewrite /Omega_m form_componentK; exact: Omega_graded (component_homogeneous x). Qed.
End ScalarCoefficients.
