(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import DualExterior.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Federer 1.4.5, opening parenthesis: the exception as printed
    (V isomorphic to R or W isomorphic to R) omits zero-dimensional
    spaces. When both spaces are zero, the ordinary tensor product
    is commutative. Thus the literal unrestricted assertion cannot
    be adopted as an axiom. *)
Section ZeroException.
Variable K : fieldType.
Hypothesis h2 : (1+1 : K) != 0.
Local Notation V := (coordinate_space K 0).
Local Notation U := (alternating_unital_algebra h2 V (scalar_algebra K)).
Local Notation E := (exterior_algebra V).
(** Source for [zero_vector]: Federer (1969), 1.4.5, p. 20, opening sentence
    and its parenthesised exception. In words: The ordinary tensor product
    of two exterior algebras is asserted to be neither commutative nor
    anticommutative apart from the printed exception. Supporting lemma for
    this passage; not separately stated in the book. The zero-dimensional
    examples are local counterexamples to the unrestricted printed
    exception, not examples stated in Federer. *)
Lemma zero_vector (v : V) : v = 0.
Proof. apply/ffunP=> i; have := ltn_ord i; by rewrite ltn0. Qed.
(** Source for [zero_exterior_scalar]: Federer (1969), 1.4.5, p. 20, opening
    sentence and its parenthesised exception. In words: The ordinary tensor
    product of two exterior algebras is asserted to be neither commutative
    nor anticommutative apart from the printed exception. Supporting lemma
    for this passage; not separately stated in the book. The
    zero-dimensional examples are local counterexamples to the unrestricted
    printed exception, not examples stated in Federer. *)
Lemma zero_exterior_scalar (x : E) : x = (exterior_augmentation V x : K) *: exterior_unit V.
Proof. exact: exterior_zero_reconstruction zero_vector x. Qed.
(** Source for [zero_covector_scalar]: Federer (1969), 1.4.5, p. 20, opening
    sentence and its parenthesised exception. In words: The ordinary tensor
    product of two exterior algebras is asserted to be neither commutative
    nor anticommutative apart from the printed exception. Supporting lemma
    for this passage; not separately stated in the book. The
    zero-dimensional examples are local counterexamples to the unrestricted
    printed exception, not examples stated in Federer. *)
Lemma zero_covector_scalar (phi : U) : phi = (phi (exterior_unit V) : K) *: alg_one U.
Proof.
apply: hom_finite_ext => x; rewrite hom_finite_scaleE.
change (phi x = (phi (exterior_unit V) : K) * coefficient_form V (1 : K^o) x).
rewrite {1}(zero_exterior_scalar x) (linZ (hom_linear phi)) coefficient_formE.
change ((exterior_augmentation V x : K)*phi (exterior_unit V) =
  (phi (exterior_unit V) : K)*((exterior_augmentation V x : K)*1)).
by rewrite mulr1 mulrC.
Qed.
(** Source for [scalar_generated_commutative]: Federer (1969), 1.4.5, p. 20,
    opening sentence and its parenthesised exception. In words: The ordinary
    tensor product of two exterior algebras is asserted to be neither
    commutative nor anticommutative apart from the printed exception.
    Supporting lemma for this passage; not separately stated in the book.
    The zero-dimensional examples are local counterexamples to the
    unrestricted printed exception, not examples stated in Federer. *)
Lemma scalar_generated_commutative (B : algebra K) (c : B -> K) :
  (forall x, x = c x *: alg_one B) -> commutative (alg_mul B).
Proof.
move=> h x y; rewrite (h x) (h y) !(bilZl (alg_bilinear B)) !(bilZr (alg_bilinear B)) !scalerA.
by rewrite mulrC.
Qed.
(** Source for [zero_ordinary_tensor_commutative]: Federer (1969), 1.4.5, p.
    20, opening sentence and its parenthesised exception. In words: The
    ordinary tensor product of two exterior algebras is asserted to be
    neither commutative nor anticommutative apart from the printed
    exception. Local counterexample or necessary correction to the printed
    assertion, not a claim of the book. The zero-dimensional examples are
    local counterexamples to the unrestricted printed exception, not
    examples stated in Federer. *)
Theorem zero_ordinary_tensor_commutative : commutative (alg_mul (algebra_tensor U E)).
Proof.
apply: algebra_tensor_commutative.
- exact: scalar_generated_commutative zero_covector_scalar.
- exact: scalar_generated_commutative zero_exterior_scalar.
Qed.
(** Source for [zero_spaces_not_lines]: Federer (1969), 1.4.5, p. 20,
    opening sentence and its parenthesised exception. In words: The ordinary
    tensor product of two exterior algebras is asserted to be neither
    commutative nor anticommutative apart from the printed exception. Local
    counterexample or necessary correction to the printed assertion, not a
    claim of the book. The zero-dimensional examples are local
    counterexamples to the unrestricted printed exception, not examples
    stated in Federer. *)
Theorem zero_spaces_not_lines :
  dim (finite_basis_vect (coordinate_basisP K 0)) = 0%N /\
  dim (finite_basis_vect (coordinate_basisP K 0)) != 1%N.
Proof. by rewrite finite_basis_dimension card_ord. Qed.
(** Source for [zero_space_not_isomorphic_scalar]: Federer (1969), 1.4.5, p.
    20, opening sentence and its parenthesised exception. In words: The
    ordinary tensor product of two exterior algebras is asserted to be
    neither commutative nor anticommutative apart from the printed
    exception. Local counterexample or necessary correction to the printed
    assertion, not a claim of the book. The zero-dimensional examples are
    local counterexamples to the unrestricted printed exception, not
    examples stated in Federer. *)
Theorem zero_space_not_isomorphic_scalar :
  ~ exists f : {linear V -> K^o}, bijective f.
Proof.
move=> [f [g fg gf]]; have h := gf 1.
rewrite (zero_vector (g 1)) linear0 in h.
by have /eqP := esym h; rewrite oner_eq0.
Qed.
End ZeroException.
