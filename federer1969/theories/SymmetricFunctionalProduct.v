(** Federer (1969), 1.10.5, p. 48, supporting scalar forms for the
    pure-power mass identity. The product of the values of one linear
    functional is a symmetric multilinear form. It is obtained from the
    existing abstract symmetric algebra extension, with no choice of
    coordinates. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import TensorUP AlgebraUP Hom GradedComponents ScalarCoefficients
  WordEvaluation SymmetricAlgebra SymmetricGrading SymmetricForms
  SymmetricFormIsomorphism SymmetricPairing.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section Product.
Variable K : fieldType.
Variable V : lmodType K.
Variable f : {linear V -> K^o}.

(** Source for [symmetric_functional_extension]: Federer 1.10.5,
    p. 48, supporting extension of a scalar functional to products.
    The commutative scalar algebra is a target for the universal property
    in 1.9.1, p. 41. *)
Definition symmetric_functional_extension :=
  @symmetric_algebra_extension K V (scalar_algebra K) f (@mulrC K).

(** Source for [symmetric_functional_product_hom]: Federer 1.10.5,
    p. 48, restriction of the extended functional to the m-th
    symmetric power; this is the linear map representing the product form. *)
Definition symmetric_functional_product_hom m : Hom (symmetric_power V m) K^o :=
  hom_of_linear (linear_comp symmetric_functional_extension
    (GRing.Linear.clone _ _ _ _ (@component_val K (symmetric_space V) (symmetric_grading V) m) _)).

(** Source for [symmetric_functional_product_form]: Federer 1.10.5,
    p. 48, the symmetric form whose value is the product of
    the individual functional values. It is normalized without a factorial. *)
Definition symmetric_functional_product_form m : S_m V K^o m :=
  hom_to_sform (symmetric_functional_product_hom m).

(** Source for [scalar_functional_word_product]: Federer 1.10.5,
    p. 48, supporting scalar evaluation: the universal algebra
    extension on a word is the ordinary product of its scalar images. *)
Lemma scalar_functional_word_product s :
  @word_eval K V (scalar_algebra K) f s = \prod_(x <- s) f x.
Proof. elim: s=> [|x s ih]; by rewrite /= ?big_nil ?big_cons ?ih. Qed.

(** Source for [symmetric_functional_product_formE]: Federer 1.10.5,
    p. 48, the product form evaluates on a tuple as the
    product of the functional values, including the empty product. *)
Lemma symmetric_functional_product_formE m (t : m.-tuple V) :
  symmetric_functional_product_form m t = \prod_(i < m) f (tnth t i).
Proof.
rewrite /symmetric_functional_product_form hom_to_sformE
  /symmetric_functional_product_hom hom_of_linearE /=.
change (symmetric_functional_extension (component_val (symmetric_tuple_component t)) =
  \prod_(i < m) f (tnth t i)).
rewrite symmetric_tuple_componentE /symmetric_functional_extension
  symmetric_algebra_extension_word scalar_functional_word_product.
exact: big_tuple.
Qed.

(** Source for [symmetric_functional_product_pairing]: Federer
    1.10.5, p. 48, the product form pairs with an arbitrary
    symmetric vector by the restricted algebra extension. *)
Lemma symmetric_functional_product_pairing m (x : symmetric_power V m) :
  symmetric_pairing x (symmetric_functional_product_form m) =
    symmetric_functional_product_hom m x.
Proof. by rewrite /symmetric_pairing /symmetric_functional_product_form hom_to_sformK. Qed.

(** Source for [symmetric_functional_product_diagonal]: Federer
    1.10.5, p. 48, supporting pure-power calculation: evaluation
    on m copies of x is the m-th power of the scalar functional value. *)
Lemma symmetric_functional_product_diagonal m (x : V) :
  symmetric_pairing (symmetric_tuple_component [tuple x | i < m])
    (symmetric_functional_product_form m) = (f x)^+m.
Proof.
rewrite symmetric_pairing_tuple symmetric_functional_product_formE.
under eq_bigr do rewrite tnth_mktuple.
by rewrite prodr_const card_ord.
Qed.
End Product.
