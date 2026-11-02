(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import DualExterior.
From Federer Require Import TraceBasisProduct.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Federer 1.4.5, opening assertion: the ordinary tensor product
    is neither commutative nor graded anticommutative when both
    vector spaces have dimension greater than one. The following
    witnesses use only the indicated biorthogonal vectors. *)
Section TensorFunctionals.
Variable K : fieldType.
Variables U E : lmodType K.
Variables f : {linear U -> K^o}.
Variables g : {linear E -> K^o}.
(** Source for [scalar_tensor_functional]: Federer (1969), 1.4.5, p. 20,
    opening sentence and its parenthesised exception. In words: The ordinary
    tensor product of two exterior algebras is asserted to be neither
    commutative nor anticommutative apart from the printed exception.
    Definition or construction used to formalise this passage. The
    zero-dimensional examples are local counterexamples to the unrestricted
    printed exception, not examples stated in Federer. *)
Definition scalar_tensor_functional : {linear tensor_space U E -> K^o} :=
  GRing.Linear.clone _ _ _ _ (tensor_lift (bilinear_pre f g (scalar_bilinear K))) _.
(** Source for [scalar_tensor_functionalE]: Federer (1969), 1.4.5, p. 20,
    opening sentence and its parenthesised exception. In words: The ordinary
    tensor product of two exterior algebras is asserted to be neither
    commutative nor anticommutative apart from the printed exception.
    Supporting lemma for this passage; not separately stated in the book.
    The zero-dimensional examples are local counterexamples to the
    unrestricted printed exception, not examples stated in Federer. *)
Lemma scalar_tensor_functionalE x y : scalar_tensor_functional (tensor_inj x y) = f x * g y.
Proof. exact: tensor_liftE. Qed.
End TensorFunctionals.
Section Evaluation.
Variable K : fieldType.
Variables V : lmodType K.
(** Source for [covector_evaluation]: Federer (1969), 1.4.5, p. 20, opening
    sentence and its parenthesised exception. In words: The ordinary tensor
    product of two exterior algebras is asserted to be neither commutative
    nor anticommutative apart from the printed exception. Definition or
    construction used to formalise this passage. The zero-dimensional
    examples are local counterexamples to the unrestricted printed
    exception, not examples stated in Federer. *)
Definition covector_evaluation (x : exterior_space V) (phi : A_star V K^o) : K^o := phi x.
(** Source for [covector_evaluation_linear]: Federer (1969), 1.4.5, p. 20,
    opening sentence and its parenthesised exception. In words: The ordinary
    tensor product of two exterior algebras is asserted to be neither
    commutative nor anticommutative apart from the printed exception.
    Supporting lemma for this passage; not separately stated in the book.
    The zero-dimensional examples are local counterexamples to the
    unrestricted printed exception, not examples stated in Federer. *)
Lemma covector_evaluation_linear x : linear (covector_evaluation x).
Proof. move=> c phi psi; by rewrite /covector_evaluation hom_finite_addE hom_finite_scaleE. Qed.
HB.instance Definition _ x := GRing.isLinear.Build K (A_star V K^o) K^o *:%R
  (covector_evaluation x) (covector_evaluation_linear x).
End Evaluation.
Section OrdinaryObstructions.
Variable K : fieldType.
Hypothesis h2 : (1+1 : K) != 0.
Variables V W : lmodType K.
Local Notation U := (alternating_unital_algebra h2 V (scalar_algebra K)).
Local Notation E := (exterior_algebra W).
Local Notation T := (algebra_tensor U E).
Local Notation G := (tensor_grading_product (A_star_grading V K^o) (exterior_grading W)).
Variables b0 b1 : Hom W K^o.
Variables w0 w1 : W.
Hypotheses (h00 : b0 w0 = 1) (h01 : b0 w1 = 0)
  (h10 : b1 w0 = 0) (h11 : b1 w1 = 1).
(** Source for [two_covector]: Federer (1969), 1.4.5, p. 20, opening
    sentence and its parenthesised exception. In words: The ordinary tensor
    product of two exterior algebras is asserted to be neither commutative
    nor anticommutative apart from the printed exception. Definition or
    construction used to formalise this passage. The zero-dimensional
    examples are local counterexamples to the unrestricted printed
    exception, not examples stated in Federer. *)
Definition two_covector := alternating_wedge h2 (scalar_bilinear K) (one_generator b0) (one_generator b1).
(** Source for [detect_commutator]: Federer (1969), 1.4.5, p. 20, opening
    sentence and its parenthesised exception. In words: The ordinary tensor
    product of two exterior algebras is asserted to be neither commutative
    nor anticommutative apart from the printed exception. Definition or
    construction used to formalise this passage. The zero-dimensional
    examples are local counterexamples to the unrestricted printed
    exception, not examples stated in Federer. *)
Definition detect_commutator : {linear T -> K^o} := scalar_tensor_functional
  (GRing.Linear.clone _ _ _ _ (covector_evaluation (exterior_unit V)) _)
  (hom_as_linear two_covector).
(** Source for [detect_right_product]: Federer (1969), 1.4.5, p. 20, opening
    sentence and its parenthesised exception. In words: The ordinary tensor
    product of two exterior algebras is asserted to be neither commutative
    nor anticommutative apart from the printed exception. Supporting lemma
    for this passage; not separately stated in the book. The
    zero-dimensional examples are local counterexamples to the unrestricted
    printed exception, not examples stated in Federer. *)
Lemma detect_right_product v w :
  detect_commutator (alg_mul T (@algebra_tensor_right K U E (exterior_generator v))
    (@algebra_tensor_right K U E (exterior_generator w))) = b0 v * b1 w - b0 w * b1 v.
Proof.
rewrite /algebra_tensor_right ordinary_tensor_productE alg_unitl.
rewrite /detect_commutator scalar_tensor_functionalE.
change (coefficient_form V (1 : K^o) (exterior_unit V) *
  two_covector (wedge (exterior_generator v) (exterior_generator w)) = b0 v*b1 w-b0 w*b1 v).
rewrite coefficient_formE exterior_augmentation_unit scale1r mul1r.
have hw : wedge (exterior_generator v) (exterior_generator w) = exterior_word [::v;w].
  by rewrite !exterior_word_cons exterior_word_nil wedge_unitr.
rewrite hw /two_covector.
exact: one_forms_wedge_two.
Qed.
(** Source for [ordinary_tensor_not_commutative]: Federer (1969), 1.4.5, p.
    20, opening sentence and its parenthesised exception. In words: The
    ordinary tensor product of two exterior algebras is asserted to be
    neither commutative nor anticommutative apart from the printed
    exception. Formalises the indicated part of the passage under the
    hypotheses in the statement below. The zero-dimensional examples are
    local counterexamples to the unrestricted printed exception, not
    examples stated in Federer. *)
Theorem ordinary_tensor_not_commutative : ~ commutative (alg_mul T).
Proof.
move=> hc; have hh := congr1 detect_commutator
  (hc (@algebra_tensor_right K U E (exterior_generator w0))
    (@algebra_tensor_right K U E (exterior_generator w1))).
have hs : b0 w0*b1 w1-b0 w1*b1 w0 = b0 w1*b1 w0-b0 w0*b1 w1 :=
  eq_trans (esym (@detect_right_product w0 w1))
    (eq_trans hh (@detect_right_product w1 w0)).
clear hh.
rewrite h00 h01 h10 h11 !mul1r !mul0r subr0 sub0r in hs.
have hz : (1+1 : K) = 0 by rewrite {1}hs addNr.
by move: h2; rewrite hz eqxx.
Qed.
Variable a : Hom V K^o.
Variable v : V.
Hypothesis hav : a v = 1.
(** Source for [detect_crossing]: Federer (1969), 1.4.5, p. 20, opening
    sentence and its parenthesised exception. In words: The ordinary tensor
    product of two exterior algebras is asserted to be neither commutative
    nor anticommutative apart from the printed exception. Definition or
    construction used to formalise this passage. The zero-dimensional
    examples are local counterexamples to the unrestricted printed
    exception, not examples stated in Federer. *)
Definition detect_crossing : {linear T -> K^o} := scalar_tensor_functional
  (GRing.Linear.clone _ _ _ _ (covector_evaluation (exterior_generator v)) _)
  (linear_comp (hom_as_linear b0) (exterior_degree_one W)).
(** Source for [detect_crossingE]: Federer (1969), 1.4.5, p. 20, opening
    sentence and its parenthesised exception. In words: The ordinary tensor
    product of two exterior algebras is asserted to be neither commutative
    nor anticommutative apart from the printed exception. Supporting lemma
    for this passage; not separately stated in the book. The
    zero-dimensional examples are local counterexamples to the unrestricted
    printed exception, not examples stated in Federer. *)
Lemma detect_crossingE : detect_crossing (tensor_inj (one_generator a) (exterior_generator w0)) = 1.
Proof.
rewrite /detect_crossing scalar_tensor_functionalE.
change (one_generator a (exterior_generator v) * b0 (exterior_degree_one W (exterior_generator w0)) = 1).
by rewrite one_generatorE exterior_generatorK hav h00 mulr1.
Qed.
(** Source for [ordinary_tensor_not_anticommutative]: Federer (1969), 1.4.5,
    p. 20, opening sentence and its parenthesised exception. In words: The
    ordinary tensor product of two exterior algebras is asserted to be
    neither commutative nor anticommutative apart from the printed
    exception. Formalises the indicated part of the passage under the
    hypotheses in the statement below. The zero-dimensional examples are
    local counterexamples to the unrestricted printed exception, not
    examples stated in Federer. *)
Theorem ordinary_tensor_not_anticommutative : ~ graded_anticommutative G (alg_mul T).
Proof.
move=> hc.
have hx : homogeneous G 1 (@algebra_tensor_left K U E (one_generator a)).
  exact (@tensor_homogeneous_pure K U E (A_star_grading V K^o) (exterior_grading W)
    1 0 (one_generator a) (exterior_unit W)
    (one_generator_homogeneous a) (exterior_unit_homogeneous W)).
have hy : homogeneous G 1 (@algebra_tensor_right K U E (exterior_generator w0)).
  exact (@tensor_homogeneous_pure K U E (A_star_grading V K^o) (exterior_grading W)
    0 1 (coefficient_form V (1 : K^o)) (exterior_generator w0)
    (coefficient_form_homogeneous V (1 : K^o)) (exterior_generator_homogeneous w0)).
have hp := hc 1 1 _ _ hx hy.
have hs : tensor_inj (one_generator a) (exterior_generator w0) =
    (-1 : K)^+(1*1) *: tensor_inj (one_generator a) (exterior_generator w0) :=
  eq_trans (esym (@algebra_tensor_left_right K U E (one_generator a) (exterior_generator w0)))
    (eq_trans hp (congr1 (fun z : T => (-1 : K)^+(1*1) *: z)
      (@algebra_tensor_right_left K U E (one_generator a) (exterior_generator w0)))).
rewrite muln1 expr1 scaleN1r in hs.
have hh : (1 : K) = -1 :=
  eq_trans (esym detect_crossingE)
    (eq_trans (congr1 detect_crossing hs)
      (eq_trans (linearN detect_crossing _)
        (congr1 (fun c : K => -c) detect_crossingE))).
have hz : (1+1 : K) = 0 by rewrite {1}hh addNr.
by move: h2; rewrite hz eqxx.
Qed.
End OrdinaryObstructions.
