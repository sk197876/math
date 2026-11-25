(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order ssralg.
From Federer Require Import Graded.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Infrastructure for Federer 1.3.2: the associative, unital graded
    algebras used there, with the products and maps already proved in 1.2.2. *)
(** Source for [unital_graded_algebra]: Federer (1969), 1.2.2, p. 12, final
    paragraph defining Phi. In words: Multiplication factors uniquely
    through a linear map Phi on A tensor A; for an associative commutative
    or anticommutative algebra this is a graded homomorphism for the
    corresponding tensor product. Definition or construction used to
    formalise this passage. *)
Record unital_graded_algebra (K : fieldType) := UnitalGradedAlgebra {
  unital_algebra :> algebra K;
  unital_grading : grading unital_algebra;
  unital_product_graded : graded_product unital_grading (alg_mul unital_algebra)
}.

(** Source for [unital_graded_view]: Federer (1969), 1.2.2, p. 12, final
    paragraph defining Phi. In words: Multiplication factors uniquely
    through a linear map Phi on A tensor A; for an associative commutative
    or anticommutative algebra this is a graded homomorphism for the
    corresponding tensor product. Definition or construction used to
    formalise this passage. *)
Definition unital_graded_view (K : fieldType) (A : unital_graded_algebra K) : graded_algebra K :=
  @GradedAlgebra K A (unital_grading A) (alg_mul A) (alg_bilinear A)
    (@unital_product_graded K A).

(** Source for [unital_one_homogeneous]: Federer (1969), 1.2.2, p. 12, final
    paragraph defining Phi. In words: Multiplication factors uniquely
    through a linear map Phi on A tensor A; for an associative commutative
    or anticommutative algebra this is a graded homomorphism for the
    corresponding tensor product. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma unital_one_homogeneous (K : fieldType) (A : unital_graded_algebra K) :
  homogeneous (unital_grading A) 0 (alg_one A).
Proof.
exact: (@graded_unit_degree_zero K A (unital_grading A) (alg_mul A)
  (alg_bilinear A) (@unital_product_graded K A) (alg_one A)
  (@alg_unitl K A) (@alg_unitr K A)).
Qed.

Section Tensor.
Variable K : fieldType.
Variables A B : unital_graded_algebra K.
Variable s : bool.
Local Notation AG := (unital_graded_view A).
Local Notation BG := (unital_graded_view B).
Local Notation mu := (@graded_tensor_mul K AG BG s).
Local Notation T := (tensor_space A B).

(** Source for [unital_tensor_algebra]: Federer (1969), 1.2.2, p. 12, final
    paragraph defining Phi. In words: Multiplication factors uniquely
    through a linear map Phi on A tensor A; for an associative commutative
    or anticommutative algebra this is a graded homomorphism for the
    corresponding tensor product. Definition or construction used to
    formalise this passage. *)
Definition unital_tensor_algebra : algebra K :=
  @Algebra K T mu (tensor_inj (alg_one A) (alg_one B))
    (graded_tensor_bilinear AG BG s)
    (@graded_tensor_associative K AG BG s (@alg_assoc K A) (@alg_assoc K B))
    (@tensor_unit_left K AG BG s (alg_one A) (alg_one B)
      (@alg_unitl K A) (@alg_unitl K B) (@alg_unitr K B))
    (@tensor_unit_right K AG BG s (alg_one A) (alg_one B)
      (@alg_unitl K A) (@alg_unitr K A) (@alg_unitr K B)).

(** Source for [unital_graded_tensor]: Federer (1969), 1.2.2, p. 12, final
    paragraph defining Phi. In words: Multiplication factors uniquely
    through a linear map Phi on A tensor A; for an associative commutative
    or anticommutative algebra this is a graded homomorphism for the
    corresponding tensor product. Definition or construction used to
    formalise this passage. *)
Definition unital_graded_tensor : unital_graded_algebra K :=
  @UnitalGradedAlgebra K unital_tensor_algebra
    (tensor_grading_product (unital_grading A) (unital_grading B))
    (@graded_tensor_mul_degree K AG BG s).

(** Source for [tensor_left]: Federer (1969), 1.2.2, p. 12, final paragraph
    defining Phi. In words: Multiplication factors uniquely through a linear
    map Phi on A tensor A; for an associative commutative or anticommutative
    algebra this is a graded homomorphism for the corresponding tensor
    product. Definition or construction used to formalise this passage. *)
Definition tensor_left (a : A) : T := tensor_inj a (alg_one B).
(** Source for [tensor_left_linear]: Federer (1969), 1.2.2, p. 12, final
    paragraph defining Phi. In words: Multiplication factors uniquely
    through a linear map Phi on A tensor A; for an associative commutative
    or anticommutative algebra this is a graded homomorphism for the
    corresponding tensor product. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma tensor_left_linear : linear tensor_left.
Proof. by move=> k a a'; rewrite /tensor_left tensor_inj_addl tensor_inj_scalel. Qed.
HB.instance Definition _ := GRing.isLinear.Build K A T *:%R tensor_left tensor_left_linear.
(** Source for [tensor_right]: Federer (1969), 1.2.2, p. 12, final paragraph
    defining Phi. In words: Multiplication factors uniquely through a linear
    map Phi on A tensor A; for an associative commutative or anticommutative
    algebra this is a graded homomorphism for the corresponding tensor
    product. Definition or construction used to formalise this passage. *)
Definition tensor_right (b : B) : T := tensor_inj (alg_one A) b.
(** Source for [tensor_right_linear]: Federer (1969), 1.2.2, p. 12, final
    paragraph defining Phi. In words: Multiplication factors uniquely
    through a linear map Phi on A tensor A; for an associative commutative
    or anticommutative algebra this is a graded homomorphism for the
    corresponding tensor product. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma tensor_right_linear : linear tensor_right.
Proof. by move=> k b b'; rewrite /tensor_right tensor_inj_addr tensor_inj_scaler. Qed.
HB.instance Definition _ := GRing.isLinear.Build K B T *:%R tensor_right tensor_right_linear.

(** Source for [tensor_left_mul]: Federer (1969), 1.2.2, p. 12, final
    paragraph defining Phi. In words: Multiplication factors uniquely
    through a linear map Phi on A tensor A; for an associative commutative
    or anticommutative algebra this is a graded homomorphism for the
    corresponding tensor product. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma tensor_left_mul a c : tensor_left (alg_mul A a c) = mu (tensor_left a) (tensor_left c).
Proof.
elim/(graded_induction (G := unital_grading A)): c => [|c d hc hd|n c hc].
- by rewrite (bil0r (alg_bilinear A)) linear0 (bil0r (graded_tensor_bilinear AG BG s)).
- rewrite (bilDr (alg_bilinear A)) !linearD (bilDr (graded_tensor_bilinear AG BG s)).
  change (tensor_left (alg_mul A a c) + tensor_left (alg_mul A a d) =
    mu (tensor_left a) (tensor_left c) + mu (tensor_left a) (tensor_left d)).
  by rewrite hc hd.
rewrite /tensor_left (@graded_tensor_mulE K AG BG s 0 n a (alg_one B) c (alg_one B)
  (unital_one_homogeneous B) hc) koszul0l scale1r.
change (tensor_inj (alg_mul A a c) (alg_one B) =
  tensor_inj (alg_mul A a c) (alg_mul B (alg_one B) (alg_one B))).
by rewrite alg_unitl.
Qed.
(** Source for [tensor_right_mul]: Federer (1969), 1.2.2, p. 12, final
    paragraph defining Phi. In words: Multiplication factors uniquely
    through a linear map Phi on A tensor A; for an associative commutative
    or anticommutative algebra this is a graded homomorphism for the
    corresponding tensor product. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma tensor_right_mul b d : tensor_right (alg_mul B b d) = mu (tensor_right b) (tensor_right d).
Proof.
elim/(graded_induction (G := unital_grading B)): b => [|b c hb hc|n b hb].
- by rewrite (bil0l (alg_bilinear B)) linear0 (bil0l (graded_tensor_bilinear AG BG s)).
- rewrite (bilDl (alg_bilinear B)) !linearD (bilDl (graded_tensor_bilinear AG BG s)).
  change (tensor_right (alg_mul B b d) + tensor_right (alg_mul B c d) =
    mu (tensor_right b) (tensor_right d) + mu (tensor_right c) (tensor_right d)).
  by rewrite hb hc.
rewrite /tensor_right (@graded_tensor_mulE K AG BG s n 0 (alg_one A) b (alg_one A) d
  hb (unital_one_homogeneous A)) koszul0r scale1r.
change (tensor_inj (alg_one A) (alg_mul B b d) =
  tensor_inj (alg_mul A (alg_one A) (alg_one A)) (alg_mul B b d)).
by rewrite alg_unitl.
Qed.

(** Source for [tensor_left_map]: Federer (1969), 1.2.2, p. 12, final
    paragraph defining Phi. In words: Multiplication factors uniquely
    through a linear map Phi on A tensor A; for an associative commutative
    or anticommutative algebra this is a graded homomorphism for the
    corresponding tensor product. Definition or construction used to
    formalise this passage. *)
Definition tensor_left_map : algebra_map A unital_tensor_algebra :=
  @AlgebraMap K A unital_tensor_algebra (GRing.Linear.clone _ _ _ _ tensor_left _)
    (erefl _) tensor_left_mul.
(** Source for [tensor_right_map]: Federer (1969), 1.2.2, p. 12, final
    paragraph defining Phi. In words: Multiplication factors uniquely
    through a linear map Phi on A tensor A; for an associative commutative
    or anticommutative algebra this is a graded homomorphism for the
    corresponding tensor product. Definition or construction used to
    formalise this passage. *)
Definition tensor_right_map : algebra_map B unital_tensor_algebra :=
  @AlgebraMap K B unital_tensor_algebra (GRing.Linear.clone _ _ _ _ tensor_right _)
    (erefl _) tensor_right_mul.

(** Source for [tensor_left_graded]: Federer (1969), 1.2.2, p. 12, final
    paragraph defining Phi. In words: Multiplication factors uniquely
    through a linear map Phi on A tensor A; for an associative commutative
    or anticommutative algebra this is a graded homomorphism for the
    corresponding tensor product. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma tensor_left_graded : preserves_grading (unital_grading A)
  (unital_grading unital_graded_tensor) tensor_left.
Proof.
move=> n a ha; rewrite -[n]addn0.
exact: tensor_homogeneous_pure ha (unital_one_homogeneous B).
Qed.
(** Source for [tensor_right_graded]: Federer (1969), 1.2.2, p. 12, final
    paragraph defining Phi. In words: Multiplication factors uniquely
    through a linear map Phi on A tensor A; for an associative commutative
    or anticommutative algebra this is a graded homomorphism for the
    corresponding tensor product. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma tensor_right_graded : preserves_grading (unital_grading B)
  (unital_grading unital_graded_tensor) tensor_right.
Proof.
move=> n b hb; rewrite -[n]add0n.
exact: tensor_homogeneous_pure (unital_one_homogeneous A) hb.
Qed.

(** Source for [tensor_left_right]: Federer (1969), 1.2.2, p. 12, final
    paragraph defining Phi. In words: Multiplication factors uniquely
    through a linear map Phi on A tensor A; for an associative commutative
    or anticommutative algebra this is a graded homomorphism for the
    corresponding tensor product. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma tensor_left_right a b : mu (tensor_left a) (tensor_right b) = tensor_inj a b.
Proof.
rewrite /tensor_left /tensor_right
  (@graded_tensor_mulE K AG BG s 0 0 a (alg_one B) (alg_one A) b
    (unital_one_homogeneous B) (unital_one_homogeneous A)) koszul0l scale1r.
change (tensor_inj (alg_mul A a (alg_one A)) (alg_mul B (alg_one B) b) = tensor_inj a b).
by rewrite alg_unitr alg_unitl.
Qed.
End Tensor.
Arguments tensor_left {K} A B a.
Arguments tensor_right {K} A B b.

Section Maps.
Variable K : fieldType.
Variables A B C D : unital_graded_algebra K.
Variables (f : algebra_map A C) (g : algebra_map B D).
Hypotheses (hf : preserves_grading (unital_grading A) (unital_grading C) f)
  (hg : preserves_grading (unital_grading B) (unital_grading D) g).
Variable s : bool.

(** Source for [unital_tensor_map]: Federer (1969), 1.2.2, p. 12, final
    paragraph defining Phi. In words: Multiplication factors uniquely
    through a linear map Phi on A tensor A; for an associative commutative
    or anticommutative algebra this is a graded homomorphism for the
    corresponding tensor product. Definition or construction used to
    formalise this passage. *)
Definition unital_tensor_map : algebra_map (unital_tensor_algebra A B s) (unital_tensor_algebra C D s).
Proof.
apply: (@AlgebraMap K (unital_tensor_algebra A B s)
  (unital_tensor_algebra C D s) (tensor_map f g)).
  by rewrite /= tensor_mapE !algebra_map_one.
exact: (@tensor_map_multiplicative K (unital_graded_view A) (unital_graded_view B)
  (unital_graded_view C) (unital_graded_view D) f g hf hg
  (algebra_map_mul f) (algebra_map_mul g) s).
Defined.
End Maps.

(** Federer 1.2.2 and 1.3.2: Phi is the homomorphism induced by multiplication. *)
Section Multiplication.
Variable K : fieldType.
Variable A : unital_graded_algebra K.
Hypothesis hanti : graded_anticommutative (unital_grading A) (alg_mul A).

(** Source for [Phi]: Federer (1969), 1.2.2, p. 12, final paragraph defining
    Phi. In words: Multiplication factors uniquely through a linear map Phi
    on A tensor A; for an associative commutative or anticommutative algebra
    this is a graded homomorphism for the corresponding tensor product.
    Definition or construction used to formalise this passage. *)
Definition Phi : algebra_map (unital_tensor_algebra A A true) A.
Proof.
apply: (@AlgebraMap K (unital_tensor_algebra A A true) A
  (graded_multiplication (unital_graded_view A))).
  change (graded_multiplication (unital_graded_view A)
    (tensor_inj (alg_one A) (alg_one A)) = alg_one A).
  rewrite graded_multiplicationE.
  change (alg_mul A (alg_one A) (alg_one A) = alg_one A).
  exact: alg_unitl.
exact: (@signed_multiplication_hom K (unital_graded_view A) (@alg_assoc K A) hanti).
Defined.
(** Source for [PhiE]: Federer (1969), 1.2.2, p. 12, final paragraph
    defining Phi. In words: Multiplication factors uniquely through a linear
    map Phi on A tensor A; for an associative commutative or anticommutative
    algebra this is a graded homomorphism for the corresponding tensor
    product. Formalises the indicated part of the passage under the
    hypotheses in the statement below. *)
Lemma PhiE a b : Phi (tensor_inj a b) = alg_mul A a b.
Proof. exact: (@graded_multiplicationE K (unital_graded_view A) a b). Qed.
(** Source for [Phi_graded]: Federer (1969), 1.2.2, p. 12, final paragraph
    defining Phi. In words: Multiplication factors uniquely through a linear
    map Phi on A tensor A; for an associative commutative or anticommutative
    algebra this is a graded homomorphism for the corresponding tensor
    product. Supporting lemma for this passage; not separately stated in the
    book. *)
Lemma Phi_graded : preserves_grading
  (unital_grading (unital_graded_tensor A A true)) (unital_grading A) Phi.
Proof. exact: (@graded_multiplication_graded K (unital_graded_view A)). Qed.
End Multiplication.
