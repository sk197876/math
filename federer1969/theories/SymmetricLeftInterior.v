(** Federer (1969), 1.10.3, p. 45: symmetric interior multiplications,
    defined by the characteristic pairings as in 1.5.1. Scalars may be any
    field here. No finite-dimensional hypothesis is used. surjectivity is
    neither asserted nor used. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From mathcomp.classical Require Import boolp.
From Federer Require Import ScalarCoefficients TensorUP Bilinear Graded GradedComponents
  TensorProduct AlgebraTensor TensorGrading Hom HomogeneousHom
  HomogeneousSum Convolution ConvolutionAssociativity GradedConvolution
  SymmetricAlgebra SymmetricGrading SymmetricDirectSum SymmetricDiagonal
  SymmetricCoassociativity SymmetricForms SymmetricFormWords
  SymmetricFormExtension SymmetricFormIsomorphism SymmetricFormSum
  SymmetricFormProduct SymmetricPairing.
From Federer Require Import ScalarTensorContraction SymmetricPairingSeparation
  SymmetricInteriorUP SymmetricLeftInteriorHom SymmetricLeftInteriorDegree
  SymmetricFormReindex.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

Section SymmetricLeftInterior.
Variable K : fieldType.
Variable V : lmodType K.
Variables p q : nat.

(** Source for [symmetric_left_interior]: Federer 1.10.3, p. 45,
    opening paragraph, referring to the characteristic conditions of
    1.5.1. In words: Regard the diagonal contraction as an actual vector in its proved degree q-p. *)
Definition symmetric_left_interior (_ : (p <= q)%N) (zeta : symmetric_power V q) (a : S_m V K^o p) :
  symmetric_power V (q-p) :=
  @Component K (symmetric_space V) (symmetric_grading V) (q-p)
    (symmetric_left_interior_hom (component_val zeta) (sform_homogeneous a))
    (introT eqP (symmetric_left_interior_degree zeta a)).
Variable hpq : (p <= q)%N.

(** Source for [symmetric_left_interiorE]: Federer 1.10.3, p. 45,
    opening paragraph, referring to the characteristic conditions of
    1.5.1. In words: Component inclusion recovers the diagonal contraction on the full symmetric algebra. *)
Lemma symmetric_left_interiorE zeta a : component_val (symmetric_left_interior hpq zeta a) =
  symmetric_left_interior_hom (component_val zeta) (sform_homogeneous a).
Proof. by []. Qed.

(** Source for [symmetric_left_interior_characteristic]: Federer 1.10.3, p. 45,
    opening paragraph, referring to the characteristic conditions of
    1.5.1. In words: The bracket of the contracted vector against beta equals the bracket of the original vector against alpha times beta. *)
Theorem symmetric_left_interior_characteristic zeta a (b : S_m V K^o (q-p)) :
  symmetric_pairing (symmetric_left_interior hpq zeta a) b =
    symmetric_pairing zeta (sform_reindex (subnKC hpq) (sform_product (scalar_bilinear K) a b)).
Proof.
change (sform_homogeneous b (component_val (symmetric_left_interior hpq zeta a)) =
  sform_homogeneous (sform_reindex (subnKC hpq) (sform_product (scalar_bilinear K) a b)) (component_val zeta)).
rewrite symmetric_left_interiorE sform_reindexE /sform_product homogeneous_sformK.
exact: symmetric_left_interior_diagram.
Qed.

(** Source for [symmetric_left_interior_unique]: Federer 1.10.3, p. 45,
    opening paragraph, referring to the characteristic conditions of
    1.5.1. In words: The characteristic brackets uniquely determine the left interior vector, including in infinite dimension. *)
Theorem symmetric_left_interior_unique zeta a (xi : symmetric_power V (q-p)) :
  (forall b : S_m V K^o (q-p), symmetric_pairing xi b =
    symmetric_pairing zeta (sform_reindex (subnKC hpq) (sform_product (scalar_bilinear K) a b))) ->
  xi = symmetric_left_interior hpq zeta a.
Proof.
move=> h; apply: symmetric_pairing_vectors_separate => b.
by rewrite h symmetric_left_interior_characteristic.
Qed.

(** Source for [symmetric_left_interior_bilinear]: Federer 1.10.3, p. 45,
    opening paragraph, referring to the characteristic conditions of
    1.5.1. In words: Left interior multiplication is linear separately in its vector and covector inputs. *)
Lemma symmetric_left_interior_bilinear : bilinear (symmetric_left_interior hpq).
Proof.
split.
- move=> a c x y; apply: val_inj.
  change (symmetric_left_interior_hom (component_val (c *: x+y)) (sform_homogeneous a) =
    component_val (c *: symmetric_left_interior hpq x a + symmetric_left_interior hpq y a)).
  by rewrite !linearP ?symmetric_left_interiorE (proj1 (symmetric_left_interior_hom_bilinear V)).
- move=> x c a b; apply: val_inj.
  change (symmetric_left_interior_hom (component_val x) (sform_homogeneous (c *: a+b)) =
    component_val (c *: symmetric_left_interior hpq x a + symmetric_left_interior hpq x b)).
  by rewrite !linearP ?symmetric_left_interiorE (proj2 (symmetric_left_interior_hom_bilinear V)).
Qed.

(** Source for [symmetric_left_interior_exists]: Federer 1.10.3, p. 45,
    opening paragraph, referring to the characteristic conditions of
    1.5.1. In words: The constructed operation satisfies the abstract bilinearity and characteristic-pairing specification. *)
Theorem symmetric_left_interior_exists : @is_symmetric_left_interior K V p q hpq (symmetric_left_interior hpq).
Proof. split; [exact: symmetric_left_interior_bilinear | exact: symmetric_left_interior_characteristic]. Qed.

(** Source for [symmetric_left_interior_universal]: Federer 1.10.3, p. 45,
    opening paragraph, referring to the characteristic conditions of
    1.5.1. In words: There exists exactly one bilinear operation satisfying the left characteristic pairing. *)
Theorem symmetric_left_interior_universal : exists i : symmetric_power V q -> S_m V K^o p -> symmetric_power V (q-p),
  is_symmetric_left_interior hpq i /\ forall j, is_symmetric_left_interior hpq j -> forall zeta a, j zeta a = i zeta a.
Proof.
exists (symmetric_left_interior hpq); split; first exact: symmetric_left_interior_exists.
move=> j [hj hc] zeta a; apply: symmetric_left_interior_unique => b; exact: hc.
Qed.
End SymmetricLeftInterior.
