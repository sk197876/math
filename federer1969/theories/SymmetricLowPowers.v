(** Federer (1969), 1.9.1, p. 41: the identifications Sym_0(V)=K and
    Sym_1(V)=V as mutually inverse linear maps. Arbitrary fields are
    allowed; the proofs use the abstract interface. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order ssralg.
From Federer Require Import TensorUP Bilinear AlgebraUP GradedAlgebra
  GradedComponents SymmetricAlgebra SymmetricGrading.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section LowPowers.
Variable K : fieldType.
Variable V : lmodType K.
Local Notation E := (symmetric_space V).
Local Notation G := (symmetric_grading V).

(** Source for [symmetric_zeroth_inclusion]: Federer 1.9.1, p. 41,
    the sentence identifying the zeroth and first powers. In words:
    The scalar inclusion and augmentation are inverse linear
    identifications of the degree-zero power with the scalar field. *)
Definition symmetric_zeroth_inclusion : {linear K^o -> symmetric_power V 0} :=
  linear_comp (GRing.Linear.clone _ _ _ _ (component G 0) _)
    (GRing.Linear.clone _ _ _ _ (symmetric_scalar V) _).

(** Source for [symmetric_zeroth_inverse]: Federer 1.9.1, p. 41,
    the sentence identifying the zeroth and first powers. In words:
    The scalar inclusion and augmentation are inverse linear
    identifications of the degree-zero power with the scalar field. *)
Definition symmetric_zeroth_inverse : {linear symmetric_power V 0 -> K^o} :=
  linear_comp (symmetric_augmentation V)
    (GRing.Linear.clone _ _ _ _ (@component_val K E G 0) _).

(** Source for [symmetric_zeroth_inclusionK]: Federer 1.9.1, p. 41,
    the sentence identifying the zeroth and first powers. In words:
    The scalar inclusion and augmentation are inverse linear
    identifications of the degree-zero power with the scalar field. *)
Lemma symmetric_zeroth_inclusionK : cancel symmetric_zeroth_inclusion symmetric_zeroth_inverse.
Proof.
move=> a; change (symmetric_augmentation V (symmetric_degree 0 (symmetric_scalar V a)) = a).
have h : homogeneous G 0 (symmetric_scalar V a).
  exact: (@homogeneousZ K E G 0 a (symmetric_unit V) (symmetric_unit_homogeneous V)).
by rewrite h symmetric_scalarK.
Qed.

(** Source for [symmetric_zeroth_inverseK]: Federer 1.9.1, p. 41,
    the sentence identifying the zeroth and first powers. In words:
    The scalar inclusion and augmentation are inverse linear
    identifications of the degree-zero power with the scalar field. *)
Lemma symmetric_zeroth_inverseK : cancel symmetric_zeroth_inverse symmetric_zeroth_inclusion.
Proof.
move=> x; apply/val_inj.
change (symmetric_degree 0 (symmetric_scalar V (symmetric_augmentation V (component_val x))) =
  component_val x).
rewrite -symmetric_degree_zero_reconstruction symmetric_degree_orthogonal eqxx.
exact: component_homogeneous.
Qed.

(** Source for [symmetric_first_inclusion]: Federer 1.9.1, p. 41,
    the sentence identifying the zeroth and first powers. In words:
    The generator inclusion and degree-one evaluation are inverse
    linear identifications of the degree-one power with V. *)
Definition symmetric_first_inclusion : {linear V -> symmetric_power V 1} :=
  linear_comp (GRing.Linear.clone _ _ _ _ (component G 1) _)
    (GRing.Linear.clone _ _ _ _ (@symmetric_generator K V) _).

(** Source for [symmetric_first_inverse]: Federer 1.9.1, p. 41,
    the sentence identifying the zeroth and first powers. In words:
    The generator inclusion and degree-one evaluation are inverse
    linear identifications of the degree-one power with V. *)
Definition symmetric_first_inverse : {linear symmetric_power V 1 -> V} :=
  linear_comp (symmetric_degree_one V)
    (GRing.Linear.clone _ _ _ _ (@component_val K E G 1) _).

(** Source for [symmetric_first_inclusionK]: Federer 1.9.1, p. 41,
    the sentence identifying the zeroth and first powers. In words:
    The generator inclusion and degree-one evaluation are inverse
    linear identifications of the degree-one power with V. *)
Lemma symmetric_first_inclusionK : cancel symmetric_first_inclusion symmetric_first_inverse.
Proof.
move=> v; change (symmetric_degree_one V (symmetric_degree 1 (symmetric_generator v)) = v).
by rewrite (symmetric_generator_homogeneous v) symmetric_generatorK.
Qed.

(** Source for [symmetric_first_inverseK]: Federer 1.9.1, p. 41,
    the sentence identifying the zeroth and first powers. In words:
    The generator inclusion and degree-one evaluation are inverse
    linear identifications of the degree-one power with V. *)
Lemma symmetric_first_inverseK : cancel symmetric_first_inverse symmetric_first_inclusion.
Proof.
move=> x; apply/val_inj.
change (symmetric_degree 1 (symmetric_generator (symmetric_degree_one V (component_val x))) =
  component_val x).
rewrite -symmetric_degree_one_reconstruction symmetric_degree_orthogonal eqxx.
exact: component_homogeneous.
Qed.
End LowPowers.
