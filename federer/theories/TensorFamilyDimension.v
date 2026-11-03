(** Federer 1.1.2, p. 10, dimension display: finite dimensions multiply
    for any number of tensor factors, including a zero-dimensional factor.
    The empty product is one, as required by the empty tensor family. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import TensorFamily TensorFamilyBasis LinearBasis FiniteDimension.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.

Section Dimension.
Variable K : fieldType.
Variable n : nat.
Variable V : 'I_n -> lmodType K.
Variable J : 'I_n -> finType.
Variable e : forall i, J i -> V i.
Arguments e i _ : clear implicits.
Hypothesis he : forall i, is_basis (e i).
Variable T : lmodType K.
Variable mu : {dffun forall i, V i} -> T.
Hypothesis hmu : is_tensor_product_family mu.

(** Source for [tensor_family_finite_space]: Federer 1.1.2, p. 10;
    the original abstract tensor space equipped with its proved finite
    product basis. This installs a structure, not a replacement space. *)
Definition tensor_family_finite_space : vectType K :=
  @finite_basis_vect K (Finite.clone {dffun forall i, J i} _) T
    (@tensor_family_basis K n V (fun i => (Choice.clone (J i) _)) e T mu)
    (@tensor_family_basisP K n V (fun i => (Choice.clone (J i) _)) e he T mu hmu).

(** Source for [tensor_family_dimension]: Federer 1.1.2, p. 10,
    dim(V_1 tensor ... tensor V_n) is the product of the factor dimensions.
    Each supplied finite basis has cardinality equal to its dimension. *)
Theorem tensor_family_dimension : dim tensor_family_finite_space =
    foldr muln 1 [seq #|J i| | i : 'I_n].
Proof.
by rewrite /tensor_family_finite_space finite_basis_dimension card_dep_ffun.
Qed.
End Dimension.
