(** Federer (1969), 3.4.12, p. 339, extending 3.4.8(1),(8),
    pp. 326, 329: the original coordinate basis reconstructs
    each vector. Reuse dual-basis uniqueness and the already
    proved finite basis expansion over the original field. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import Hom TensorUP LinearBasis Annihilator FiniteDualDimension DualityAnnihilator FiniteCoordinates FieldCoordinateFunctional.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [field_coordinate_expansion]: original finite
    coordinate reconstruction, supporting 3.4.12, p. 339. *)
Lemma field_coordinate_expansion (K:fieldType) n (x:coordinate_space K n):
  \sum_(i<n) x i*:@coordinate_basis K n i=x.
Proof.
have hDual i k:@field_coordinate_functional K n i (@coordinate_basis K n k)=if i==k then 1 else 0.
  by rewrite /field_coordinate_functional /= /coordinate_basis ffunE eq_sym.
have hOmega i:@field_coordinate_functional K n i=dual_basis (@coordinate_basisP K n) i.
  exact:(@biorthogonal_basis_unique K (coordinate_space K n) n (@coordinate_basis K n)
    (@coordinate_basisP K n) (fun j=>@field_coordinate_functional K n j) hDual i).
rewrite {2}(basis_vector_expansion (@coordinate_basisP K n) x).
apply:eq_bigr=>i _;by rewrite -hOmega.
Qed.
