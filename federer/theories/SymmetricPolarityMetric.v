(** Federer (1969), 1.10.6, pp. 48-49: the scalar symmetric form inner
    product makes the polarity of 1.10.5 an orthogonal isomorphism. The norm
    on vector-valued forms is already specified by the method of 1.7.9; the
    proof below verifies that its scalar specialization has exactly this
    property. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InnerProductUP InnerNorm InnerSymmetric InnerSymmetricPositivity
  InnerSymmetricBasis SymmetricAlgebra SymmetricGrading SymmetricForms SymmetricPairing
  SymmetricNormalizedMonomials SymmetricFormInner SymmetricFormInnerCoordinates
  ScalarInnerProduct SymmetricPolarityIsomorphism LinearBasis OrthonormalFamilies
  OrthonormalBilinearCoordinates OrthonormalParseval GramSchmidt OrthonormalisationUP
  SymmetricMultiIndices SymmetricIndexBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [symmetric_polarity_isometry]: Federer 1.10.6,
    pp. 48-49, the opening requirement: the scalar form inner
    product preserves the inner product of symmetric vectors under gamma_m.
    The finite basis supplied to the interface need not be orthonormal. *)
Theorem symmetric_polarity_isometry (R : rcfType) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B)
    n (e : 'I_n -> V) (he : is_basis e) m (x y : symmetric_power V m) :
  symmetric_form_inner hB (scalar_inner_productP R) he m
    (inner_symmetric_form hB x) (inner_symmetric_form hB y) =
      symmetric_inner_form hB x y.
Proof.
have [d [hd hdo]] := orthonormal_basis_exists hB he.
have ho := orthonormalisation_orthonormal hdo.
have hm := symmetric_normalized_monomial_basis hd m.
have hmo := @symmetric_orthonormal_family R V B hB n d ho m.
rewrite (@symmetric_form_inner_orthonormal_sum R V R^o B
  (fun a b : R => a*b) hB (scalar_inner_productP R) n e he n d hd ho m).
rewrite (@orthonormal_basis_bilinear_coordinates R (symmetric_power V m)
  _ (inner_bilinear (@symmetric_inner_productP R V B hB m))
  (Finite.clone (symmetric_indices n m) _) _ hmo hm x y).
apply: eq_bigr=> a _.
rewrite !(@orthonormal_basis_inner_coordinate R (symmetric_power V m)
  _ (@symmetric_inner_productP R V B hB m)
  (Finite.clone (symmetric_indices n m) _) _ hmo hm).
change (symmetric_inner_form hB (symmetric_normalized_monomial d a) x *
  symmetric_inner_form hB (symmetric_normalized_monomial d a) y =
  symmetric_inner_form hB x (symmetric_normalized_monomial d a) *
  symmetric_inner_form hB y (symmetric_normalized_monomial d a)).
by rewrite (symmetric_inner_symmetric hB _ x) (symmetric_inner_symmetric hB _ y).
Qed.

(** Source for [symmetric_polarity_norm]: Federer 1.10.6,
    pp. 48-49, the polarity preserves lengths as a consequence
    of the defining inner product isometry, in every degree. *)
Theorem symmetric_polarity_norm (R : rcfType) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B)
    n (e : 'I_n -> V) (he : is_basis e) m (x : symmetric_power V m) :
  symmetric_form_norm hB (scalar_inner_productP R) he m (inner_symmetric_form hB x) =
    inner_norm (@symmetric_inner_productP R V B hB m) x.
Proof.
apply: inner_norm_value; first exact: inner_norm_nonnegative.
by rewrite inner_norm_sqr symmetric_polarity_isometry.
Qed.
