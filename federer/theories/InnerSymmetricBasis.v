(** Federer (1969), 1.10.5, p. 47: orthonormal monomials and positivity of
    the induced symmetric inner product. Finite-support reduction avoids
    assuming a basis of the whole ambient vector space. *)
From mathcomp Require Import all_boot all_order all_algebra.
From mathcomp.classical Require Import boolp.
From Federer Require Import TensorUP Bilinear BilinearPrecompose
  InnerProductUP InnerProductRestriction OrthonormalFamilies OrthonormalBilinearCoordinates
  LinearBasis GramSchmidt OrthonormalisationUP FiniteIndependence FiniteSpans
  FiniteSpanSpace ModuleQuotient SubspaceCarrier SymmetricAlgebra SymmetricGrading
  SymmetricMaps SymmetricPowerFunctor SymmetricMultiIndices SymmetricIndexBounds
  SymmetricMonomialBasis InnerSymmetric SymmetricFiniteSupport SymmetricFiniteReduction
  SymmetricNormalizedMonomials SymmetricMonomialGram.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [symmetric_orthonormal_family]: Federer 1.10.5,
    p. 47, the first displayed family: normalized degree-m monomials
    in any finite orthonormal family are orthonormal. Its finite span
    supplies the coordinate space in the proved transport calculation. *)
Theorem symmetric_orthonormal_family (R : rcfType) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B) n (e : 'I_n -> V)
    (ho : orthonormal_family B e) m :
  orthonormal_family (@symmetric_inner_form R V B hB m)
    (@symmetric_normalized_monomial R V n e m).
Proof.
have he := @orthonormal_independent R V B hB 'I_n e ho.
pose U := finite_span_vect he.
pose F := subspace_inclusion (finite_span_subspace e).
have hf : F \o finite_span_basis e = e.
  apply: funext=> i; exact: finite_span_basisE.
have hfo : orthonormal_family B (F \o finite_span_basis e) by rewrite hf.
have h := @symmetric_transported_orthonormal_monomials R U V B hB n
  (finite_span_basis e) (finite_span_basisP he) F hfo m.
by rewrite hf in h.
Qed.

(** Source for [symmetric_transport_inner_product]: Federer 1.10.5,
    p. 47, supporting positivity on a finite source space whose
    basis has orthonormal image. The normalized monomial basis gives
    a sum of coordinate squares, without requiring the image to span V. *)
Theorem symmetric_transport_inner_product (R : rcfType) (U V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B) n (e : 'I_n -> U)
    (he : is_basis e) (F : {linear U -> V})
    (ho : orthonormal_family B (F \o e)) m :
  is_inner_product (fun x y : symmetric_power U m =>
    symmetric_inner_form hB (symmetric_power_map F m x) (symmetric_power_map F m y)).
Proof.
have hb := bilinear_linear_precompose (@symmetric_inner_form_bilinear R V B hB m)
  (symmetric_power_map F m) (symmetric_power_map F m).
apply: (@orthonormal_basis_inner_product R (symmetric_power U m) _ hb
  (Finite.clone (symmetric_indices n m) _) (@symmetric_normalized_monomial R U n e m)).
- move=> a b; rewrite !symmetric_normalized_monomial_map.
  exact: (@symmetric_transported_orthonormal_monomials R U V B hB n e he F ho m a b).
- exact: symmetric_normalized_monomial_basis he m.
Qed.

(** Source for [finite_symmetric_inner_product]: Federer 1.10.5,
    p. 47, positivity in finite dimension: an orthonormal monomial
    basis makes the induced form an inner product. *)
Theorem finite_symmetric_inner_product (R : rcfType) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B) n (e : 'I_n -> V)
    (he : is_basis e) (ho : orthonormal_family B e) m :
  is_inner_product (@symmetric_inner_form R V B hB m).
Proof.
apply: (@orthonormal_basis_inner_product R (symmetric_power V m)
  _ (@symmetric_inner_form_bilinear R V B hB m)
  (Finite.clone (symmetric_indices n m) _) (@symmetric_normalized_monomial R V n e m)).
- exact: (@symmetric_orthonormal_family R V B hB n e ho m).
- exact: symmetric_normalized_monomial_basis he m.
Qed.
