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
From Federer Require Import InnerSymmetricBasis.

(** Source for [symmetric_finite_subspace_inner_product]: Federer 1.10.5,
    p. 47, supporting coordinate-square argument on any finite
    subspace. Gram-Schmidt supplies the required orthonormal source basis. *)
Lemma symmetric_finite_subspace_inner_product (R : rcfType) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B) n (e : 'I_n -> V)
    (he : finite_independent e) m :
  is_inner_product (fun x y : symmetric_power (finite_span_vect he) m =>
    symmetric_inner_form hB
      (symmetric_power_map (subspace_inclusion (finite_span_subspace e)) m x)
      (symmetric_power_map (subspace_inclusion (finite_span_subspace e)) m y)).
Proof.
pose S := finite_span_subspace e.
pose C := @restricted_inner_product R V B S.
have hC := @restricted_inner_productP R V B hB S.
have [d [hd hdo]] := @orthonormal_basis_exists R (finite_span_vect he) C hC n
  (finite_span_basis e) (finite_span_basisP he).
apply: (@symmetric_transport_inner_product R (finite_span_vect he) V B hB n d hd
  (subspace_inclusion S)).
exact: orthonormalisation_orthonormal hdo.
Qed.

(** Source for [symmetric_inner_symmetric]: Federer 1.10.5,
    p. 47, symmetry of the induced form in arbitrary dimension.
    Both arguments lie in one finite subspace, where the monomial
    Gram matrix is symmetric. *)
Theorem symmetric_inner_symmetric (R : rcfType) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B) m (x y : symmetric_power V m) :
  symmetric_inner_form hB x y = symmetric_inner_form hB y x.
Proof.
have [n [e [he [a [b [ha hb]]]]]] := symmetric_pair_finite_reduction x y.
have hE := @symmetric_finite_subspace_inner_product R V B hB n e he m.
rewrite -ha -hb.
exact: inner_symmetric hE a b.
Qed.

(** Source for [symmetric_inner_positive]: Federer 1.10.5,
    p. 47, strict positivity precisely for nonzero symmetric vectors.
    The coordinate-square argument applies after finite-support reduction;
    injectivity of the induced inclusion transfers nonvanishing. *)
Theorem symmetric_inner_positive (R : rcfType) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B) m (x : symmetric_power V m) :
  (0 < symmetric_inner_form hB x x) = (x != 0).
Proof.
have [n [e [he [a [b [ha hb]]]]]] := symmetric_pair_finite_reduction x x.
have hE := @symmetric_finite_subspace_inner_product R V B hB n e he m.
rewrite -ha (inner_positive hE).
have hin := @symmetric_power_subspace_injective R V (finite_span_subspace e) m.
by rewrite -(linear0 (symmetric_power_map (subspace_inclusion (finite_span_subspace e)) m)) (inj_eq hin).
Qed.

(** Source for [symmetric_inner_productP]: Federer 1.10.5,
    p. 47, the constructed bilinear function is an inner product
    on every symmetric power, including degree zero and arbitrary
    ambient dimension. All three defining laws have been proved. *)
Theorem symmetric_inner_productP (R : rcfType) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B) m :
  is_inner_product (@symmetric_inner_form R V B hB m).
Proof.
constructor.
- exact: symmetric_inner_form_bilinear.
- exact: symmetric_inner_symmetric.
- exact: symmetric_inner_positive.
Qed.
