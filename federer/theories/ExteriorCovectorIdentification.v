(** Federer (1969), 1.7.5, p. 33: compatibility of the induced metrics with
    the canonical covector identification. All metrics below are specified
    by their laws; no choices of coordinates enter the assertion. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InnerProductUP InnerExterior InnerExteriorPositivity
  InnerExteriorPolarity InnerExteriorIsomorphism InnerDualUP InnerPolarity
  ExteriorCovectorInnerUP ExteriorCovectorInner LinearBasis
  ExteriorGrading AlternatingCoordinates AlternatingIsomorphism OneFormIdentification Hom.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [exterior_covector_identification_orthogonal]:
    Federer 1.7.5, p. 33, the canonical isomorphism from
    m-covectors to one-forms on m-vectors is orthogonal for the
    metrics making gamma_m and beta_m orthogonal, respectively. *)
Theorem exterior_covector_identification_orthogonal (R : rcfType)
    (h2 : (1+1 : R) != 0) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B)
    n (e : 'I_n -> V) (he : is_basis e) m
    (D : A_m V R^o m -> A_m V R^o m -> R)
    (E : A_m (exterior_power V m) R^o 1 -> A_m (exterior_power V m) R^o 1 -> R) :
  is_exterior_covector_inner_product h2 hB D ->
  is_dual_inner_product (@exterior_inner_productP R h2 V B hB m) E ->
  forall a b, E (one_form (form_to_hom a)) (one_form (form_to_hom b)) = D a b.
Proof.
move=> hD hE a b.
have [g [hfg hgf]] := @inner_exterior_inverse_exists R h2 V B hB n e he m.
rewrite -(hgf a) -(hgf b) -!exterior_polarity_identification.
rewrite /exterior_polarity (dual_inner_product_polarity hE).
symmetry; exact (@exterior_covector_inner_isometry R h2 V B hB m D hD (g a) (g b)).
Qed.

(** Source for [exterior_covector_inner_basis_independent]:
    Federer 1.7.5, p. 33, supporting intrinsicness: uniqueness
    makes the covector metric independent of the finite basis
    used to establish existence. *)
Theorem exterior_covector_inner_basis_independent (R : rcfType)
    (h2 : (1+1 : R) != 0) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B)
    n (e : 'I_n -> V) (he : is_basis e)
    k (f : 'I_k -> V) (hf : is_basis f) m (a b : A_m V R^o m) :
  exterior_covector_inner h2 hB he a b = exterior_covector_inner h2 hB hf a b.
Proof.
apply: (@exterior_covector_inner_unique R h2 V B hB m).
- move=> c; have [g [hfg hgf]] := @inner_exterior_inverse_exists R h2 V B hB n e he m.
  by exists (g c).
- exact: exterior_covector_innerP.
- exact: exterior_covector_innerP.
Qed.
