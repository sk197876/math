(** Federer (1969), 1.7.9, p. 35: the degree-one dual of an orthogonal
    automorphism is orthogonal. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InnerProductUP InnerDual InnerPolarity InnerPolaritySurjection
  OrthogonalMaps OrthogonalFinite AdjointUP ExteriorAdjoint
  AlternatingDual AlternatingCoordinates OneFormLinear LinearBasis Hom.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [one_covector_orthogonal]: Federer 1.7.9,
    p. 35, the dual of a finite-dimensional orthogonal endomorphism
    is orthogonal for the dual inner product. Inverse existence
    follows from finite dimension, rather than being an extra hypothesis. *)
Theorem one_covector_orthogonal (R : rcfType) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B)
    n (e : 'I_n -> V) (he : is_basis e)
    (s : {linear V -> V}) (hs : is_orthogonal_map B B s) :
  is_orthogonal_map (inner_dual_product hB he) (inner_dual_product hB he)
    (GRing.Linear.clone _ _ _ _ (@A_m_dual R V V R^o s 1) _).
Proof.
have [a [hsa [has ha]]] := orthogonal_endomorphism_inverse_exists hB he hs.
have had : is_adjoint B B s a by move=> x y; rewrite -hs has.
move=> alpha beta.
have [x <-] := @inner_polarity_surjective R V B hB n e he alpha.
have [y <-] := @inner_polarity_surjective R V B hB n e he beta.
change (inner_dual_product hB he (A_m_dual s (inner_polarity hB x))
  (A_m_dual s (inner_polarity hB y)) =
  inner_dual_product hB he (inner_polarity hB x) (inner_polarity hB y)).
by rewrite !(@adjoint_polarity_pullback R V V B B hB hB s a had)
  !inner_dual_polarityE ha.
Qed.

(** Source for [one_covector_dual_cancel]: Federer 1.7.9,
    p. 35, supporting inverse law for the degree-one dual;
    a right inverse on vectors becomes a left inverse on covectors. *)
Theorem one_covector_dual_cancel (R : fieldType) (V : lmodType R)
    (s a : {linear V -> V}) : cancel a s ->
  cancel (@A_m_dual R V V R^o s 1) (@A_m_dual R V V R^o a 1).
Proof.
move=> ha alpha; apply: one_hom_injective; apply: Hom.hom_ext => x.
rewrite !one_homE !A_m_dualE.
have hm (f : {linear V -> V}) v : map_tuple f [tuple v] = [tuple f v] by apply: val_inj.
by rewrite !hm ha.
Qed.

(** Source for [one_covector_orthogonal_bijective]: Federer
    1.7.9, p. 35, the dual orthogonal map is an automorphism. *)
Theorem one_covector_orthogonal_bijective (R : rcfType) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B)
    n (e : 'I_n -> V) (he : is_basis e)
    (s : {linear V -> V}) (hs : is_orthogonal_map B B s) :
  bijective (@A_m_dual R V V R^o s 1).
Proof.
have [a [hsa [has ha]]] := orthogonal_endomorphism_inverse_exists hB he hs.
exists (@A_m_dual R V V R^o a 1); exact: one_covector_dual_cancel.
Qed.
