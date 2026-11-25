(** Federer (1969), 4.1.7, p. 356: multiplication
    of an original form by a zero-covector
    is scalar multiplication. This supports the
    current coordinate expansion and retains the
    original equal-degree identifications. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import BoundedHom HomogeneousHom GradedComponents Hom TensorUP Bilinear AlternatingForms AlternatingZero AlternatingSum
  AlternatingProduct ScalarCoefficients ExteriorHomogeneousProducts ComassWedgeSymmetry
  ZeroFormScalarProduct ExteriorGrading CurrentVectorFormInterior CurrentInteriorPairing.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [current_form_wedge_zero_scalar]:
    the original right zero-degree factor acts
    by its scalar value, supporting Federer
    4.1.7, p. 356, from the
    preceding graded commutation and unit laws. *)
Lemma current_form_wedge_zero_scalar (K:fieldType) (h2:(1+1:K)!=0)
    (V:lmodType K) m (phi:A_m V K^o m) (c:K):
  form_reindex (addn0 m) (form_wedge h2 (scalar_bilinear K) phi (@zero_form K V K^o c))=c*:phi.
Proof.
have hSwap:=@form_wedge_reindex_swap K h2 V m 0 phi (@zero_form K V K^o c).
rewrite muln0 expr0 scale1r in hSwap.
apply:(can_inj (@form_includeK K V K^o m)).
rewrite form_reindex_include linearZ hSwap form_reindex_include.
by rewrite original_zero_form_wedge_scalar linearZ.
Qed.

(** Source for [current_form_interior_scalar_product]:
    multiplication by the scalar contraction gives
    the actual coordinate pairing times the
    original form, supporting Federer 4.1.7,
    p. 356. *)
Lemma current_form_interior_scalar_product (K:fieldType) (h2:(1+1:K)!=0)
    (V:lmodType K) m (phi:A_m V K^o m)
    (xi:exterior_power V m) (psi:A_m V K^o (m+0)):
  form_reindex (addn0 m)
    (form_wedge h2 (scalar_bilinear K) phi (current_vector_form_interior xi psi))=
      (form_include psi (component_val xi):K)*:phi.
Proof.
rewrite -{1}(zero_form_valueK (current_vector_form_interior xi psi)).
rewrite current_vector_interior_scalar_value.
exact:current_form_wedge_zero_scalar.
Qed.
