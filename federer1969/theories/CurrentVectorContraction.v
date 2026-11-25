(** Federer (1969), 4.1.7, p. 356: the
    original contraction of a multivector field
    by a covector field in the last
    two displayed identities. The actual operation
    is the characteristic left interior from
    1.5.1, pp. 21–22. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import BoundedHom HomogeneousHom GradedComponents Hom TensorUP Bilinear ExteriorGrading ExteriorHomogeneousProducts
  AlternatingForms AlternatingIsomorphism AlternatingPairing AlternatingSum AlternatingProduct
  ScalarCoefficients LeftInterior ComassWedgeSymmetry.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section CurrentVectorContraction.
Variable K:fieldType.
Hypothesis h2:(1+1:K)!=0.
Variable V:lmodType K.
Variables k p:nat.

(** Source for [current_vector_contraction]: the
    original (k+p)-vector contracted by a
    k-covector, supporting Federer 4.1.7,
    p. 356. Its output has degree p. *)
Definition current_vector_contraction (xi:exterior_power V (k+p)) (phi:A_m V K^o k):
    exterior_power V p:=
  exterior_reindex (addKn k p) (left_interior h2 (leq_addr p k) xi phi).

(** Source for [current_vector_contraction_bilinear]:
    the original contraction is bilinear,
    supporting Federer 4.1.7, p. 356,
    by the earlier left-interior laws. *)
Lemma current_vector_contraction_bilinear:bilinear current_vector_contraction.
Proof.
split=>z c a b;rewrite /current_vector_contraction.
- rewrite ((@left_interior_bilinear K h2 V k (k+p) (leq_addr p k)).1 z) linearP;by [].
- rewrite ((@left_interior_bilinear K h2 V k (k+p) (leq_addr p k)).2 z) linearP;by [].
Qed.

(** Source for [current_vector_contraction_pairing]:
    the original pairing of xi contracted
    phi with psi is the pairing of
    xi with phi wedge psi, supporting
    Federer 4.1.7, p. 356. All
    equal-degree identifications preserve the actual
    full exterior-algebra values. *)
Lemma current_vector_contraction_pairing xi phi (psi:A_m V K^o p):
  pairing (current_vector_contraction xi phi) psi=
    form_include (form_wedge h2 (scalar_bilinear K) phi psi) (component_val xi).
Proof.
pose b:=form_reindex (esym (addKn k p)) psi.
have h:=@left_interior_characteristic K h2 V k (k+p) (leq_addr p k) xi phi b.
change (form_include b (component_val (left_interior h2 (leq_addr p k) xi phi))=
  form_include (form_reindex (subnKC (leq_addr p k))
    (form_wedge h2 (scalar_bilinear K) phi b)) (component_val xi)) in h.
have hB:form_include b=form_include psi:=
  @form_reindex_include K V p ((k+p)-k) (esym (addKn k p)) psi.
have hW:form_include (form_wedge h2 (scalar_bilinear K) phi b)=
    form_include (form_wedge h2 (scalar_bilinear K) phi psi).
  apply:(eq_trans (@form_wedge_include K h2 V K^o (fun a b:K^o=>a*b)
    (scalar_bilinear K) k ((k+p)-k) phi b)).
  apply:(eq_trans (congr1 (fun z=>alternating_wedge h2 (scalar_bilinear K)
    (form_include phi) z) hB)).
  exact:esym (@form_wedge_include K h2 V K^o (fun a b:K^o=>a*b)
    (scalar_bilinear K) k p phi psi).
have hRight:=congr1 (fun z:A_star V K^o=>z (component_val xi))
  (@form_reindex_include K V (k+((k+p)-k)) (k+p)
    (subnKC (leq_addr p k)) (form_wedge h2 (scalar_bilinear K) phi b)).
have hPair:=eq_trans h (eq_trans hRight (congr1 (fun z:A_star V K^o=>z (component_val xi)) hW)).
have hLeft:=congr1 (fun z:A_star V K^o=>z (component_val (left_interior h2 (leq_addr p k) xi phi))) hB.
change (form_include psi (component_val (current_vector_contraction xi phi))=
  form_include (form_wedge h2 (scalar_bilinear K) phi psi) (component_val xi)).
apply:(eq_trans (congr1 (fun z=>form_include psi z)
  (@exterior_reindexE K V ((k+p)-k) p (addKn k p)
    (left_interior h2 (leq_addr p k) xi phi)))).
exact:eq_trans (esym hLeft) hPair.
Qed.
End CurrentVectorContraction.
