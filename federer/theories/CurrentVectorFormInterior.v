(** Federer (1969), 4.1.7, pp. 355–356: the
    actual multivector interior operation that defines
    multiplication of currents by smooth vector fields. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import Hom TensorUP Bilinear ExteriorGrading AlternatingForms
  ExteriorHomogeneousProducts RightInterior.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section CurrentVectorFormInterior.
Variable K:fieldType.
Variable V:lmodType K.
Variables k p:nat.

(** Source for [current_vector_form_interior]: the
    original right interior of a k-vector and a
    (k+p)-covector, with its exact output degree,
    supporting Federer 4.1.7, pp. 355–356. *)
Definition current_vector_form_interior (xi:exterior_power V k) (phi:A_m V K^o (k+p)):
    A_m V K^o p:=
  form_reindex (addKn k p) (right_interior (leq_addr p k) xi phi).

(** Source for [current_vector_form_interior_bilinear]:
    original bilinearity, supporting Federer 4.1.7,
    pp. 355–356, by 1.5.1, p. 21. *)
Lemma current_vector_form_interior_bilinear:bilinear current_vector_form_interior.
Proof.
split=>z c a b; rewrite /current_vector_form_interior.
- rewrite ((@right_interior_bilinear K V K^o k (k+p) (leq_addr p k)).1 z) linearP; by [].
- rewrite ((@right_interior_bilinear K V K^o k (k+p) (leq_addr p k)).2 z) linearP; by [].
Qed.
End CurrentVectorFormInterior.
