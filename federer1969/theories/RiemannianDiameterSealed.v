(** Opaque diameter for original rho, supporting Federer
    (1969), 3.2.46, p. 281. The implementation is hidden
    behind the independent supremum laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals
  classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct
  InnerMetric RiemannianTensorUP RiemannianMetricCarrier
  RiemannianDiameterUP RiemannianDiameterConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Type RiemannianDiameterSignature.
(** Source for [value]: original-distance diameter of actual
    chart subsets, supporting 3.2.46, p. 281. *)
Parameter value : forall (R : realType) n A g
  (hg : @is_continuous_riemannian_tensor R n A g),
  set (riemannian_metric_space hg) -> \bar R.
(** Source for [laws]: independent diameter supremum laws
    supporting 3.2.46, p. 281. *)
Parameter laws : forall (R : realType) n A g
  (hg : @is_continuous_riemannian_tensor R n A g) S,
  @is_riemannian_diameter R n A g hg S (@value R n A g hg S).
End RiemannianDiameterSignature.

Module RiemannianDiameter : RiemannianDiameterSignature.
(** Source for [value]: opaque witness selected only after
    proving existence, supporting 3.2.46, p. 281. *)
Definition value (R : realType) n A g
    (hg : @is_continuous_riemannian_tensor R n A g) S :=
  projT1 (cid (@riemannian_diameter_exists R n A g hg S)).
(** Source for [laws]: the chosen diameter satisfies its
    independent laws, supporting 3.2.46, p. 281. *)
Lemma laws (R : realType) n A g
    (hg : @is_continuous_riemannian_tensor R n A g) S :
  @is_riemannian_diameter R n A g hg S (@value R n A g hg S).
Proof. exact: projT2 (cid (@riemannian_diameter_exists R n A g hg S)). Qed.
End RiemannianDiameter.
