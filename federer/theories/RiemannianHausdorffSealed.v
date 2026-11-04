(** Opaque original-distance Hausdorff measure, Federer
    (1969), 3.2.46, p. 281. The public interface exposes
    the independent covering and supremum laws only. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals
  classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct
  InnerMetric RiemannianTensorUP RiemannianMetricCarrier
  RiemannianHausdorffUP RiemannianHausdorffConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

Module Type RiemannianHausdorffSignature.
(** Source for [value]: the actual original-rho Hausdorff
    measure specified in 3.2.46, p. 281, for every real p>=0. *)
Parameter value : forall (R : realType) n A g
  (hg : @is_continuous_riemannian_tensor R n A g) (p : R) (hp : 0<=p),
  set (riemannian_metric_space hg) -> \bar R.
(** Source for [laws]: original-rho covering infima and
    their limiting supremum, supporting 3.2.46, p. 281. *)
Parameter laws : forall (R : realType) n A g
  (hg : @is_continuous_riemannian_tensor R n A g) (p : R) (hp : 0<=p),
  is_riemannian_hausdorff_measure hg p hp (@value R n A g hg p hp).
End RiemannianHausdorffSignature.

Module RiemannianHausdorff : RiemannianHausdorffSignature.
(** Source for [value]: witness chosen only from proved
    existence, hidden behind the laws of 3.2.46, p. 281. *)
Definition value (R : realType) n A g
    (hg : @is_continuous_riemannian_tensor R n A g) (p : R) (hp : 0<=p) :=
  projT1 (cid (@riemannian_hausdorff_measure_exists R n A g hg p hp)).
(** Source for [laws]: the chosen original-rho measure
    satisfies its independent laws, 3.2.46, p. 281. *)
Lemma laws (R : realType) n A g
    (hg : @is_continuous_riemannian_tensor R n A g) (p : R) (hp : 0<=p) :
  is_riemannian_hausdorff_measure hg p hp (@value R n A g hg p hp).
Proof. exact: projT2 (cid (@riemannian_hausdorff_measure_exists R n A g hg p hp)). Qed.
End RiemannianHausdorff.
