(** General normed-space background for Federer (1969), 4.1.14,
    p. 371: the bounded extension exposes its independent agreement
    and sharp bound laws. The proved Cauchy-filter construction
    remains hidden behind an opaque module signature. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric CompleteMetricUP
  BanachDenseLinearExtensionUP BanachDenseLinearExtensionExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Module Type BanachDenseLinearExtensionSignature.
(** Source for [value]: bounded linear extension in the dense
    normal-to-flat step of Federer 4.1.14, p. 371. *)
Parameter value : forall (R : realType) (A V W : lmodType R)
  (NV : V -> R) (NW : W -> R), is_real_norm NV ->
  forall hNW : is_real_norm NW,
  is_complete_metric_space (real_norm_metric_space hNW) ->
  forall (i : Hom A V) (F : Hom A W) (C : R), 0<=C ->
  is_norm_dense_linear_image NV i ->
  (forall a, NW (F a)<=C*NV (i a)) -> Hom V W.
(** Source for [laws]: original agreement and bound of the
    extension in Federer 4.1.14, p. 371. *)
Parameter laws : forall (R : realType) (A V W : lmodType R)
  (NV : V -> R) (NW : W -> R) (hNV : is_real_norm NV)
  (hNW : is_real_norm NW)
  (hW : is_complete_metric_space (real_norm_metric_space hNW))
  (i : Hom A V) (F : Hom A W) (C : R) (hC : 0<=C)
  (hDense : is_norm_dense_linear_image NV i)
  (hBound : forall a, NW (F a)<=C*NV (i a)),
  is_bounded_dense_linear_extension NV NW i F C
    (@value R A V W NV NW hNV hNW hW i F C hC hDense hBound).
End BanachDenseLinearExtensionSignature.
Module BanachDenseLinearExtension : BanachDenseLinearExtensionSignature.
(** Source for [value]: select the separately proved extension
    witness for Federer 4.1.14, p. 371. *)
Definition value (R : realType) (A V W : lmodType R)
  (NV : V -> R) (NW : W -> R) (hNV : is_real_norm NV)
  (hNW : is_real_norm NW)
  (hW : is_complete_metric_space (real_norm_metric_space hNW))
  (i : Hom A V) (F : Hom A W) (C : R) (hC : 0<=C)
  (hDense : is_norm_dense_linear_image NV i)
  (hBound : forall a, NW (F a)<=C*NV (i a)) : Hom V W :=
  projT1 (cid (@bounded_dense_linear_extension_exists R A V W NV NW
    hNV hNW hW i F C hC hDense hBound)).
(** Source for [laws]: verify the opaque selected extension
    against its independent laws, Federer 4.1.14, p. 371. *)
Lemma laws (R : realType) (A V W : lmodType R)
  (NV : V -> R) (NW : W -> R) (hNV : is_real_norm NV)
  (hNW : is_real_norm NW)
  (hW : is_complete_metric_space (real_norm_metric_space hNW))
  (i : Hom A V) (F : Hom A W) (C : R) (hC : 0<=C)
  (hDense : is_norm_dense_linear_image NV i)
  (hBound : forall a, NW (F a)<=C*NV (i a)) :
  is_bounded_dense_linear_extension NV NW i F C
    (@value R A V W NV NW hNV hNW hW i F C hC hDense hBound).
Proof.
exact: projT2 (cid (@bounded_dense_linear_extension_exists R A V W NV NW
  hNV hNW hW i F C hC hDense hBound)).
Qed.
End BanachDenseLinearExtension.
