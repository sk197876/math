(** Opaque actual discriminant-density interface for Federer (1969),
    3.2.46, pp. 281--282. The implementation supplies existence only. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import GrassmannAbbreviations RealMetricBackground
  PartialFunctionUP RiemannianTensorUP RiemannianVolumeDensityUP
  RiemannianVolumeDensityConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Type RiemannianVolumeDensitySignature.
(** Source for [value]: the function sqrt(discr g) in Federer
    3.2.46, pp. 281--282, accessed through its exact graph laws. *)
Parameter value : forall (R : realType) n A g,
  @is_continuous_riemannian_tensor R n A g ->
    partial_function (R_n R n) (real_line_metric R).
(** Source for [laws]: the original-domain graph specification,
    Federer 3.2.46, pp. 281--282. *)
Parameter laws : forall (R : realType) n A g
  (hg : @is_continuous_riemannian_tensor R n A g),
  is_riemannian_volume_density hg (@value R n A g hg).
End RiemannianVolumeDensitySignature.

Module RiemannianVolumeDensity : RiemannianVolumeDensitySignature.
(** Source for [value]: selection from the proved independent
    graph existence, Federer 3.2.46, pp. 281--282. *)
Definition value (R : realType) n A g
    (hg : @is_continuous_riemannian_tensor R n A g) :=
  projT1 (cid (riemannian_volume_density_exists hg)).
(** Source for [laws]: the opaque value satisfies its original
    graph laws, Federer 3.2.46, pp. 281--282. *)
Lemma laws (R : realType) n A g
    (hg : @is_continuous_riemannian_tensor R n A g) :
  is_riemannian_volume_density hg (@value R n A g hg).
Proof. exact: projT2 (cid (riemannian_volume_density_exists hg)). Qed.
End RiemannianVolumeDensity.
