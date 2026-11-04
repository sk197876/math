(** Public diameter of the original curve distance rho,
    supporting Federer (1969), 3.2.46, p. 281. Capping
    is a separate representation, not this definition. *)
From mathcomp Require Import all_boot all_order all_algebra reals
  classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct
  InnerMetric RiemannianTensorUP RiemannianMetricCarrier
  RiemannianDiameterUP RiemannianDiameterSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [riemannian_diameter]: the opaque original
    rho diameter in Hausdorff coverings, 3.2.46, p. 281. *)
Definition riemannian_diameter (R : realType) n A g
    (hg : @is_continuous_riemannian_tensor R n A g) S :=
  @RiemannianDiameter.value R n A g hg S.
Arguments riemannian_diameter {R n A g} hg S.

(** Source for [riemannian_diameter_specification]: the
    original diameter satisfies its independent supremum
    laws, supporting 3.2.46, p. 281. *)
Lemma riemannian_diameter_specification (R : realType) n A g
    (hg : @is_continuous_riemannian_tensor R n A g) S :
  @is_riemannian_diameter R n A g hg S (riemannian_diameter hg S).
Proof. exact (@RiemannianDiameter.laws R n A g hg S). Qed.
Arguments riemannian_diameter_specification {R n A g} hg S.
