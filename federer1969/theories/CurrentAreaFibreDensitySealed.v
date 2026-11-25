(** Federer (1969), 4.1.25, p. 383: opaque
    access to the target density specified by the
    original full-fibre vector sum. Its graph law
    exposes neither an arbitrary extension nor an
    off-domain coefficient. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct
  ExteriorGrading PartialFunctionUP CurrentAreaFibreSumUP
  CurrentAreaFibreDensityUP CurrentAreaFibreDensityExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

Module Type CurrentAreaFibreDensitySignature.
(** Source for [value]: the original partial fibre
    density of Federer 4.1.25, p. 383. *)
Parameter value : forall (R : realType) (h2 : (1+1 : R) != 0)
  (X : choiceType) n m (f : X -> R_n R n)
  (u : partial_function X (exterior_power (R_n R n) m)),
  partial_function (R_n R n) (exterior_power (R_n R n) m).
(** Source for [laws]: the exact original graph of
    the fibre density in Federer 4.1.25, p. 383. *)
Parameter laws : forall R h2 X n m f u,
  @is_current_area_fibre_density R X n m f u (@value R h2 X n m f u).
End CurrentAreaFibreDensitySignature.

Module CurrentAreaFibreDensity : CurrentAreaFibreDensitySignature.
(** Source for [value]: choose the independently proved
    witness of the original specification, Federer 4.1.25,
    p. 383. The choice remains hidden by the signature. *)
Definition value (R : realType) h2 (X : choiceType) n m f u :=
  projT1 (cid (@current_area_fibre_density_exists R h2 X n m f u)).
(** Source for [laws]: the chosen witness has the
    exact full-fibre graph in Federer 4.1.25, p. 383. *)
Lemma laws R h2 X n m f u :
  @is_current_area_fibre_density R X n m f u (@value R h2 X n m f u).
Proof. exact: projT2 (cid (@current_area_fibre_density_exists R h2 X n m f u)). Qed.
End CurrentAreaFibreDensity.
