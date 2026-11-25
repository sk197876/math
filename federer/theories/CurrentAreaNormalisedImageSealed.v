(** Federer (1969), 4.1.25, p. 383: opaque access
    to the uniquely specified normalized differential
    summand. Only its original partial-graph law is
    public; the chosen existence witness stays hidden. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct
  ExteriorGrading PartialFunctionUP CurrentAreaNormalisedImageUP
  CurrentAreaNormalisedImageExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Type CurrentAreaNormalisedImageSignature.
(** Source for [value]: the original partial normalized
    differential summand of Federer 4.1.25, p. 383. *)
Parameter value : forall (R : realType) m n
  (f : R_n R m -> R_n R n)
  (xi : R_n R m -> exterior_power (R_n R m) m),
  partial_function (R_n R m) (exterior_power (R_n R n) m).
(** Source for [laws]: the exact original partial
    graph of the summand in Federer 4.1.25, p. 383. *)
Parameter laws : forall (R : realType) m n f xi,
  @is_current_area_normalised_image R m n f xi (@value R m n f xi).
End CurrentAreaNormalisedImageSignature.

Module CurrentAreaNormalisedImage : CurrentAreaNormalisedImageSignature.
(** Source for [value]: select the independently proved
    existence witness for Federer 4.1.25, p. 383. *)
Definition value (R : realType) m n f xi :=
  projT1 (cid (@current_area_normalised_image_exists R m n f xi)).
(** Source for [laws]: the selected witness satisfies
    precisely the original graph, Federer 4.1.25, p. 383. *)
Lemma laws (R : realType) m n f xi :
  @is_current_area_normalised_image R m n f xi (@value R m n f xi).
Proof. exact: projT2 (cid (@current_area_normalised_image_exists R m n f xi)). Qed.
End CurrentAreaNormalisedImage.
