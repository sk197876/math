(** Opaque polarity witness for Federer (1969), 3.1.1, p. 209.
    Only the linear map and its pairing law are exposed. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp.
From Federer Require Import Hom InnerProductUP InnerNorm RealNormUP
  ContinuousDualUP ContinuousPolarityUP ContinuousPolarityConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Module Type ContinuousPolaritySignature.
(** Source for [map]: the polarity into X* in Federer 3.1.1, p. 209. *)
Parameter map : forall (R : realType) (V D : lmodType R)
  (B : V -> V -> R) (hB : is_inner_product B)
  (hN : is_real_norm (inner_norm hB))
  (evaluation : Hom D (Hom V R^o)) (DN : D -> R),
  is_continuous_dual hN evaluation DN -> Hom V D.
(** Source for [laws]: the defining pairing of the polarity in
    Federer 3.1.1, p. 209. *)
Parameter laws : forall (R : realType) (V D : lmodType R)
  (B : V -> V -> R) (hB : is_inner_product B)
  (hN : is_real_norm (inner_norm hB))
  (evaluation : Hom D (Hom V R^o)) (DN : D -> R)
  (hD : is_continuous_dual hN evaluation DN),
  is_continuous_polarity B evaluation (@map R V D B hB hN evaluation DN hD).
End ContinuousPolaritySignature.
Module ContinuousPolarity : ContinuousPolaritySignature.
(** Source for [map]: selection of a proved polarity witness,
    Federer 3.1.1, p. 209; selection is private behind this seal. *)
Definition map (R : realType) (V D : lmodType R)
  (B : V -> V -> R) (hB : is_inner_product B)
  (hN : is_real_norm (inner_norm hB))
  (evaluation : Hom D (Hom V R^o)) (DN : D -> R)
  (hD : is_continuous_dual hN evaluation DN) : Hom V D :=
  sval (constructive_indefinite_description (continuous_polarity_exists hD)).
(** Source for [laws]: the witness satisfies the defining pairing
    of Federer 3.1.1, p. 209. *)
Lemma laws (R : realType) (V D : lmodType R)
  (B : V -> V -> R) (hB : is_inner_product B)
  (hN : is_real_norm (inner_norm hB))
  (evaluation : Hom D (Hom V R^o)) (DN : D -> R)
  (hD : is_continuous_dual hN evaluation DN) :
  is_continuous_polarity B evaluation (@map R V D B hB hN evaluation DN hD).
Proof. exact: (svalP (constructive_indefinite_description
  (continuous_polarity_exists hD))). Qed.
End ContinuousPolarity.
