(** Opaque radial shrink map for Federer (1969),
    4.1.15, p. 372. Public users receive only the original
    value laws. No Lipschitz or approximation theorem is
    assumed by this interface. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals.
From Federer Require Import GrassmannAbbreviations RadialShrinkMapUP
  RadialShrinkMapExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

Module Type RadialShrinkMapSignature.
(** Source for [value]: Psi_r on the original Euclidean
    space, for a positive real radius, Federer 4.1.15, p. 372. *)
Parameter value : forall (R : realType) n (r : R),
  0 < r -> R_n R n -> R_n R n.
(** Source for [laws]: the original two value laws of
    Federer 4.1.15, p. 372, with existence hidden. *)
Parameter laws : forall (R : realType) n (r : R) (hr : 0 < r),
  @is_radial_shrink_map R n r (@value R n r hr).
End RadialShrinkMapSignature.

Module RadialShrinkMap : RadialShrinkMapSignature.
(** Source for [value]: choose the separately proved
    original map of Federer 4.1.15, p. 372, behind an
    opaque seal. The construction is not a public law. *)
Definition value (R : realType) n (r : R) (hr : 0 < r) :
    R_n R n -> R_n R n :=
  projT1 (cid (@radial_shrink_map_exists R n r hr)).
(** Source for [laws]: the chosen map satisfies the
    independent printed specification, Federer 4.1.15, p. 372. *)
Lemma laws (R : realType) n (r : R) (hr : 0 < r) :
  @is_radial_shrink_map R n r (@value R n r hr).
Proof.
exact: (projT2 (cid (@radial_shrink_map_exists R n r hr))).
Qed.
End RadialShrinkMap.
