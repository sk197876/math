(** Federer (1969), 4.1.27, p. 384:
    opaque access to the original simplex
    Hausdorff-density field. Only its independently
    specified on-image and off-image laws are
    exposed; its existence witness stays hidden. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct ExteriorGrading
  SimplexHausdorffDensityUP SimplexHausdorffDensityExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Type SimplexHausdorffDensitySignature.
(** Source for [value]: the field eta displayed
    in Federer 4.1.27, p. 384. *)
Parameter value:forall (R:realType) n m (v:'I_(m.+1)->R_n R n),
  R_n R n->exterior_power (R_n R n) m.
(** Source for [laws]: the original values on
    and off f(C), 4.1.27, p. 384. *)
Parameter laws:forall R n m v,is_simplex_hausdorff_density v (@value R n m v).
End SimplexHausdorffDensitySignature.

Module SimplexHausdorffDensity:SimplexHausdorffDensitySignature.
(** Source for [value]: seal the independently proved
    density witness for 4.1.27, p. 384. *)
Definition value (R:realType) n m (v:'I_(m.+1)->R_n R n):=
  projT1 (cid (@simplex_hausdorff_density_exists R n m v)).
(** Source for [laws]: expose exactly the independent
    original density laws of 4.1.27,
    p. 384, without an implementation field. *)
Lemma laws R n m v:is_simplex_hausdorff_density v (@value R n m v).
Proof. exact:projT2 (cid (@simplex_hausdorff_density_exists R n m v)). Qed.
End SimplexHausdorffDensity.
