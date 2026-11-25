(** Federer (1969), 4.1.27, p. 384:
    the printed on-image and off-image values
    give an actual field satisfying the
    independent simplex-density specification. The piecewise
    witness serves only to prove existence. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct ExteriorGrading
  SimplexCubeParametrisationUP SimplexHausdorffDensityUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [simplex_hausdorff_density_exists]: existence of
    the field displayed in 4.1.27,
    p. 384, from its independent pointwise
    laws. No auxiliary measure or integration
    representation is assumed by those laws. *)
Theorem simplex_hausdorff_density_exists (R:realType) n m
    (v:'I_(m.+1)->R_n R n):
  exists w:R_n R n->exterior_power (R_n R n) m,is_simplex_hausdorff_density v w.
Proof.
exists (fun y=>if pselect (simplex_positive_barycentric_image v y)
  then simplex_normalised_orientation v else 0).
constructor=>y hY;case:pselect=>hMember;by [].
Qed.
