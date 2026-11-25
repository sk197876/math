(** Proved existence and uniqueness for the pointwise
    supremum supporting Federer (1969), 3.3.4, p. 291.
    Only the already sealed extended order bounds are used. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets functions reals constructive_ereal.
From Federer Require Import ExtendedRealBoundsUP ExtendedRealBounds MeasureFamilySupremumUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [measure_family_supremum_exists]: existence
    of the actual setwise supremum used for psi_v,
    Federer 3.3.4, p. 291, from 2.1.1, p. 51.
    The empty parameter family also has its order supremum. *)
Theorem measure_family_supremum_exists (R:realType) (X J:Type)
    (D:set J) (nu:J->set X->\bar R):
  exists psi,is_measure_family_supremum D nu psi.
Proof.
exists (fun A=>extended_real_sup [set z|exists j,D j /\ z=nu j A])=>A.
constructor; [exact:extended_real_sup_upper|exact:extended_real_sup_least].
Qed.

(** Source for [measure_family_supremum_unique]: uniqueness
    of the setwise least upper bounds in the definition
    of psi_v, Federer 3.3.4, p. 291. This uses
    the independent specification alone. *)
Theorem measure_family_supremum_unique (R:realType) (X J:Type)
    (D:set J) (nu:J->set X->\bar R) psi chi:
  is_measure_family_supremum D nu psi ->
  is_measure_family_supremum D nu chi ->psi=chi.
Proof.
move=>hPsi hChi; apply:funext=>A.
exact:(extended_real_supremum_unique (hPsi A) (hChi A)).
Qed.
