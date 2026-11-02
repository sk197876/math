(** Private coordinate-maximum witness for mu in Federer (1969), 2.10.44,
    printed p. 202. Prove the coordinate supremum order laws for the finite
    maximum. The real norm laws are already consequences of the abstract
    specification; this implementation will be hidden by opaque sealing.
    Source context: PlaneSupremumNormUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates UniformFunctionNormUP
  PlaneSupremumNormUP PlaneSupremumNormLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [plane_supremum_norm_exists]: direct
    existence witness for the printed two-coordinate
    supremum norm in 2.10.44, p. 202.
    Only the least-bound laws are exposed later. *)
Lemma plane_supremum_norm_exists (R : realType) :
  exists N : R_n R 2 -> R, is_plane_supremum_norm N.
Proof.
exists (fun x : R_n R 2=>Num.max `|x ord0| `|x ord_max|)=> x; constructor.
- by rewrite le_max normr_ge0.
- move=> i; have [->|->] := plane_coordinate_index_cases i.
  + by rewrite le_max lexx.
  + by rewrite le_max lexx orbT.
- move=> c hc hb; rewrite ge_max; apply/andP; split; [exact: hb ord0|exact: hb ord_max].
Qed.
