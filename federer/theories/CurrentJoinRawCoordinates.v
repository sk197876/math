(** Federer (1969), 4.1.11, pp. 364–365: the original
    x,t,y coordinates on the actual source domain. The
    preceding opaque Cartesian-domain maps provide the
    points; only their public coordinate laws are used. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions
  classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct EuclideanOneCoordinate EuclideanCartesianMap
  EuclideanBlockLinearMaps EuclideanScalarCoordinateMaps CurrentDomain
  CurrentCartesianDomainMapsSealed CurrentJoinDomain.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Section CurrentJoinRawCoordinates.
Variable R:realType.
Variable n:nat.
Local Notation X := (R_n R n).
Local Notation Full := (fun _:X=>True).
Local Notation Time := (fun _:R_n R 1%N=>True).
Local Notation TimeSpace := (@euclidean_cartesian_set R 1%N n Time Full).
Local Notation CT := (current_domain R (n+(1+n))%N (@current_join_domain R n)).
Local Notation D := (@CartesianCurrentDomain.split R n (1+n)%N Full TimeSpace).
Local Notation E := (@CartesianCurrentDomain.split R 1%N n Time Full).
Local Notation first := (@euclidean_first_block_map R n (1+n)%N).
Local Notation rest := (@euclidean_last_block_map R n (1+n)%N).
Local Notation middle := (hom_comp (@euclidean_first_block_map R 1%N n) rest).
Local Notation last := (hom_comp (@euclidean_last_block_map R 1%N n) rest).
Local Notation time := (hom_comp (@euclidean_scalar_coordinate_map R 1%N ord0) middle).

(** Source for [current_join_first_point]: the actual x
    in the original S factor, Federer 4.1.11, pp. 364–365. *)
Definition current_join_first_point (z:CT):current_domain R n Full:=(D z).1.

(** Source for [current_join_time_point]: the actual
    time point in the original unit-segment carrier,
    supporting Federer 4.1.11, pp. 364–365. *)
Definition current_join_time_point (z:CT):current_domain R 1%N Time:=(E (D z).2).1.

(** Source for [current_join_last_point]: the actual y
    in the original T factor, Federer 4.1.11, pp. 364–365. *)
Definition current_join_last_point (z:CT):current_domain R n Full:=(E (D z).2).2.

(** Source for [current_join_time_coordinate]: the real
    value of the original time point, supporting the
    literal mass integrals in Federer 4.1.11, p. 365. *)
Definition current_join_time_coordinate (z:CT):R:=
  @euclidean_one_project R (set_val (current_join_time_point z)).

(** Source for [current_join_raw_coordinate_values]: the
    actual source-domain points have exactly their original
    ambient x,t,y coordinates, supporting the differential
    and mass displays in Federer 4.1.11, p. 365. *)
Theorem current_join_raw_coordinate_values z:
  first (set_val z)=set_val (current_join_first_point z) /\
  time (set_val z)=current_join_time_coordinate z /\
  last (set_val z)=set_val (current_join_last_point z).
Proof.
have hOuter:=(@CartesianCurrentDomain.laws R n (1+n)%N Full TimeSpace).2 z.
have hInner:=(@CartesianCurrentDomain.laws R 1%N n Time Full).2 (D z).2.
split;first exact:esym hOuter.1.
split.
- change (@euclidean_one_project R (@euclidean_first_block_map R 1%N n (rest (set_val z)))=
    @euclidean_one_project R (set_val (E (D z).2).1)).
  by rewrite -hOuter.2 -hInner.1.
- change (@euclidean_last_block_map R 1%N n (rest (set_val z))=set_val (E (D z).2).2).
  by rewrite -hOuter.2 -hInner.2.
Qed.
End CurrentJoinRawCoordinates.
