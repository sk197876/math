(** Federer (1969), 4.1.8, p. 362: the
    original open coordinate box for the finite
    ordered scalar segment product. This is a
    derived Cartesian set in the existing block coordinates. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import GrassmannAbbreviations EuclideanBlockCoordinates EuclideanCartesianMap
  EuclideanOneCoordinate OrientedRectangleDomain ScalarSegmentFactors.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section ScalarRectangleBox.
Variable R:realType.
Local Notation D := (fun f=>oriented_rectangle_dimension (@scalar_segment_factors R f)).

(** Source for [scalar_rectangle_box_step]: attach the
    original first scalar interval to the remaining
    nonempty Cartesian box, supporting Federer 4.1.8,
    p. 362. A singleton retains its interval. *)
Definition scalar_rectangle_box_step (a:R*R) (t:seq (R*R)):
    set (R_n R (D t))->set (R_n R (D (a::t))):=
  match t as q return set (R_n R (D q))->set (R_n R (D (a::q))) with
  |[::]=>fun _=>[set x|a.1<x ord0<a.2]
  |b::s=>fun B=>@euclidean_cartesian_set R 1%N (D (b::s))
      [set x|a.1<x ord0<a.2] B
  end.

(** Source for [scalar_rectangle_box]: the original
    open coordinate box {x:u_k<x_k<v_k}, supporting
    the final display of Federer 4.1.8,
    p. 362. The empty box is all R^0. *)
Fixpoint scalar_rectangle_box (f:seq (R*R)):set (R_n R (D f)):=
  match f as g return set (R_n R (D g)) with
  |[::]=>setT
  |a::t=>@scalar_rectangle_box_step a t (@scalar_rectangle_box t)
  end.
End ScalarRectangleBox.
