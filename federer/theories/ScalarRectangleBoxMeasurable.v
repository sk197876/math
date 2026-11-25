(** Federer (1969), 4.1.8, p. 362: the
    original finite open coordinate box is Lebesgue
    measurable. Reuse the coordinate-box theorem of
    2.6.5, pp. 119–120, with its actual intervals. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology normedtype.
From Federer Require Import GrassmannAbbreviations RealMetricBackground EuclideanLebesgueDimensions
  EuclideanLebesgueBoxes MeasureUP OrientedRectangleDomain
  ScalarSegmentFactors ScalarRectangleBox ScalarRectangleBoxCoordinates.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [scalar_rectangle_box_measurable]: the original
    box in the finite-product identity is measurable,
    supporting the actual E^nu restriction in Federer
    4.1.8, p. 362. The empty box is included.
    Ordering is not required for measurability. *)
Theorem scalar_rectangle_box_measurable (R:realType) (f:seq (R*R)):
  measure_measurable (@euclidean_lebesgue_measure R
    (oriented_rectangle_dimension (@scalar_segment_factors R f))) (@scalar_rectangle_box R f).
Proof.
pose d:=oriented_rectangle_dimension (@scalar_segment_factors R f).
pose I (i:'I_d):set (real_line_metric R):=`](nth (0,0) f (val i)).1,(nth (0,0) f (val i)).2[.
have [hMeas _]:=@euclidean_coordinate_box_measure R d I
  (fun i=>@lebesgue_scalar_open_interval_measurable R
    (nth (0,0) f (val i)).1 (nth (0,0) f (val i)).2).
have hBox:@scalar_rectangle_box R f=euclidean_coordinate_box I.
  apply/seteqP;split=>x h.
  - have hc:=(scalar_rectangle_box_coordinates x).1 h.
    move=>i.
    change (is_true (x i \in `](nth (0,0) f (val i)).1,(nth (0,0) f (val i)).2[%R)).
    rewrite in_itv /=;exact:(hc i).
  - apply:(scalar_rectangle_box_coordinates x).2=>i.
    have hi:=h i.
    change (is_true (x i \in `](nth (0,0) f (val i)).1,(nth (0,0) f (val i)).2[%R)) in hi.
    move:hi;by rewrite in_itv /=.
by rewrite hBox.
Qed.
