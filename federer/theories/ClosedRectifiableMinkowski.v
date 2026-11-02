(** Federer (1969), 3.2.39, pp. 275--276:
    Hausdorff measure is the common Minkowski content of every
    closed genuinely rectifiable Euclidean subset. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric RectifiableSetUP
  ClosedRectifiableCompactParametrization CompactRectifiableImageMinkowski
  RectifiableLowerMinkowskiBound ZeroDegreeRectifiableMinkowski HausdorffMeasure
  MinkowskiContents PartialFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [closed_rectifiable_minkowski_equalities]: both
    full-radius contents equal actual H^m(W), proving the common
    content asserted in Federer 3.2.39, pp. 275--276.
    All admissible natural dimensions remain. Positive dimension
    uses the actual compact parametrization, finite compact source
    family, multiplicity layers and full-radius comparison. Zero
    dimension uses counting equality for every original finite
    set, including several atoms; a single R^0 map is not
    asserted to parametrize a multipoint set. No finite-mass,
    derivative-field or selected-cover premise is added. *)
Theorem closed_rectifiable_minkowski_equalities (R:realType) m n
    (W:set (inner_metric_space (@euclidean_inner_productP R n))):
  (m<=n)%N ->closed W ->is_m_rectifiable m W ->
  upper_minkowski_content m W=@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R n)) m W /\
  lower_minkowski_content m W=@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R n)) m W.
Proof.
case:m=>[|m] hmn hClosed hW.
- exact:zero_degree_hausdorff_minkowski_equalities.
- have [f [A [hLip [hA hImage]]]]:=closed_positive_rectifiable_compact_parametrization hClosed hW.
  have hDims:(0<m.+1<=n)%N by rewrite ltn0Sn.
  have hUpper:=@compact_rectifiable_image_upper_minkowski R m.+1 n f A W hDims hLip hA hImage hW.
  have hLower:=@rectifiable_hausdorff_lower_minkowski_bound R m.+1 n W hmn hW.
  have hOrder:=@minkowski_contents_ordered R n m.+1 W.
  split.
  + apply/eqP; rewrite eq_le; apply/andP; split; first exact hUpper.
    exact:le_trans hLower hOrder.
  + apply/eqP; rewrite eq_le; apply/andP; split; last exact hLower.
    exact:le_trans hOrder hUpper.
Qed.

(** Source for [federer_3_2_39]: the entire theorem of
    Federer 3.2.39, p. 275, proved on pp. 275--276.
    The actual partial common-content graph has precisely the
    printed H^m value, since both full-radius contents agree.
    Retain the genuine rectifiability definition and its finite
    degree-zero convention, original closed W and all admissible
    natural dimensions. No unproved kinematic or later content
    comparison is used. *)
Theorem federer_3_2_39 (R:realType) m n
    (W:set (inner_metric_space (@euclidean_inner_productP R n))):
  (m<=n)%N ->closed W ->is_m_rectifiable m W ->
  partial_function_graph (@minkowski_content R n m) W
    (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m W).
Proof.
move=>hmn hClosed hW; apply:(minkowski_content_graph m W _).2.
exact:closed_rectifiable_minkowski_equalities hmn hClosed hW.
Qed.
