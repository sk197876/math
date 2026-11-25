(** Federer (1969), 3.2.41, printed p. 277, finite-family
    induction: strict coordinate halfspaces are measurable and
    their separating hyperplane is null. The resulting split
    holds for the outer measure of every original set. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology normedtype lra.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  EuclideanCoordinateTopology EuclideanLebesgueDimensions EuclideanLebesgueBoxes
  EuclideanCoordinateHyperplaneNull MeasureUP MeasureBasic MeasureNullModification
  TopologicalBorel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_coordinate_lower_halfspace_open]: supporting
    separating open halfspace in Federer 3.2.41, p. 277, from
    continuity of the actual coordinate projection. *)
Lemma euclidean_coordinate_lower_halfspace_open (R:realType) n (i:'I_n) (t:R):
  open [set x:inner_metric_space (@euclidean_inner_productP R n)|(x i<t)%R].
Proof.
change (open ((fun x:inner_metric_space (@euclidean_inner_productP R n)=>(x i:R^o))
  @^-1` [set u:R^o|u<t])).
apply:open_comp; last exact:open_lt.
by move=> x _; exact:euclidean_coordinate_continuous.
Qed.

(** Source for [euclidean_coordinate_upper_halfspace_open]: supporting
    other separating halfspace in Federer 3.2.41, p. 277. *)
Lemma euclidean_coordinate_upper_halfspace_open (R:realType) n (i:'I_n) (t:R):
  open [set x:inner_metric_space (@euclidean_inner_productP R n)|(t<x i)%R].
Proof.
change (open ((fun x:inner_metric_space (@euclidean_inner_productP R n)=>(x i:R^o))
  @^-1` [set u:R^o|t<u])).
apply:open_comp; last exact:open_gt.
by move=> x _; exact:euclidean_coordinate_continuous.
Qed.

(** Source for [euclidean_coordinate_halfspace_volume_split]: supporting
    exact two-piece volume sum in Federer 3.2.41, p. 277.
    The original A may be nonmeasurable or have infinite mass.
    The measurability used is that of the separating halfspace;
    the omitted coordinate hyperplane is genuinely null. *)
Lemma euclidean_coordinate_halfspace_volume_split (R:realType) n (i:'I_n) (t:R)
    (A:set (inner_metric_space (@euclidean_inner_productP R n))):
  @euclidean_lebesgue_measure R n A=
    (@euclidean_lebesgue_measure R n (A `&` [set x|(x i<t)%R])+
      @euclidean_lebesgue_measure R n (A `&` [set x|(t<x i)%R]))%E.
Proof.
pose E:=inner_metric_space (@euclidean_inner_productP R n).
pose mu:=@euclidean_lebesgue_measure R n.
have hm:=euclidean_lebesgue_is_measure R n.
have hLeft:measure_measurable mu [set x:E|(x i<t)%R].
  exact:euclidean_borel_measurable (open_borel_set
    (@euclidean_coordinate_lower_halfspace_open R n i t)).
have hRemainder:mu (A `\` [set x|(x i<t)%R])=mu (A `&` [set x|(t<x i)%R]).
  apply:(@measure_null_modification_value R E mu hm _ _ [set x|x i=t]
    (@euclidean_coordinate_hyperplane_null R n i t)).
  move=> x hNe; split.
  - move=> [hx hNotLow]; split=>//.
    have hGe:(t<=x i) by rewrite leNgt; exact/negP.
    have hDifferent:x i!=t by apply/eqP.
    case:(ltP t (x i))=>[hLt|hLe]; first exact hLt.
    exfalso; apply:hNe; apply/eqP; by rewrite eq_le hGe hLe.
  - move=> [hx hHigh]; split=>// hLow.
    have hBad:=lt_trans hHigh hLow; by rewrite ltxx in hBad.
rewrite /mu in hLeft hRemainder.
rewrite (hLeft A) hRemainder; reflexivity.
Qed.
