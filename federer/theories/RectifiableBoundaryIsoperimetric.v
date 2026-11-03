(** Federer (1969), 3.2.44, printed p. 278:
    for a genuinely codimension-one rectifiable boundary,
    replace its lower Minkowski content in 3.2.43 by its
    actual Hausdorff measure using already proved3.2.39.
    The future reference to4.5.9(31) is not assumed here. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanLebesgueDimensions
  EuclideanBallVolume RealPower MinkowskiContents RectifiableSetUP HausdorffMeasure
  ClosedRectifiableMinkowski IsoperimetricInequality.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [topological_boundary_closed]: general topology
    supporting the 3.2.39 application in Federer3.2.44,
    p.278. The original boundary is the intersection of
    the closure with the complement of the interior. *)
Lemma topological_boundary_closed (X:topologicalType) (S:set X):
  closed (closure S `\` interior S).
Proof.
rewrite setDE; apply:closedI; first exact:closed_closure.
exact:open_closedC (open_interior S).
Qed.

(** Source for [federer_3_2_44]: direct rectifiable-boundary
    conclusion of Federer3.2.44, p.278, for ambient
    dimensions at least two. Genuine boundary rectifiability,
    finite original closure volume and all source conventions
    of3.2.43 are retained. No boundary parametrization,
    normal field, area or future unrestricted isoperimetric
    theorem is assumed. *)
Theorem federer_3_2_44 (R:realType) k
    (S:set (inner_metric_space (@euclidean_inner_productP R k.+2))):
  (@euclidean_lebesgue_measure R k.+2 (closure S) < +oo)%E ->
  is_m_rectifiable k.+1 (closure S `\` interior S) ->
  (((k.+2)%:R*real_power (euclidean_unit_ball_volume R k.+2) ((k.+2)%:R)^-1*
    real_power (fine (@euclidean_lebesgue_measure R k.+2 (closure S)))
      ((k.+1)%:R/(k.+2)%:R))%:E<=
    @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R k.+2))
      k.+1 (closure S `\` interior S))%E.
Proof.
move=>hFinite hRect.
have hBound:=@federer_3_2_43 R k S hFinite.
have hClosed:=@topological_boundary_closed
  (inner_metric_space (@euclidean_inner_productP R k.+2)) S.
have hEqual:=(@closed_rectifiable_minkowski_equalities R k.+1 k.+2
  (closure S `\` interior S) (leqnSn k.+1) hClosed hRect).2.
by rewrite hEqual in hBound.
Qed.

(** Source for [positive_closure_rectifiable_boundary_isoperimetric]:
    the positive-volume line case as well as higher dimensions
    in Federer3.2.44, p.278. The positive-volume scope avoids
    the zero-exponent boundary qualification recorded for3.2.43.
    Future4.5.9(31) remains a historical forward reference. *)
Theorem positive_closure_rectifiable_boundary_isoperimetric (R:realType) k
    (S:set (inner_metric_space (@euclidean_inner_productP R k.+1))) (a:R):
  @euclidean_lebesgue_measure R k.+1 (closure S)=a%:E ->0<a ->
  is_m_rectifiable k (closure S `\` interior S) ->
  (((k.+1)%:R*real_power (euclidean_unit_ball_volume R k.+1) ((k.+1)%:R)^-1*
    real_power a (k%:R/(k.+1)%:R))%:E<=
    @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R k.+1))
      k (closure S `\` interior S))%E.
Proof.
move=>hMass ha hRect.
have hBound:=@positive_closure_volume_isoperimetric R k S a hMass ha.
have hEqual:=(@closed_rectifiable_minkowski_equalities R k k.+1
  (closure S `\` interior S) (leqnSn k) (@topological_boundary_closed (inner_metric_space (@euclidean_inner_productP R k.+1)) S) hRect).2.
by rewrite hEqual in hBound.
Qed.
