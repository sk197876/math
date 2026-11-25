(** Federer (1969), 3.2.36, p. 272:
    uniform image-point control bounds the
    Hausdorff distance of the actual compact images. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets topology.
From Federer Require Import CompactSetDistanceProfile CompactHausdorffMetric
  HausdorffDistanceUP HausdorffDistanceBasic HausdorffDistance MetricSetDistanceUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [compact_image_hausdorff_change_bound]:
    supporting the joint projection-image continuity
    in Federer 3.2.36, p. 272.
    Two compact images of the same source
    have Hausdorff distance at most the
    common pointwise image error. Exact image
    laws specify both images; no image operator
    or nearest-point function is selected.
    Convexity and Euclidean structure are
    unnecessary for this metric support. *)
Lemma compact_image_hausdorff_change_bound (R:realType) (T:Type) (Y:metricType R)
    (A:set T) (F G:T->Y) (P Q:compact_hausdorff_space Y) (e:R):
  0<=e ->val P=F @` A ->val Q=G @` A ->
  (forall x,A x ->mdist (F x) (G x)<=e) ->mdist P Q<=e.
Proof.
move=>he hP hQ hChange.
rewrite compact_hausdorff_distanceE.
apply ((@hausdorff_distance_directed_bound R Y (@hausdorff_distance R Y)
  (@hausdorff_distance_specification R Y) P Q e he).2).
split.
- move=>y; rewrite hP=>[[x hx <-]].
  have hG:val Q (G x) by rewrite hQ; exists x.
  exact:le_trans (@metric_set_distance_lower R Y (val Q) (compact_set_distance_profile Q) (compact_set_distance_profile_specification Q) (F x) (G x) hG)
    (hChange x hx).
- move=>y; rewrite hQ=>[[x hx <-]].
  have hF:val P (F x) by rewrite hP; exists x.
  have h:=@metric_set_distance_lower R Y (val P) (compact_set_distance_profile P) (compact_set_distance_profile_specification P) (G x) (F x) hF.
  rewrite metric_sym in h; exact:le_trans h (hChange x hx).
Qed.
