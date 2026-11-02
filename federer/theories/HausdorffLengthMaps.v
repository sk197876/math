(** The nonexpanding image comparison supporting Federer (1969), 2.5.10, p.
    101, through the Hausdorff construction of 2.10.2(1), p. 171. This is
    the nonmultiplicity special case of 2.10.11, p. 176. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import MetricDiameterUP MetricDiameter MetricDiameterMaps
  CaratheodoryLimitUP CaratheodoryTransport HausdorffLengthUP HausdorffLength.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [nonempty_metric_image_member]: the image of a nonempty cover
    member remains nonempty, supporting Federer 2.10.11, p. 176 *)
Lemma nonempty_metric_image_member (R : realType) (X Y : metricType R)
    (f : X -> Y) (A : @nonempty_metric_sets R X) : f @` val A !=set0.
Proof. have [x hx] := set_valP A; exists (f x); by exists x. Qed.

(** Source for [nonempty_metric_image]: image-cover map supporting Federer
    2.10.11, p. 176. *)
Definition nonempty_metric_image (R : realType) (X Y : metricType R)
    (f : X -> Y) (A : @nonempty_metric_sets R X) : @nonempty_metric_sets R Y :=
  Sub (f @` val A) (mem_set (nonempty_metric_image_member f A)).

(** Source for [hausdorff_length_nonexpanding]: the distance-nonincreasing
    image bound from Federer 2.10.11, p. 176 This does not assert the
    stronger counting-multiplicity bound. *)
Theorem hausdorff_length_nonexpanding (R : realType) (X Y : metricType R)
    (f : X -> Y) :
  (forall x y, (mdist (f x) (f y)<=mdist x y)%R) ->
  forall A, hausdorff_length (f @` A)<=hausdorff_length A.
Proof.
move=> hf A.
apply: (@caratheodory_limit_transport R X Y
  (@nonempty_metric_sets R X) (@nonempty_metric_sets R Y)
  (fun j => val j) (fun j => val j)
  (fun j => extended_metric_diameter (val j))
  (fun j => extended_metric_diameter (val j)) f (@nonempty_metric_image R X Y f)
  (@hausdorff_length R X) (@hausdorff_length R Y)
  (@hausdorff_length_specification R X) (@hausdorff_length_specification R Y)
  _ _ _ _ A).
- move=> j; exact: metric_diameter_nonnegative (extended_metric_diameter_specification (val j)).
- move=> j x hx; by exists x.
- move=> j; exact (@extended_metric_diameter_nonexpanding R X Y f hf (val j)).
- move=> j; exact (@extended_metric_diameter_nonexpanding R X Y f hf (val j)).
Qed.

(** Source for [hausdorff_length_retracted_isometry]:
    supporting invariance for coordinate-line embeddings in
    Federer 2.5.10, p. 101, obtained by applying
    the bound of 2.10.11, p. 176, in both
    directions. Both maps are explicitly nonexpanding and
    the retraction is defined on the whole ambient space. *)
Theorem hausdorff_length_retracted_isometry (R : realType)
    (X Y : metricType R) (f : X -> Y) (g : Y -> X) :
  (forall x y, (mdist (f x) (f y)<=mdist x y)%R) ->
  (forall x y, (mdist (g x) (g y)<=mdist x y)%R) ->
  cancel f g -> forall A, hausdorff_length (f @` A)=hausdorff_length A.
Proof.
move=> hf hg hgf A.
have hupper := hausdorff_length_nonexpanding hf A.
have hlower := hausdorff_length_nonexpanding hg (f @` A).
have he : g @` (f @` A)=A.
  apply/seteqP; split=> x.
  - move=> [_ [y hy <-] <-]; by rewrite hgf.
  - move=> hx; exists (f x); first by exists x.
    exact: hgf.
rewrite he in hlower.
by apply/eqP; rewrite eq_le hupper hlower.
Qed.
