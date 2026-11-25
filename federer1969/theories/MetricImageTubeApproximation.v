(** Federer (1969), 3.2.38, p. 274: replacing f by its affine
    approximation enlarges the image-tube radius by the pointwise error. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets topology lra.
From Federer Require Import MetricOpenThickening.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [metric_pointwise_image_tube_inclusion]: supporting
    the last display on p. 274 in Federer 3.2.38. A uniform
    pointwise image error e enlarges every original radius-r tube
    into the actual radius-(r+e) tube of the approximating image.
    Empty sources and arbitrary metric targets are retained. *)
Lemma metric_pointwise_image_tube_inclusion (R:realType) (X:Type) (Y:metricType R)
    (S:set X) (f g:X->Y) (e r:R):
  (forall x,S x ->mdist (f x) (g x)<=e) ->
  metric_open_thickening (f @` S) r `<=`metric_open_thickening (g @` S) (r+e).
Proof.
move=>hError z [y [x hx <-] hRadius].
exists (g x); first by exists x.
change (is_true (mdist (g x) z<r+e)).
have hTriangle:=metric_triangle (g x) (f x) z.
have hBound:=hError x hx; rewrite (metric_sym (g x) (f x)) in hTriangle.
change (is_true (mdist (f x) z<r)) in hRadius; lra.
Qed.
