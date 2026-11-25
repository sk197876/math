(** Federer (1969), 3.2.36, p. 273: compact-closure
    reduction commutes with the actual isometric image. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets topology.
From Federer Require Import RealMetricBackground HomeomorphicImageClosure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [continuous_compact_closure_image]: the original-source
    closure reduction for the isometry assertion of Federer 3.2.36,
    p. 273. A continuous image of the compact source closure is
    closed in the metric target. The two closure inclusions then give
    exact equality, without measurability or a global target inverse. *)
Lemma continuous_compact_closure_image (R:realType) (X Y:metricType R)
    (f:X->Y) (A:set X):
  continuous f ->compact (closure A) ->f @` closure A=closure (f @` A).
Proof.
move=>hF hCompact.
have hImageCompact:compact (f @` closure A).
  exact:continuous_compact (continuous_subspaceT hF) hCompact.
have hImageClosed:closed (f @` closure A):=compact_closed (@metric_hausdorff R Y) hImageCompact.
have hCover:f @` A `<=` f @` closure A.
  move=>y [x hx <-]; exists x=>//; exact:subset_closure hx.
apply/seteqP; split.
- exact:continuous_image_closure_subset hF.
- move=>y hy; exact:hImageClosed y (@closureS Y (f @` A) (f @` closure A) hCover y hy).
Qed.
