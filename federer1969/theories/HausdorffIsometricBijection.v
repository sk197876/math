(** Federer (1969), 2.10.45, printed p. 202: the measure gamma is invariant
    under Euclidean translations. This supporting Hausdorff invariance
    follows by applying the image estimate of 2.10.11, p. 176, to an
    isometric bijection and its inverse. It is derived from the already
    proved covering laws, not imported from an external measure library. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology LipschitzUP HausdorffMeasure HausdorffLipschitzImages.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [hausdorff_bijective_isometry_invariance]: supporting
    translation invariance of gamma in 2.10.45,
    p. 202, by the two Lipschitz image
    inequalities of 2.10.11, p. 176.
    All natural degrees, arbitrary targets and
    infinite mass are included. *)
Theorem hausdorff_bijective_isometry_invariance (R : realType) (X Y : metricType R)
    (f : X -> Y) (g : Y -> X) :
  cancel f g -> cancel g f -> (forall x y, mdist (f x) (f y)=mdist x y) ->
    forall m A, @hausdorff_measure R Y m (f @` A)=@hausdorff_measure R X m A.
Proof.
move=> hgf hfg hdist m A.
have hb : is_metric_lipschitz_bound setT f 1%R.
  split; first exact: ler01.
  by move=> x y _ _; rewrite hdist mul1r.
have hbi : is_metric_lipschitz_bound setT g 1%R.
  split; first exact: ler01.
  by move=> x y _ _; rewrite mul1r -(hdist (g x) (g y)) !hfg.
have hf := @hausdorff_lipschitz_image_bound R X Y f 1%R m hb A.
have hg := @hausdorff_lipschitz_image_bound R Y X g 1%R m hbi (f @` A).
rewrite expr1n mul1e in hf hg.
have he : g @` (f @` A)=A.
  apply/seteqP; split.
  - move=> x [y [z hz <-] <-]; by rewrite hgf.
  - move=> x hx; exists (f x); last by rewrite hgf.
    by exists x.
rewrite he mul1e in hg; by apply/eqP; rewrite eq_le hf hg.
Qed.
