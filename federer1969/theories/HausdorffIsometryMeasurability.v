(** Federer (1969), 2.10.11, p. 176: completed
    measurable sets are preserved by isometric bijections.
    Supporting the original Cartesian source sets in 3.2.48,
    p. 284; full outer-measure laws handle completions. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp
  classical_sets constructive_ereal topology.
From Federer Require Import InnerMetric HausdorffMeasure HausdorffIsometricBijection
  MeasureUP MeasurePushforward PushforwardMeasurableSets.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [hausdorff_bijective_isometry_pushforward]: exact
    image-measure form of 2.10.11, p. 176, supporting
    the Cartesian coordinates of 3.2.48, p. 284.
    Both actual inverse laws and distance equality are obligations. *)
Lemma hausdorff_bijective_isometry_pushforward (R:realType) (X Y:metricType R)
    (f:X->Y) (g:Y->X):
  cancel f g ->cancel g f ->(forall x y,mdist (f x) (f y)=mdist x y) ->
  forall q,measure_pushforward f (@hausdorff_measure R X q)=@hausdorff_measure R Y q.
Proof.
move=>hLeft hRight hDistance q; apply:funext=>A.
have hImage:f @` (f @^-1` A)=A.
  apply/seteqP; split=>x.
  - by move=>[y hy <-].
  - move=>hx; exists (g x); last exact:hRight.
    change (A (f (g x))); by rewrite hRight.
have h:=@hausdorff_bijective_isometry_invariance R X Y f g hLeft hRight
  hDistance q (f @^-1` A).
rewrite hImage in h; exact (esym h).
Qed.

(** Source for [hausdorff_bijective_isometry_measurable]: supporting
    preservation of completed measurable source sets in 3.2.48,
    p. 284, by the full measure identity of
    2.10.11, p. 176. No source Borel hypothesis is needed. *)
Lemma hausdorff_bijective_isometry_measurable (R:realType) (X Y:metricType R)
    (f:X->Y) (g:Y->X):
  cancel f g ->cancel g f ->(forall x y,mdist (f x) (f y)=mdist x y) ->
  forall q A,measure_measurable (@hausdorff_measure R X q) A ->
    measure_measurable (@hausdorff_measure R Y q) (f @` A).
Proof.
move=>hLeft hRight hDistance q A hA.
rewrite -(@hausdorff_bijective_isometry_pushforward R X Y f g hLeft hRight hDistance q).
apply:pushforward_measurable_from_preimage.
have hPre:f @^-1` (f @` A)=A.
  apply/seteqP; split=>x.
  - move=>[y hy hEq]; have hSame:y=x:=can_inj hLeft hEq.
    by rewrite -hSame.
  - move=>hx; by exists x.
by rewrite hPre.
Qed.
