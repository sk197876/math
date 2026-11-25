(** Federer (1969), 3.4.8(1),(5), pp. 326, 328:
    the original coordinate pullback subring is closed.
    Actual analytic projection and inclusion give a
    continuous retraction of the original germ spaces. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import RealNormUP NormAnalyticUP AnalyticGermUP AnalyticGermMetric
  PointedAnalyticPullbackSealed PointedAnalyticPullbackContinuity
  PointedAnalyticPullbackRetraction ContinuousRetractionImageClosed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [analytic_coordinate_pullback_image_closed]:
    the image of an actual analytic coordinate projection
    with an analytic section is closed in the original
    germ metric, supporting Q_j in 3.4.8(5), p. 328.
    The proof uses the exact same image as the printed
    definition, through its continuous retraction equalizer. *)
Theorem analytic_coordinate_pullback_image_closed (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (A:set X) (B:set Y) (u:X->Y) (v:Y->X) (a:X) (b:Y)
    (hu:@norm_analytic_at R X Y NX NY hNX hNY A u a)
    (hv:@norm_analytic_at R Y X NY NX hNY hNX B v b)
    (hab:u a=b) (hba:v b=a):
  (forall y,u (v y)=y) ->
  @closed (@analytic_germ_metric R X NX hNX a)
    ((fun alpha:@analytic_germ_metric R Y NY hNY b=>
      (@PointedAnalyticPullback.map R X Y NX NY hNX hNY A u a b hu hab alpha:
        @analytic_germ_metric R X NX hNX a)) @` setT).
Proof.
move=>hSection.
pose MX:=@analytic_germ_metric R X NX hNX a.
pose MY:=@analytic_germ_metric R Y NY hNY b.
pose P:=@PointedAnalyticPullback.map R X Y NX NY hNX hNY A u a b hu hab.
pose Q:=@PointedAnalyticPullback.map R Y X NY NX hNY hNX B v b a hv hba.
have hP:=@PointedAnalyticPullback.laws R X Y NX NY hNX hNY A u a b hu hab.
have hQ:=@PointedAnalyticPullback.laws R Y X NY NX hNY hNX B v b a hv hba.
apply:(@continuous_retraction_image_closed MY MX P Q (@metric_hausdorff R MX)).
- exact:(@pointed_analytic_germ_pullback_continuous R X Y NX NY hNX hNY A u a b P hu hab hP).
- exact:(@pointed_analytic_germ_pullback_continuous R Y X NY NX hNY hNX B v b a Q hv hba hQ).
- exact:(@pointed_analytic_germ_pullback_retraction R X Y NX NY hNX hNY a b u v P Q hP hQ hSection).
Qed.
