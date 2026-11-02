(** Federer (1969), 3.2.35, p. 271:
    boundedness of the original body containing zero
    supplies a finite positive outer norm bound. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology lra.
From Federer Require Import RealNormUP NormMetric MetricDiameterUP MetricDiameter CoveringFamilyUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [norm_bounded_zero_outer_ball]: supporting
    the positive unit-sphere gauge bound in
    Federer 3.2.35, p. 271. The existing
    sealed diameter laws bound all distances from
    the original zero member. Its proved finite
    value plus one gives a local positive radius;
    no outer-ball hypothesis or selected global
    witness is added to the body theorem. *)
Lemma norm_bounded_zero_outer_ball (R:realType) (V:lmodType R)
    (N:V->R) (hN:is_real_norm N) (S:set V):
  @metric_set_bounded R [the metricType R of real_norm_metric_space hN] S ->S 0 ->
  exists M:R,0<M /\forall y:V,S y ->N y<=M.
Proof.
move=>hBound hZero.
pose T:=[the metricType R of real_norm_metric_space hN].
pose D:=@extended_metric_diameter R T S.
have hD:=@extended_metric_diameter_specification R T S.
have hNonnegative:(0<=D)%E:=metric_diameter_nonnegative hD.
have hFinite:D \is a fin_num.
  rewrite (ge0_fin_numE hNonnegative); exact hBound.
pose d:R:=fine D.
have hValue:D=d%:E by rewrite /d fineK.
have hd:0<=d by move:hNonnegative; rewrite hValue lee_fin.
exists (d+1); split; first by lra.
move=>y hy.
have hh:=@metric_diameter_upper R T S D hD 0 y hZero hy.
change (is_true ((N (0-y))%:E<=D)%E) in hh.
rewrite sub0r (real_seminorm_negate hN.1) hValue lee_fin in hh; lra.
Qed.
