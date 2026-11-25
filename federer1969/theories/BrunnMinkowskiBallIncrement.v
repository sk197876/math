(** Federer (1969), 3.2.42, printed p. 278, first
    proof display: apply the actual Brunn--Minkowski theorem
    to the original source and radius-r ball, then retain
    the constant and linear terms of the integer power. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology num_normedtype ring.
From Federer Require Import EuclideanInnerProduct InnerMetric InnerNormedTopology
  EuclideanLebesgueDimensions EuclideanBallVolume VectorSetSum BrunnMinkowski
  ExtendedPositivePower ExtendedRootPowerComparison RealPower
  RealPowerNaturalHausdorff PositiveNaturalRootPowers NaturalPowerIncrementLower
  MeasureUP MeasureBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [brunn_minkowski_ball_volume_increment]: direct
    first volume estimate in the proof of Federer 3.2.42,
    p. 278. The original nonempty source need not be measurable
    or bounded. Its actual finite volume a and the actual
    ball volume determine the printed linear coefficient. *)
Lemma brunn_minkowski_ball_volume_increment (R:realType) k
    (S:set (inner_metric_space (@euclidean_inner_productP R k.+1))) (a r:R):
  S !=set0 ->@euclidean_lebesgue_measure R k.+1 S=a%:E ->0<r ->
  ((a+(k.+1)%:R*real_power a (k%:R/(k.+1)%:R)*
    real_power (euclidean_unit_ball_volume R k.+1) ((k.+1)%:R)^-1*r)%:E<=
    @euclidean_lebesgue_measure R k.+1
      (vector_set_sum S [set y | (`|y|<r)%R]))%E.
Proof.
move=> hS hMass hr.
pose E:=inner_metric_space (@euclidean_inner_productP R k.+1).
pose mu:=@euclidean_lebesgue_measure R k.+1.
pose alpha:=euclidean_unit_ball_volume R k.+1.
pose p:R:=(k.+1)%:R.
pose x:=real_power a p^-1.
pose y:=real_power alpha p^-1*r.
pose B:set E:=[set y | `|y|<r].
have hp:0<p by rewrite /p ltr0n.
have ha:0<=a.
  have h:(0<=mu S)%E:=measure_nonnegative (euclidean_lebesgue_is_measure R k.+1) S.
  by rewrite /mu hMass lee_fin in h.
have hAlpha:0<alpha:=(euclidean_unit_ball_volumeE R k.+1).2.
have hBNe:B !=set0.
  exists (0:E); change (is_true (`|(0:E)|<r)); by rewrite normr0.
have hBall:mu B=(alpha*r^+k.+1)%:E.
  have h:=@euclidean_ball_measure R k.+1 (0:E) r hr.
  have hSet:[set z:E | `|z-0|<r]=B.
    by apply/seteqP; split=>z; rewrite /B /= subr0.
  rewrite hSet in h; exact h.
have hBallRoot:real_power (alpha*r^+k.+1) p^-1=y.
  rewrite (@real_power_product R alpha (r^+k.+1) p^-1
    (ltW hAlpha) (exprn_ge0 k.+1 (ltW hr))).
  by rewrite (@positive_natural_power_root R r k.+1 (ltW hr) (erefl true)).
have hBound:=@federer_3_2_41 R k.+1 S B (erefl true) hS hBNe.
change (is_true (extended_positive_power (mu S) p^-1+
  extended_positive_power (mu B) p^-1<=
  extended_positive_power (mu (vector_set_sum S B)) p^-1)%E) in hBound.
have hMS:mu S=a%:E:=hMass.
rewrite hMS hBall /extended_positive_power hBallRoot -EFinD in hBound.
have hx:0<=x:=real_power_nonnegative _ _.
have hy:0<=y:=mulr_ge0 (real_power_nonnegative _ _) (ltW hr).
have hXY:0<=x+y:=addr_ge0 hx hy.
have hPowered:=(@extended_root_power_lower_comparison R (mu (vector_set_sum S B))
  p (x+y) (measure_nonnegative (euclidean_lebesgue_is_measure R k.+1) _) hp hXY).1 hBound.
have hRootPower:x^+k.+1=a:=@positive_natural_root_power R a k.+1 ha (erefl true).
have hRootSubpower:x^+k=real_power a (k%:R/(k.+1)%:R):=
  @positive_natural_root_subpower R a k.+1 k ha (erefl true).
have hLinear:=@natural_power_increment_linear_lower R x y k hx hy.
rewrite hRootPower hRootSubpower /y in hLinear.
rewrite /p (@real_power_natural_exponent R (x+y) k.+1 hXY) in hPowered.
apply:le_trans _ hPowered; rewrite lee_fin.
have hEq:(k.+1)%:R*real_power a (k%:R/(k.+1)%:R)*
    (real_power alpha p^-1*r)=
    (k.+1)%:R*real_power a (k%:R/(k.+1)%:R)*real_power alpha p^-1*r by ring.
rewrite hEq in hLinear; exact hLinear.
Qed.
