(** Federer (1969), 3.3.19, p. 304: the exact original
    convex first-measure mass of every level piece. *)
From mathcomp Require Import all_boot all_order all_algebra finmap reals boolp classical_sets constructive_ereal topology ring.
From Federer Require Import EuclideanInnerProduct InnerMetric MetricClosedBalls RealTrigonometryUP CircularTrigonometryUP CircularTrigonometrySealed
  FactorialDiscScalesSealed CircularDiscTreeUP CircularDiscLimitUP CircularDiscExactMass
  CircularDiscRestrictedMeasures CircularDiscPieceHausdorffMass IntegralGeometricMeasure ProjectionBeta.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Pieces.
Variable R:realType.
Local Notation E:=(inner_metric_space (@euclidean_inner_productP R 2)).
Local Notation p:=(@CircularTrigonometry.half_period R).
Local Notation rho:=(@FactorialDiscScales.radius R).
Local Notation b:=(@projection_beta R 2 1 (leqnSn 1) 1).
Local Notation Q:=(@convex_integral_geometric_measure R 2 1 (leqnSn 1) 1).
Variable H:nat->{fset E}.
Hypothesis hH:is_circular_disc_tree H.
Variable A:set E.
Hypothesis hA:is_circular_disc_limit H A.

(** Source for [circular_disc_piece_convex_mass]:
    Q_1^1(A intersect B)= pi rho_n for each original
    B in G_n, exactly 3.3.19, p. 304.
    Apply the proved original restriction identity and
    cancel the actual positive finite beta coefficient. *)
Theorem circular_disc_piece_convex_mass j (c:E):c \in H j ->
  Q (A `&` metric_closed_ball c (rho j))=(p* rho j)%:E.
Proof.
move=>hc.
have h:= @circular_disc_restricted_normalized_measure_agreement R H hH A hA
  (metric_closed_ball c (rho j)).
rewrite (@circular_disc_piece_Hausdorff_mass R H hH A hA j c hc) in h.
have hExpected:(b%:E*(p* rho j)%:E=(2* rho j)%:E)%E.
  by rewrite -EFinM mulrA (@circular_disc_first_beta_normalization R).
have hEqual:= eq_trans h (esym hExpected).
have hPositive:0<b:= @projection_beta_positive R 2 1 (leqnSn 1) 1 (lexx _).
have hNonzero:b!=0 by rewrite gt_eqF.
have hCancel (z: \bar R):((b^-1)%:E*(b%:E* z)= z)%E.
  by rewrite muleA -EFinM mulVf // mul1e.
have hScaled:= congr1 (fun z: \bar R=>((b^-1)%:E* z)%E) hEqual.
by rewrite !hCancel in hScaled.
Qed.

(** Source for [circular_disc_printed_restriction_normalization]:
    the literal normalized restriction identity
    (H1 restricted to A)/2=(Q_1 restricted to A)/pi,
    3.3.19, p. 304. It holds on every original
    test set, including nonmeasurable ones. *)
Theorem circular_disc_printed_restriction_normalization (T:set E):
  (((2:R)^-1)%:E*@HausdorffMeasure.hausdorff_measure R E 1 (A `&` T)=
    (p^-1)%:E*Q (A `&` T))%E.
Proof.
rewrite -(@circular_disc_restricted_normalized_measure_agreement R H hH A hA T) muleA -EFinM.
suff h:(2:R)^-1* b= p^-1 by rewrite h.
have hPositive:0<b:= @projection_beta_positive R 2 1 (leqnSn 1) 1 (lexx _).
have hPi:0<p:= real_trigonometry_pi_positive (circular_trig_basic (@CircularTrigonometry.laws R)).
have hNonzero:p!=0 by rewrite gt_eqF.
apply:(mulIf hNonzero).
rewrite -mulrA (@circular_disc_first_beta_normalization R) !mulVf //.
by rewrite pnatr_eq0.
Qed.
End Pieces.
