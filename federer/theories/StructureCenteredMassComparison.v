(** Federer (1969), 3.3.7, p. 294: the local actual
    centered-ball estimate controls the original outer target mass. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import MeasureUP MeasureBasic MeasureRestriction MeasureDerivationContext
  MeasureDerivates CoveringRelationLimits CenteredBallRelations CenteredDensityGeometry
  CenteredRatioInfinity CenteredMeasureDecomposition NullBallLocus DerivationComparison
  AbsoluteContinuousPart MetricClosedBalls StructureCenteredMassLowerLimit ExtendedGeometricSqueeze.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [structure_centered_local_mass_comparison]: the use
    of 2.9.15 and the comparison underlying 2.9.7 in Federer 3.3.7,
    p. 294. Actual ball bounds exclude the original infinite-density
    and null-ball exceptional sets on E. The continuous part equals
    the ORIGINAL numerator there. Apply strict 2.9.4 at C times t
    and let t decrease to one to retain the exact coefficient. No
    measurability of the original target E is assumed. *)
Theorem structure_centered_local_mass_comparison (R:realType) (X:metricType R)
    (phi psi:set X-> \bar R) (V0:X->set X->Prop) (E:set X) (C:R):
  is_measure_derivation_context phi V0 ->is_derivation_measure psi ->
  is_centered_density_geometry phi ->0<C ->
  (forall x,E x ->~measure_null_ball_points phi x) ->
  (forall x,E x ->exists delta:R,0<delta /\forall r:R,0<r ->r<delta ->
    (psi (metric_closed_ball x r)<=C%:E*phi (metric_closed_ball x r))%E) ->
  (psi E<=C%:E*phi E)%E.
Proof.
move=>hContext hPsi hGeometry hC hNotNull hMass.
have hPhi:=derivation_context_measure hContext.
have hm:=derivation_measure_law hPhi.
have hLower x:E x ->
    (covering_lower_limit (@centered_closed_ball_relation R X)
      (measure_ratio_function psi phi) x<=C%:E)%E.
  move=>hx; have [delta [hDelta hBound]]:=hMass x hx.
  exact:(@structure_centered_mass_lower_limit R X phi psi x C delta
    hPhi (hNotNull x hx) hDelta hBound).
have hOutside:E `<=` ~` (measure_infinite_centered_density_points psi phi `|` measure_null_ball_points phi).
  move=>x hx; case=>[hInfinite|hNull]; last exact:hNotNull x hx hNull.
  have hDerivate:=(@infinite_centered_density_derivate R X phi psi x hPhi).1 hInfinite.
  have hBound:=hLower x hx.
  by rewrite hDerivate.2.2 leye_eq in hBound.
have [_ [_ hDecomposition]]:=@federer_2_9_15 R X phi psi V0 hContext hPsi hGeometry.
have hSame:measure_continuous_part psi phi E=psi E.
  rewrite hDecomposition /measure_restrict.
  congr (psi _); apply/seteqP; split; first by move=>x [_ hx].
  move=>x hx; split; [exact:hOutside x hx|exact:hx].
have hCentered:is_measure_derivation_context phi (@centered_closed_ball_relation R X).
  constructor; first exact:hPhi.
  exact:geometric_centered_balls_vitali hContext hGeometry.
rewrite -hSame; apply:extended_geometric_squeeze.
- apply:mule_ge0; first by rewrite lee_fin; exact:ltW hC.
  exact:measure_nonnegative hm E.
- move=>t ht.
  have ht0:0<t:=lt_trans ltr01 ht.
  have hCt:0<C*t:=mulr_gt0 hC ht0.
  have hStrict:(C%:E<(C*t)%:E)%E.
    by rewrite lte_fin -{1}[C]mulr1 ltr_pM2l.
  have hLevels x:E x ->
      (covering_lower_limit (@centered_closed_ball_relation R X)
        (measure_ratio_function psi phi) x<(C*t)%:E)%E.
    move=>hx; exact:le_lt_trans (hLower x hx) hStrict.
  have hBound:=@derivation_lower_comparison R X phi psi
    (@centered_closed_ball_relation R X) E (C*t) hCentered hPsi hCt hLevels.
  rewrite muleA -EFinM (mulrC t C); exact:hBound.
Qed.
