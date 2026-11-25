(** Federer (1969), 3.3.8, p. 295: nullity of each original
    small source piece through the closed increasing sets C_j. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology ring.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanProjectionSpace
  StructureConeUP StructureApertureMassUP StructureApertureClosedSets StructureZeroApertureCutoffs
  StructureSmallSourceAllRadii StructureProjectedDiameterFinite StructurePureProjectionMass
  StructureConeDensityValues EuclideanBallVolume EuclideanLebesgueDimensions
  RectifiableSetUP PureUnrectifiableLaws MeasureUP MeasureBasic MeasureRestriction
  MeasureContinuityBelow RealLatticeTruncationLimits ExtendedRealReciprocalBounds ExtendedRealLimitBounds ExtendedScaledErrorBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [structure_small_zero_aperture_null]: the complete
    small-piece argument of Federer 3.3.8, p. 295. The C_j are
    actual closed centre sets and hence measurable for the ORIGINAL
    restriction phi to E. Original-image monotonicity retains a
    single finite projected cost when passing to the increasing
    union. Arbitrarily small positive lambda then gives outer-nullity.
    Neither E nor its projected image is assumed measurable. *)
Theorem structure_small_zero_aperture_null (R:realType) n m (hmn:(m<=n)%N)
    (phi:set (inner_metric_space (@euclidean_inner_productP R n))->\bar R)
    (E:set (inner_metric_space (@euclidean_inner_productP R n)))
    (p:euclidean_projection_space R n m) (a delta:R):
  is_structure_measure phi ->is_purely_measure_m_unrectifiable phi m E ->
  0<=a ->a<delta ->(forall x y,E x ->E y ->mdist x y<=a) ->
  (forall x,E x ->structure_zero_aperture_at hmn phi E p x delta) ->phi E=0%E.
Proof.
move=>hStructure hPure ha haDelta hDiameter hZero.
have hLeb:=euclidean_lebesgue_is_measure R m.
pose L:=euclidean_lebesgue_measure m (euclidean_projection_linear p @` E).
have hL0:(0<=L)%E:=measure_nonnegative hLeb _.
have hLFinite:L \is a fin_num.
  rewrite (ge0_fin_numE hL0).
  exact:(@structure_projected_diameter_mass_finite R n m E p a ha hDiameter).
pose M:=fine L.
have hL:L=M%:E by rewrite /M fineK.
have hM:0<=M by move:hL0; rewrite hL lee_fin.
have hBound lam:0<lam ->(phi E<=(2*84^+m*lam)%:E*L)%E.
  move=>hLam.
  pose b:=lam*euclidean_unit_ball_volume R m.
  have hb:0<b:=mulr_gt0 hLam (@euclidean_unit_ball_volumeE R m).2.
  pose C j:=structure_aperture_bound_centres hmn phi E p delta (((j.+1)%:R:R)^-1) b.
  have hCClosed j:closed (C j):=structure_aperture_bound_centres_closed hStructure.
  have hIncreasing i j:(i<=j)%N ->C i `<=` C j.
    move=>hij; apply:structure_aperture_bound_centres_mono.
    exact:positive_reciprocal_nat_antitone hij.
  have hCover:E `<=` \bigcup_j C j.
    move=>x hx; have [t [ht hTail]]:=hZero x hx b hb.
    have [j hj]:=positive_reciprocal_nat_small ht.
    exists j=>// r s hr /andP [hs hsj]; apply:hTail=>//.
    apply/andP; split=>//; exact:lt_trans hsj hj.
  pose mu:=measure_restrict phi E.
  have hMu:is_measure mu:=measure_restrict_is_measure hStructure.1 E.
  have hMeas j:measure_measurable mu (C j).
    apply:(measure_restrict_measurable E); exact:hStructure.2 _ (hCClosed j).
  have hUnion:E `&` (\bigcup_j C j)=E.
    apply/seteqP; split; first by move=>x [hx _].
    move=>x hx; split=>//; exact:hCover x hx.
  have hLimit:=@measure_continuity_below R _ mu hMu C hMeas hIncreasing.
  rewrite /mu /measure_restrict hUnion in hLimit.
  apply:(extended_order_limit_upper_bound hLimit.2)=>j.
  pose t:=(((j.+1)%:R:R)^-1).
  have ht:0<t by rewrite /t invr_gt0 ltr0n.
  have hHalf:=structure_density_positive_half_bounds ht.
  have hHalfOne:=@structure_density_positive_half_bounds R 1 ltr01.
  pose sigma:=Num.min (1/2) (t/2).
  have hSigma0:0<sigma.
    rewrite /sigma lt_min; apply/andP; split; [exact:(andP hHalfOne).1|exact:(andP hHalf).1].
  have hSigma1:sigma<1.
    apply:le_lt_trans _ (andP hHalfOne).2; by rewrite /sigma ge_min lexx.
  have hSigmaT:sigma<t.
    apply:le_lt_trans _ (andP hHalf).2; by rewrite /sigma ge_min lexx orbT.
  have hSigma:0<sigma<1 by apply/andP; split.
  have hAperture:=@structure_small_source_all_radii R n m hmn phi E p a delta t sigma lam
    hStructure.1 ha haDelta hSigma hSigmaT hLam hDiameter.
  have hSubset:E `&` C j `<=` E by move=>x [hx _].
  have hPureSub:=pure_unrectifiable_subset hSubset hPure.
  have hImage:(euclidean_projection_linear p @` (E `&` C j)) `<=`
      (euclidean_projection_linear p @` E).
    move=>z [x [hx _] <-]; by exists x.
  have hComparison:=@federer_3_3_7 R n m hmn phi (E `&` C j) p sigma lam
    hStructure hPureSub hSigma hLam hAperture.
  have hImageBound:=@measure_mono R _ (@euclidean_lebesgue_measure R m) hLeb _ _ hImage.
  have hCoefficient:0<=2*84^+m*lam.
    apply:mulr_ge0; last exact:ltW hLam.
    apply:mulr_ge0; [by rewrite ler0n|apply:exprn_ge0; by rewrite ler0n].
  exact:le_trans hComparison (lee_wpmul2l (lee_tofin hCoefficient) hImageBound).
have hPower:0<=(84:R)^+m by apply:exprn_ge0; by rewrite ler0n.
have hCoefficient:0<=2*84^+m*M:=mulr_ge0 (mulr_ge0 (ler0n R 2) hPower) hM.
apply/eqP; rewrite eq_le (measure_nonnegative hStructure.1 E) andbT.
apply:(@extended_upper_bound_from_scaled_errors R (phi E) 0 (2*84^+m*M) hCoefficient)=>e he.
have h:=hBound e he; rewrite hL -EFinM in h.
have hEqual:(2*84^+m*e)*M=0+(2*84^+m*M)*e by ring.
by rewrite hEqual in h.
Qed.
