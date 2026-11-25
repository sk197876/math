(** Federer (1969), 3.2.31, pp. 268–269: compact parameter
    source case. The fibre threshold is Borel and finite by
    Chapter 2; the rectifiable/pure decomposition, 3.2.21 and
    the proved critical-fibre estimate remove its pure part. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  NormMetricScaleContinuity LipschitzUP LipschitzBasic HausdorffMeasure HausdorffClosedCoverAgreement
  HausdorffFibreCutoffs CompactFibreSuperlevels CompactLipschitzFibreIntegral
  EuclideanLebesgueDimensions EuclideanLebesgueBoxes EuclideanHausdorffLebesgue
  MeasureUP MeasureBasic MeasureAlmostUP MeasureAlmostBasic BorelRegularMeasureUP TopologicalBorel
  PartialFunctionUP PartialFunctionBasic MeasureIntegralUP NonnegativeIntegralSetBound
  RectifiableSetUP RectifiablePureDecomposition PureTargetFibreNull.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

Section CompactThreshold.
Variable R:realType.
Variables m v:nat.
Local Notation X:=(inner_metric_space (@euclidean_inner_productP R m.+1)).
Local Notation Y:=(inner_metric_space (@euclidean_inner_productP R v)).

(** Source for [compact_fibre_threshold_rectifiable]: the compact
    source reduction of Federer 3.2.31, pp. 268–269. The
    printed non-strict positive threshold is retained, and its
    Borelness and finite mass are proved before decomposition.
    The purely unrectifiable part is null by the actual rank
    theorem and critical-fibre estimate. No threshold measurability,
    target rectifiability or finite fibre mass is assumed. *)
Theorem compact_fibre_threshold_rectifiable (F:X->Y) (K:set X) L k mu (lambda:R):
  (0<v)%N ->(0<mu)%N ->m.+1=(k+mu)%N ->(0<lambda)%R ->
  is_metric_lipschitz_bound setT F L ->compact K ->
  borel_set [set y|lambda%:E<=hausdorff_fibre_mass F K k y] /\
  is_measure_m_rectifiable (@hausdorff_measure R Y mu) mu
    [set y|lambda%:E<=hausdorff_fibre_mass F K k y].
Proof.
move=>hv hmu hDim hLambda hLip hK.
pose Z:set Y:=[set y|lambda%:E<=hausdorff_fibre_mass F K k y].
pose beta:=@hausdorff_measure R Y mu.
have hb:is_measure beta:=@hausdorff_measure_is_measure R Y mu.
have hCont:continuous F.
  apply:(metric_fixed_lipschitz_continuous hLip.1)=>x y.
  exact (hLip.2 x y Logic.I Logic.I).
have hZ:borel_set Z:=@compact_fibre_mass_closed_superlevel_borel R X Y F K k lambda hCont hK.
have hSource:@hausdorff_measure R X (k+mu) K< +oo.
  rewrite -hDim (euclidean_hausdorff_spherical_lebesgue K).1.
  exact:euclidean_compact_finite hK.
have [P [hP hPBound]]:=metric_lipschitz_of_bound hLip.
have hPLocal:is_metric_lipschitz_bound K F P.
  exact (@metric_lipschitz_bound_restrict R X Y setT K F P (fun _ _=>Logic.I) hPBound).
have [a [hI [ha hBound]]]:=@compact_lipschitz_fibre_integral_finite_bound R m.+1 v
  F K k mu P hK hSource hP hPLocal.
have hPos y:0<=hausdorff_fibre_mass F K k y.
  exact (@measure_nonnegative R X (@hausdorff_measure R X k) (@hausdorff_measure_is_measure R X k)
    (K `&` F @^-1` [set y])).
have hMarkov:=@nonnegative_integral_arbitrary_set_bound R Y beta hb
  (hausdorff_fibre_mass F K k) Z lambda a%:E hPos hLambda (fun y hy=>hy) hI.
have hFinite:beta Z< +oo.
  case hMass:(beta Z)=>[s| |]; [exact:ltry| |by []].
  move:hMarkov; by rewrite hMass gt0_muley ?lte_fin // leNgt ltry.
have hClosed A (hA:closed A):measure_measurable beta A.
  exact (borel_regular_borel_measurable hb (@hausdorff_measure_borel_regular R Y mu) (closed_borel_set hA)).
have [B [hB [hBRect hPure]]]:=@rectifiable_pure_borel_decomposition R Y beta mu Z hb hFinite hClosed.
pose T:=Z `\` B.
have hT:borel_set T:=borel_set_difference hZ hB.
pose A:=K `&` F @^-1` T.
have hAT:A `<=` F @^-1` T by move=>x [_ hx].
have hNull:=@pure_target_fibres_almost_null R m v F A T L k mu
  hv hmu hDim hLip hT hPure hAT.
have hTFibre y (hy:T y):hausdorff_fibre_mass F A k y=hausdorff_fibre_mass F K k y.
  rewrite /hausdorff_fibre_mass; congr (hausdorff_measure k _).
  apply/seteqP; split=>x.
  - by move=>[[hx _] hxy]; split.
  - move=>[hx hxy]; split=>//; split=>//.
    have he:F x=y:=hxy; by rewrite /= he.
have hTNull:beta T=0.
  apply:(measure_null_subset hb _ hNull)=>y hy hZero.
  have hLevel:=hy.1.
  have hMass:hausdorff_fibre_mass F K k y=0 by rewrite -(hTFibre y hy).
  have hBad:lambda%:E<=0 by rewrite -hMass.
  move:hBad; by rewrite lee_fin leNgt hLambda.
split; first exact hZ.
split; last exact hFinite.
split; first exact hb.
exists B; split; first exact hBRect.
exact hTNull.
Qed.
End CompactThreshold.
