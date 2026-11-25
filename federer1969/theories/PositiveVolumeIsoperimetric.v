(** Federer (1969), 3.2.43, printed p. 278:
    assemble the original two-strip proof once the actual
    boundary is ambient-null and the closure volume is
    positive finite. This includes the positive-volume line
    case without a reciprocal-zero or zero-base convention. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology ring.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanLebesgueDimensions
  EuclideanBallVolume RealPower MinkowskiContents MinkowskiContentsBasic
  MetricOpenThickening EuclideanInnerCoreBasic OuterBoundaryLayerVolume InnerBoundaryLayerVolume
  EuclideanInnerCoreVolumeApproximation PositivePowerContractionApproximation
  EuclideanBoundaryStripsVolume BoundaryNullInteriorVolume PositiveRadiusLowerApproximation
  ExtendedContractionSqueeze FiniteOpenBoxUnionBounds MeasureUP MeasureBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [positive_volume_null_boundary_isoperimetric]:
    supporting positive-volume branch of Federer 3.2.43,
    p. 278. Ambient boundary nullity is discharged from
    finite lower Minkowski content in the numbered theorem.
    The original arbitrary S, positive ambient dimension,
    actual cores and full positive-real-radius lower limit
    are retained. *)
Theorem positive_volume_null_boundary_isoperimetric (R:realType) k
    (S:set (inner_metric_space (@euclidean_inner_productP R k.+1))) (a:R):
  @euclidean_lebesgue_measure R k.+1 (closure S)=a%:E ->0<a ->
  @euclidean_lebesgue_measure R k.+1 (closure S `\` interior S)=0%E ->
  (((k.+1)%:R*real_power (euclidean_unit_ball_volume R k.+1) ((k.+1)%:R)^-1*
    real_power a (k%:R/(k.+1)%:R))%:E<=
      lower_minkowski_content k (closure S `\` interior S))%E.
Proof.
move=>hMass ha hNull.
pose E:=inner_metric_space (@euclidean_inner_productP R k.+1).
pose mu:=@euclidean_lebesgue_measure R k.+1.
pose p:R:=k%:R/(k.+1)%:R.
pose c:R:=(k.+1)%:R*real_power (euclidean_unit_ball_volume R k.+1) ((k.+1)%:R)^-1.
pose K:R:=c*real_power a p.
pose B:=closure S `\` interior S.
have hm:=euclidean_lebesgue_is_measure R k.+1.
have hp:0<=p by rewrite /p divr_ge0 ?ler0n.
have hc:0<c.
  apply:mulr_gt0; first by rewrite ltr0n.
  exact:real_power_strictly_positive _ (euclidean_unit_ball_volumeE R k.+1).2.
have hK:0<=K:=mulr_ge0 (ltW hc) (real_power_nonnegative _ _).
have hFinite:(mu (closure S) < +oo)%E by rewrite /mu hMass ltry.
have hSNe:S !=set0.
  apply:contrapT=>hNoPoint.
  have hSet:S=set0.
    apply/seteqP; split; last by move=>x [].
    move=>x hx; apply:hNoPoint; by exists x.
  have h:=hMass; rewrite hSet closure0 (measure_empty hm) in h.
  have hZero:(0:R)=a by move/eqP:h; rewrite eqe=>/eqP.
  by rewrite -hZero ltxx in ha.
have hInteriorMass:mu (interior S)=a%:E.
  rewrite /mu -(boundary_null_interior_closure_volume hNull); exact hMass.
change (is_true (K%:E<=lower_minkowski_content k B)%E).
apply:(@extended_contraction_squeeze R K%:E (lower_minkowski_content k B)
  (minkowski_contents_nonnegative k B).1)=>t ht.
have [q [hq0 [hqa hqPower]]]:=positive_power_contraction_threshold_exists ha hp ht.
have hQ:(q%:E<mu (interior S))%E by rewrite hInteriorMass lte_fin.
have [d [hd hCoreVolume]]:=euclidean_inner_core_volume_eventual_lower hQ.
apply:(@positive_radius_lower_eventual_bound R (minkowski_tube_quotient k B)
  (t%:E*K%:E) d hd)=>r /andP[hr hrd].
have hSmall:0<r<d by apply/andP.
pose T:set E:=~`metric_open_thickening (~`S) r.
have hAboveQ:(q%:E<mu T)%E:=hCoreVolume r hSmall.
have hQ0E:(0<q%:E)%E by rewrite lte_fin.
have hTPos:(0<mu T)%E:=lt_trans hQ0E hAboveQ.
have hTNe:T !=set0:=positive_measure_set_nonempty hm hTPos.
have hTS:T `<=` S:=positive_inner_core_subset hr.
have hTC:T `<=` closure S by move=>x hx; exact:subset_closure (hTS x hx).
have hTF:(mu T < +oo)%E:=le_lt_trans (@measure_mono R E mu hm _ _ hTC) hFinite.
have hTFin:mu T \is a fin_num by rewrite (ge0_fin_numE (measure_nonnegative hm T)); exact hTF.
pose b:R:=fine (mu T).
have hTValue:mu T=b%:E by rewrite /b fineK.
have hqb:q<=b by move:hAboveQ; rewrite hTValue lte_fin=>/ltW.
have hPower:real_power q p<=real_power b p:=nonnegative_exponent_power_monotone (ltW hq0) hqb hp.
have hInnerCoefficient:t*K<=c*real_power b p.
  have h:=ler_wpM2l (ltW hc) (le_trans hqPower hPower).
  have hEq:c*(t*real_power a p)=t*K by rewrite /K mulrCA.
  by rewrite hEq in h.
have hOuter:=@outer_boundary_layer_volume_nonempty R k S r hSNe hFinite hr.
have hInner:=@inner_boundary_layer_volume_nonempty_core R k S r hTNe hFinite hr.
rewrite hMass in hOuter.
have hOuterBound:((K*r)%:E<=mu (metric_open_thickening S r `\` closure S))%E.
  change (is_true (K%:E<=mu (metric_open_thickening S r `\` closure S)*r^-1%:E)%E) in hOuter.
  by rewrite (lee_pdivlMr _ _ hr) -EFinM in hOuter.
have hInnerBound:(((t*K)*r)%:E<=mu (interior S `\` T))%E.
  change (is_true ((c*real_power b p)%:E<=mu (interior S `\` T)*r^-1%:E)%E) in hInner.
  have hCoefficientE:((t*K)%:E<=(c*real_power b p)%:E)%E by rewrite lee_fin.
  have h:=le_trans hCoefficientE hInner.
  by rewrite (lee_pdivlMr _ _ hr) -EFinM in h.
have hBound:=@euclidean_boundary_two_strip_quotient_bound R k S r K (t*K) hr hOuterBound hInnerBound.
have hHalf:t*K<=(K+t*K)/2.
  have ht1:t<=1:=ltW (andP ht).2.
  have hTK:t*K<=K by have h:=ler_wpM2r hK ht1; by rewrite mul1r in h.
  rewrite ler_pdivlMr //.
  have hEq:t*K*2=t*K+t*K by ring.
  rewrite hEq; exact:lerD hTK (lexx _).
have hHalfE:((t*K)%:E<=((K+t*K)/2)%:E)%E by rewrite lee_fin.
rewrite -EFinM; exact:(le_trans hHalfE hBound).
Qed.
