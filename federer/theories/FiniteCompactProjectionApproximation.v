(** Federer (1969), 3.2.37, p. 274: replace the finitely
    many Borel partition costs by actual projected compact source
    pieces, with one finite total error. The supporting approximation
    keeps the independent projected-volume gauge and all witness
    choices local. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology lra.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  EuclideanLebesgueDimensions CoordinateProjection ProjectedVolumeGauge CompactProjectedVolumeDetection
  SuslinSetUP MeasureUP MeasureBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [finite_compact_projection_approximation]: the
    finite cost approximation in the compact-family characterization
    cited in Federer 3.2.37, p. 274. Finite original gauge values
    suffice; source pieces need only be Suslin, and all compact
    source/projection witnesses are proved to exist. *)
Theorem finite_compact_projection_approximation (R:realType) n m
    (I:finType) (S:I->set (inner_metric_space (@euclidean_inner_productP R n))) (e:R):
  (m<=n)%N ->(forall i,is_suslin_set R (S i)) ->
  (forall i,projected_volume_gauge m (S i)< +oo) ->(0<e)%R ->
  exists (K:I->set (inner_metric_space (@euclidean_inner_productP R n)))
    (p:I->{linear R_n R n->R_n R m}),
    (forall i,compact (K i) /\ K i `<=` S i /\ O_star (p i)) /\
    (\sum_i projected_volume_gauge m (S i))<=
      (\sum_i @euclidean_lebesgue_measure R m (p i @` K i))+e%:E.
Proof.
move=>hmn hS hFinite he.
pose delta:=(e/(#|I|.+1)%:R)%R.
have hCard:(0<((#|I|.+1)%:R:R))%R by rewrite ltr0n.
have hDelta:(0<delta)%R by rewrite /delta divr_gt0.
have hGaugeFinite i:projected_volume_gauge m (S i) \is a fin_num.
  rewrite ge0_fin_numE //; exact:projected_volume_gauge_nonnegative.
pose a i:=fine (projected_volume_gauge m (S i)).
have hGauge i:projected_volume_gauge m (S i)=(a i)%:E by rewrite /a fineK.
have hex i:exists (K:set (inner_metric_space (@euclidean_inner_productP R n)))
    (p:{linear R_n R n->R_n R m}),
    [/\ compact K,K `<=` S i,O_star p & (a i-delta)%:E<@euclidean_lebesgue_measure R m (p @` K)].
  apply:projected_volume_gauge_compact_detection (hS i) _.
  rewrite hGauge lte_fin ltrBlDr ltrDl; exact:hDelta.
pose K i:=projT1 (cid (hex i)).
pose p i:=projT1 (cid (projT2 (cid (hex i)))).
have hSpec i:[/\ compact (K i),K i `<=` S i,O_star (p i) &
    (a i-delta)%:E<@euclidean_lebesgue_measure R m (p i @` K i)].
  exact:projT2 (cid (projT2 (cid (hex i)))).
pose mass i:=@euclidean_lebesgue_measure R m (p i @` K i).
have hMassBound i:mass i<=projected_volume_gauge m (S i).
  have [_ hKS hp _]:=hSpec i.
  exact:le_trans (projected_volume_gauge_projection_bound (K i) hp)
    (projected_volume_gauge_mono m hKS).
have hMassFinite i:mass i \is a fin_num.
  rewrite ge0_fin_numE; last exact:(@measure_nonnegative R
    (inner_metric_space (@euclidean_inner_productP R m)) (@euclidean_lebesgue_measure R m)
    (euclidean_lebesgue_is_measure R m) _).
  exact:le_lt_trans (hMassBound i) (hFinite i).
pose c i:=fine (mass i).
have hMass i:mass i=(c i)%:E by rewrite /c fineK.
have hPoint i:(a i<=c i+delta)%R.
  have [_ _ _ hi]:=hSpec i.
  rewrite -/(mass i) hMass lte_fin in hi; lra.
have hSum:(\sum_i a i<=\sum_i c i+(#|I|)%:R*delta)%R.
  have h:(\sum_i a i<=\sum_i (c i+delta))%R.
    apply:ler_sum=>i _; exact:hPoint.
  have hConst:((\sum_(i:I) delta)=(#|I|)%:R*delta)%R.
    rewrite sumr_const cardT; exact (esym (mulr_natl delta _)).
  by rewrite big_split hConst in h.
have hError:((#|I|)%:R*delta<=e)%R.
  have hCount:(((#|I|)%:R:R)<=((#|I|.+1)%:R:R))%R by rewrite ler_nat.
  have h:=ler_wpM2r (ltW hDelta) hCount.
  have hEquality:((#|I|.+1)%:R*delta=e)%R by rewrite mulrC /delta divfK ?gt_eqF.
  by rewrite hEquality in h.
exists K,p; split.
- move=>i; have [hK hKS hp _]:=hSpec i; by split=>//; split.
- have hGaugeSum:(\sum_i projected_volume_gauge m (S i))=(\sum_i a i)%:E.
    rewrite -sumEFin; apply:eq_bigr=>i _; exact:hGauge.
  have hMassSum:(\sum_i @euclidean_lebesgue_measure R m (p i @` K i))=(\sum_i c i)%:E.
    rewrite -sumEFin; apply:eq_bigr=>i _; exact:hMass.
  rewrite hGaugeSum hMassSum -EFinD lee_fin.
  exact:le_trans hSum (lerD (lexx _) hError).
Qed.
