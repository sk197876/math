(** Federer (1969), 3.2.26(3), p. 262: the
    Hausdorff mass of a finite rectifiable Borel set is
    bounded by every integral-geometric measure. Sum the
    actual Borel tangent-field partition and remove its
    uniform error using finite source mass. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct EuclideanLinearMaps InnerMetric
  InnerExterior InnerExteriorPositivity ExteriorGrading ExteriorNorm AssociatedSubspace
  RectifiableSetUP RectifiableOrientationUP RectifiableOrientationPartitions BorelPartialSmallPartition
  RectifiableOrientationPieceNorm RectifiableConvexGeometricUpper RectifiableGeometricBasicComparisons
  IntegralGeometricMeasure ProjectionBeta HausdorffMeasure HausdorffClosedCoverAgreement
  MeasureUP MeasureBasic MeasureSplit MeasureCountableAdditivity BorelRegularMeasureUP TopologicalBorel
  NonnegativeSum NonnegativeSumScale NonnegativeSumAdd ExtendedScaledErrorBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [borel_rectifiable_geometric_lower_error]: the
    partition sum in 3.2.26(3), p. 262, before
    delta tends to zero. Empty Borel pieces contribute
    zero and require no unit-vector assertion about their
    unused centres. The omitted source set is Hausdorff-null. *)
Lemma borel_rectifiable_geometric_lower_error (R:realType) m n
    (hmn:(m<=n)%N) (W:set (R_n R n)) (t: \bar R) (d:R):
  is_measure_m_rectifiable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R n)) m) m W ->
  @borel_set (inner_metric_space (@euclidean_inner_productP R n)) W ->1<=t ->(0<d)%R ->
  (@projection_beta R n m hmn t)%:E*
    @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m W<=
  (@projection_beta R n m hmn t)%:E*@integral_geometric_measure R n m hmn t W+d%:E*
    @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m W.
Proof.
move=>hRect hW ht hd.
pose X:=inner_metric_space (@euclidean_inner_productP R n).
pose H:=@hausdorff_measure R X m.
pose I:=@integral_geometric_measure R n m hmn t.
pose beta:=@projection_beta R n m hmn t.
have hH:=@hausdorff_measure_is_measure R X m.
have hI:=@integral_geometric_measure_is_measure R n m hmn t ht.
have hBeta:(0<beta)%R:=@projection_beta_positive R n m hmn t ht.
have [T [P [c [hT [hP [hCentres hNull]]]]]]:=
  @rectifiable_orientation_borel_partitions R m n W d hRect hW hd.
pose U:=\bigcup_i P i.
have hPW i:P i `<=` W.
  move=>x hx; have hUnion:U x by exists i.
  rewrite /U hP.2.2.1 in hUnion; exact hUnion.1.
have hUW:U `<=` W by move=>x [i _ hx]; exact:hPW i x hx.
have hHMeas i:measure_measurable H (P i).
  exact:(borel_regular_borel_measurable hH (@hausdorff_measure_borel_regular R X m) (hP.1 i)).
have hIMeas i:measure_measurable I (P i).
  exact:(borel_regular_borel_measurable hI (@integral_geometric_measure_borel_regular R n m hmn t ht) (hP.1 i)).
have hApart i j:i!=j ->forall x,P i x ->P j x ->False:=hP.2.1 i j.
have hHUnion:H U=H W.
  apply/eqP; rewrite eq_le (measure_mono hH hUW) /=.
  have hSplit:=measure_split_upper hH W U.
  have hIntersection:W `&` U=U.
    apply/seteqP; split; first by move=>x [_ hx].
    by move=>x hx; split; first exact:hUW x hx.
  rewrite hIntersection hNull adde0 in hSplit; exact hSplit.
have hPiece i:beta%:E*H (P i)<=beta%:E*I (P i)+d%:E*H (P i).
  have [hEmpty|hNonempty]:=pselect (P i=set0).
  - by rewrite hEmpty /H /I (measure_empty hH) (measure_empty hI) !mule0 adde0.
  - have hNE:P i !=set0.
      have [h|h]:=pselect (P i !=set0); first exact h.
      exfalso; exact:hNonempty ((nonemptyPn (P i)).1 h).
    have [hSimple hUnit]:=hCentres i hNE.
    apply:(@rectifiable_orientation_piece_norm_lower R m n hmn W (P i) T (c i) d t
      hRect hW (hP.1 i) (hPW i) hT hSimple hUnit (ltW hd) ht)=>w eta hw hValue.
    exact:(hP.2.2.2.2 i w eta hw hValue).
have hSum:=@nonnegative_sum_mono R [the choiceType of (nat:Type)] setT
  (fun i=>beta%:E*H (P i)) (fun i=>beta%:E*I (P i)+d%:E*H (P i)) (fun i _=>hPiece i).
rewrite (@nonnegative_sum_scale R [the choiceType of (nat:Type)] setT (fun i=>H (P i)) beta
  (ltW hBeta) (fun i _=>measure_nonnegative hH (P i))) in hSum.
rewrite (@nonnegative_sum_add R [the choiceType of (nat:Type)] setT
  (fun i=>beta%:E*I (P i)) (fun i=>d%:E*H (P i))
  (fun i _=>mule_ge0 (lee_tofin (ltW hBeta)) (measure_nonnegative hI (P i)))
  (fun i _=>mule_ge0 (lee_tofin (ltW hd)) (measure_nonnegative hH (P i)))) in hSum.
rewrite (@nonnegative_sum_scale R [the choiceType of (nat:Type)] setT (fun i=>I (P i)) beta
  (ltW hBeta) (fun i _=>measure_nonnegative hI (P i)))
  (@nonnegative_sum_scale R [the choiceType of (nat:Type)] setT (fun i=>H (P i)) d
  (ltW hd) (fun i _=>measure_nonnegative hH (P i))) in hSum.
rewrite -(@measure_sequence_disjoint_additivity R (Choice.clone X _) H hH P hHMeas hApart)
  -(@measure_sequence_disjoint_additivity R (Choice.clone X _) I hI P hIMeas hApart)
  hHUnion in hSum.
exact:(le_trans hSum (leeD2r (d%:E*H W)
  (lee_wpmul2l (lee_tofin (ltW hBeta)) (measure_mono hI hUW)))).
Qed.

(** Source for [borel_rectifiable_geometric_lower]: conclusion
    H^m(W)<=I_t^m(W) in 3.2.26(3), p. 262,
    for Borel W. Finite Hausdorff mass and the separately
    proved I_t<=Q_t<=H^m make the vanishing-error argument
    valid without cancelling an infinite quantity. *)
Theorem borel_rectifiable_geometric_lower (R:realType) m n
    (hmn:(m<=n)%N) (W:set (R_n R n)) (t: \bar R):
  is_measure_m_rectifiable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R n)) m) m W ->
  @borel_set (inner_metric_space (@euclidean_inner_productP R n)) W ->1<=t ->
  @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m W<=
    @integral_geometric_measure R n m hmn t W.
Proof.
move=>hRect hW ht.
pose X:=inner_metric_space (@euclidean_inner_productP R n).
pose H:=@hausdorff_measure R X m.
pose I:=@integral_geometric_measure R n m hmn t.
pose beta:=@projection_beta R n m hmn t.
have hH:=@hausdorff_measure_is_measure R X m.
have hI:=@integral_geometric_measure_is_measure R n m hmn t ht.
have hBeta:(0<beta)%R:=@projection_beta_positive R n m hmn t ht.
have hIUpper:I W<=H W.
  exact:(le_trans (@integral_geometric_le_convex R n m hmn t W ht)
    (@rectifiable_convex_geometric_upper R m n hmn W t hRect ht)).
have hHFin:H W \is a fin_num by rewrite (ge0_fin_numE (measure_nonnegative hH W)); exact hRect.2.
have hIFin:I W \is a fin_num.
  rewrite (ge0_fin_numE (measure_nonnegative hI W)).
  exact:(le_lt_trans hIUpper hRect.2).
pose b:R:=fine (H W).
pose a:R:=fine (I W).
have hMass:H W=b%:E by rewrite /b fineK.
have hIMass:I W=a%:E by rewrite /a fineK.
have hb:(0<=b)%R.
  have h:=measure_nonnegative hH W.
  change (is_true (0<=H W)) in h; by rewrite hMass lee_fin in h.
have hLimit:beta%:E*H W<=(beta*a)%R%:E.
  apply:(@extended_upper_bound_from_scaled_errors R (beta%:E*H W) (beta*a)%R b hb)=>d hd.
  have h:=@borel_rectifiable_geometric_lower_error R m n hmn W t d hRect hW ht hd.
  change (is_true (beta%:E*H W<=beta%:E*I W+d%:E*H W)) in h.
  rewrite hIMass hMass -!EFinM -EFinD in h.
  rewrite hMass -EFinM [(b*d)%R]mulrC; exact h.
rewrite hMass -EFinM lee_fin in hLimit.
change (is_true (H W<=I W)).
rewrite hMass hIMass lee_fin.
by rewrite (ler_pM2l hBeta) in hLimit.
Qed.
