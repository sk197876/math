(** Federer (1969), 3.4.8(13), p. 336:
    apply the coordinate projection estimate of 3.2.27
    to finite-mass pieces before asserting finite total
    mass. The increasing closed rectifiable cover of
    3.2.14, p. 252, and measure continuity from
    2.1.3(4), p. 55, justify this passage. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals
  constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  RectifiableSetUP RectifiableElementary RectifiableClosedExhaustion RectifiableFiniteHausdorffMass
  HausdorffMeasure HausdorffClosedCoverAgreement MeasureUP MeasureBasic MeasureAlmostUP
  MeasureAlmostBasic MeasureSplit MeasureFiniteClosure MeasureContinuityBelow
  BorelRegularMeasureUP TopologicalBorel StieltjesContinuityPoints.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [countably_measure_rectifiable_finite_piece_bound]:
    the finite-mass exhaustion needed in the application
    of 3.2.27 to 3.4.8(13), p. 336.
    The uniform bound on finite measurable rectifiable
    subsets bounds the whole measurable countably rectifiable
    set. No finite total mass is assumed. *)
Theorem countably_measure_rectifiable_finite_piece_bound (R:realType) n m
    (E:set (R_n R n)) (c: \bar R):
  is_countably_measure_m_rectifiable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R n)) m) m E ->
  measure_measurable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R n)) m) E ->
  (forall W:set (R_n R n),W `<=` E ->
    is_measure_m_rectifiable (@hausdorff_measure R
      (inner_metric_space (@euclidean_inner_productP R n)) m) m W ->
    measure_measurable (@hausdorff_measure R
      (inner_metric_space (@euclidean_inner_productP R n)) m) W ->
    @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m W<=c) ->
  @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m E<=c.
Proof.
move=>[hH [Z [hZ hOmit]]] hEMeas hBound.
pose X:=inner_metric_space (@euclidean_inner_productP R n).
pose H:=@hausdorff_measure R X m.
have [F [hF [hIncreasing hCover]]]:=rectifiable_closed_increasing_cover hZ.
pose B i:=E `&` F i.
have hBMeas i:measure_measurable H (B i).
  apply:(measure_measurable_intersection hH hEMeas).
  exact:(borel_regular_borel_measurable hH (@hausdorff_measure_borel_regular R X m)
    (closed_borel_set (hF i).1)).
have hBRect i:is_measure_m_rectifiable H m (B i).
  apply:rectifiable_hausdorff_measure_rectifiable.
  exact:(@rectifiable_subset R X m (F i) (B i) (fun x hx=>hx.2) (hF i).2).
have hBIncreasing i j (hij:(i<=j)%N):B i `<=` B j.
  move=>x [hx hxF];split;first exact:hx;exact:hIncreasing i j hij x hxF.
have hLimit:=@measure_continuity_below R (Choice.clone X _) H hH B hBMeas hBIncreasing.
have hUnionBound:H (\bigcup_i B i)<=c.
  apply:(extended_increases_to_le_bound hLimit)=>i.
  exact:hBound (B i) (fun x hx=>hx.1) (hBRect i) (hBMeas i).
have hMissing:H (E `\` \bigcup_i B i)=0.
  apply:(measure_null_subset hH _ hOmit)=>x [hx hNot];split;first exact:hx.
  move=>hxZ;have [i hi hxF]:=hCover x hxZ;apply:hNot;exists i;first exact:Logic.I.
  by split.
have hSplit:(H E<=H (E `&` \bigcup_i B i)+H (E `\` \bigcup_i B i))%E:=
  @MeasureSplit.measure_split_upper R (Choice.clone X _) H hH E (\bigcup_i B i).
rewrite hMissing adde0 in hSplit.
apply:(le_trans hSplit);apply:(le_trans _ hUnionBound).
apply:(measure_mono hH)=>x [_ hx];exact:hx.
Qed.
