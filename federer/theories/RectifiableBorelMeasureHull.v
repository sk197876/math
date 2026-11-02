(** Federer (1969), 3.2.25, p. 261: justify the proof's
    initial reduction to a measurable rectifiable set. An arbitrary
    finite (H^m,m)-rectifiable W has a Borel rectifiable measure
    hull. The hull need not differ from W by a null set;
    only the printed measurable-test equalities are asserted. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets cardinality constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  RectifiableSetUP RectifiableClosedExhaustion CountablyRectifiableUnions RectifiableElementary
  HausdorffMeasure HausdorffClosedCoverAgreement MeasureUP MeasureBasic MeasureAlmostUP MeasureAlmostBasic
  MeasureHull BorelRegularMeasureUP TopologicalBorel BorelFamilyBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [rectifiable_borel_measure_hull]: supporting
    measurable-hull reduction in Federer 3.2.25, p. 261.
    Closed rectifiable covers from 3.2.14, p. 252,
    and a Borel hull of the omitted null set give a
    Borel rectifiable containing set. Intersect it with a
    same-mass Borel hull of W and use 2.1.4, p. 56. *)
Theorem rectifiable_borel_measure_hull (R:realType) m n (W:set (R_n R n)):
  is_measure_m_rectifiable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R n)) m) m W ->
  exists M:set (R_n R n),
    @borel_set (inner_metric_space (@euclidean_inner_productP R n)) M /\
    is_measure_hull (@hausdorff_measure R
      (inner_metric_space (@euclidean_inner_productP R n)) m) W M /\
    is_measure_m_rectifiable (@hausdorff_measure R
      (inner_metric_space (@euclidean_inner_productP R n)) m) m M.
Proof.
move=>[[hH [C [hC hOmit]]] hFinite].
pose X:=inner_metric_space (@euclidean_inner_productP R n).
pose H:=@hausdorff_measure R X m.
have hRegular:=@hausdorff_measure_borel_regular R X m.
have [F [hF [_ hCover]]]:=rectifiable_closed_increasing_cover hC.
pose P:=\bigcup_i F i.
have hPBorel:@borel_set X P.
  apply:(borel_set_countable_union (countableP setT))=>i _.
  exact:closed_borel_set (hF i).1.
have hPRect:@is_countably_m_rectifiable R X m P.
  apply:(countably_rectifiable_countable_union (countableP setT))=>i _.
  exact:rectifiable_countably_rectifiable (hF i).2.
have hPNull:H (W `\` P)=0.
  apply:(measure_null_subset hH _ hOmit)=>x [hx hn]; split; first exact hx.
  move=>hCx; exact:hn (hCover x hCx).
have [N [hWN [hNBorel hNMass]]]:=borel_regular_cover hRegular (W `\` P).
have hNNull:H N=0:=eq_trans (esym hNMass) hPNull.
have [B [hWB [hBBorel hBMass]]]:=borel_regular_cover hRegular W.
pose M:=B `&` (P `|` N).
have hMBorel:@borel_set X M.
  exact:(borel_family_binary_intersection (borel_sets_family X) hBBorel
    (borel_family_binary_union (borel_sets_family X) hPBorel hNBorel)).
have hWM:W `<=` M.
  move=>x hx; split; first exact:hWB x hx.
  have [hPx|hPx]:=pselect (P x); first by left.
  right; exact:hWN x (conj hx hPx).
have hMass:H W=H M.
  apply/eqP; rewrite eq_le (measure_mono hH hWM) /=.
  have hMB:M `<=` B by move=>x [hx _].
  have hUpper:=measure_mono hH hMB.
  change (is_true (@hausdorff_measure R X m M<=@hausdorff_measure R X m B)) in hUpper.
  rewrite -hBMass in hUpper; exact hUpper.
have hHull:is_measure_hull H W M.
  exact:(measure_hull_of_finite_equal_measure hH hWM
    (borel_regular_borel_measurable hH hRegular hMBorel) hMass hFinite).
have hMNull:H (M `\` P)=0.
  apply:(measure_null_subset hH _ hNNull)=>x [[_ [hPx|hNx]] hNot]; first exact:False_ind _ (hNot hPx).
  exact hNx.
exists M; split; first exact hMBorel; split; first exact hHull; split.
- split; first exact hH; exists P; by split.
- change (is_true (H M< +oo)); rewrite -hMass; exact hFinite.
Qed.
