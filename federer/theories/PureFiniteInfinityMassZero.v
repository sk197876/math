(** Federer (1969), 3.3.20, p. 306:
    the original pure example has no subset of
    positive finite infinity-integral-geometric mass. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric HausdorffMeasure HausdorffClosedCoverAgreement
  RectifiableSetUP RectifiableElementary PureCountablyRectifiableNull
  StructureInfinityRectifiability StructureHausdorffNullProjection StructureProjectionConditions
  IntegralGeometricMeasure IntegralGeometricNullSets OrthogonalProjectionProbability
  MeasureUP MeasureBasic MeasureSplit MeasureAlmostUP MeasureAlmostBasic
  BorelRegularMeasureUP TopologicalBorel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [original_hausdorff_null_integral_geometric]:
    the null-set comparison used with 3.2.26 in
    3.3.20, p. 306. Every original H^m-null
    set is I_t^m-null for every exponent including
    infinity. A genuine equal-mass Borel hull and
    actual null projections prove the comparison. *)
Lemma original_hausdorff_null_integral_geometric (R:realType) n m (hmn:(m<=n)%N)
    (A:set (inner_metric_space (@euclidean_inner_productP R n))) (t: \bar R):
  @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m A=0 ->
  1<=t ->@integral_geometric_measure R n m hmn t A=0.
Proof.
move=>hNull ht.
pose X:=inner_metric_space (@euclidean_inner_productP R n).
pose H:=@hausdorff_measure R [the metricType R of X] m.
have [B [hAB [hB hEqual]]]:=borel_regular_cover (@hausdorff_measure_borel_regular R X m) A.
have hBNull:H B=0 by rewrite /H -hEqual.
apply:(@integral_geometric_projection_null_iff R n m hmn t A ht).2.
exists B;split=>//;split=>//.
have hTheta:=@theta_star_is_measure R n m hmn.
apply:(measure_almost_everywhere_mono hTheta _ (measure_almost_everywhere_true hTheta))=>p _.
exact:(@structure_hausdorff_null_projection R n m B p B (fun _ h=>h) hBNull).
Qed.

(** Source for [pure_original_finite_infinity_mass_zero]:
    the actual 3.3.14 and 3.2.26 consequence
    in 3.3.20, p. 306. Every original subset
    F of a purely (H^m,m) unrectifiable E has
    I_infinity^m(F)=0 whenever that mass is finite.
    E need not have finite H^m mass; neither E
    nor F is assumed measurable. *)
Theorem pure_original_finite_infinity_mass_zero (R:realType) n m (hmn:(m<=n)%N)
    (E F:set (inner_metric_space (@euclidean_inner_productP R n))):
  is_purely_measure_m_unrectifiable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R n)) m) m E ->
  F `<=` E ->@integral_geometric_measure R n m hmn +oo F< +oo ->
  @integral_geometric_measure R n m hmn +oo F=0.
Proof.
move=>hPure hFE hFinite.
pose X:=inner_metric_space (@euclidean_inner_productP R n).
pose I:=@integral_geometric_measure R n m hmn +oo.
have hI:is_measure I:=@integral_geometric_measure_is_measure R n m hmn +oo (leey 1).
have [[_ [B [hRect hNull]]] _]:=@federer_3_3_14 R n m hmn F hFinite.
have hSubset:(F `&` B) `<=` E by move=>x [hx _];exact:hFE x hx.
have hRectPart:is_countably_m_rectifiable m (F `&` B).
  apply:(countably_rectifiable_subset _ hRect);by move=>x [_ hx].
have hHNull:=pure_countably_rectifiable_subset_null hPure hSubset hRectPart.
have hINull:=@original_hausdorff_null_integral_geometric R n m hmn (F `&` B) +oo hHNull (leey 1).
have hCover:F `<=` (F `&` B) `|` (F `\` B).
  move=>x hx;case:(pselect (B x))=>hB;[left|right];by split.
have hBound:=@measure_binary_cover R X I hI _ _ _ hCover.
change (I (F `\` B)=0) in hNull.
change (I (F `&` B)=0) in hINull.
apply/eqP;rewrite eq_le (measure_nonnegative hI) andbT.
by rewrite hINull hNull adde0 in hBound.
Qed.
