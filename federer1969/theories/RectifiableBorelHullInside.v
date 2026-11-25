(** Federer (1969), 2.1.4, p. 56, and
    3.2.25, p. 261: a finite rectifiable
    original set has a Borel rectifiable measure hull
    inside any prescribed Borel containing set. Supporting
    the two actual hulls in 3.2.47(3), p. 283. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  RectifiableSetUP RectifiableBorelMeasureHull MeasureRectifiableSubset
  HausdorffMeasure HausdorffClosedCoverAgreement MeasureUP MeasureBasic MeasureHull
  BorelRegularMeasureUP TopologicalBorel BorelFamilyBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [rectifiable_borel_measure_hull_inside]: the
    Borel hull reduction of 3.2.25, p. 261,
    restricted by the actual hull test law of 2.1.4,
    p. 56; supporting 3.2.47(3), p. 283.
    No null difference from the original set is asserted. *)
Theorem rectifiable_borel_measure_hull_inside (R:realType) n m (E K:set (R_n R n)):
  is_measure_m_rectifiable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R n)) m) m E ->
  @borel_set (inner_metric_space (@euclidean_inner_productP R n)) K ->E `<=` K ->
  exists M:set (R_n R n),
    @borel_set (inner_metric_space (@euclidean_inner_productP R n)) M /\
    is_measure_hull (@hausdorff_measure R
      (inner_metric_space (@euclidean_inner_productP R n)) m) E M /\
    is_measure_m_rectifiable (@hausdorff_measure R
      (inner_metric_space (@euclidean_inner_productP R n)) m) m M /\M `<=` K.
Proof.
move=>hRect hK hEK.
pose X:=inner_metric_space (@euclidean_inner_productP R n).
pose H:=@hausdorff_measure R X m.
have hH:=@hausdorff_measure_is_measure R X m.
have [B [hB [hHull hRB]]]:=rectifiable_borel_measure_hull hRect.
pose M:=B `&` K.
have hMB:@borel_set X M:=borel_family_binary_intersection (borel_sets_family X) hB hK.
have hEM:E `<=` M.
  move=>x hx; exact (conj (@measure_hull_subset R X H E B hHull x hx) (hEK x hx)).
have hEqual:H E=H M.
  have hKM:=measure_hull_test hHull
    (borel_regular_borel_measurable hH (@hausdorff_measure_borel_regular R X m) hK).
  have hKE:K `&` E=E.
    apply/seteqP; split=>x; first by move=>[_ hx].
    by move=>hx; split; first exact:hEK x hx.
  by rewrite hKE setIC in hKM.
have hMMeas:=borel_regular_borel_measurable hH (@hausdorff_measure_borel_regular R X m) hMB.
exists M; split; first exact hMB.
split.
- exact (measure_hull_of_finite_equal_measure hH hEM hMMeas hEqual hRect.2).
- split; last by move=>x hx; exact hx.2.
  exact (@measure_rectifiable_subset R X H m B M (fun x hx=>hx.1) hRB).
Qed.
