(** Federer (1969), 3.2.48, p. 284: the original
    completed measurable product X times Y has finite Hausdorff
    rectifiability. The genuinely rectifiable factor required by
    3.2.23, p. 260, is preserved, on either side. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp
  classical_sets constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct
  InnerProductUP InnerNorm InnerMetric ProductInner FiniteInnerChartUP
  FiniteInnerCartesianGeometry FiniteInnerCartesianChart FiniteInnerChartMeasuredImages
  FiniteInnerChartMeasureTransport FiniteInnerRectifiableCoordinates
  FiniteInnerRectifiableCartesianProduct FiniteMeasureRectifiableImages
  RectifiableSetUP RectifiableCompletedCartesianProduct RectifiableCartesianProductUP
  LipschitzUP LipschitzBasic LipschitzRectifiableImages HausdorffMeasure
  HausdorffIsometryMeasurability MeasureUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [finite_inner_completed_cartesian_product]: supporting
    3.2.23 in the first paragraph of 3.2.48,
    p. 284, in the actual Cartesian inner metric.
    The first original factor is genuinely rectifiable; both
    original factors are only assumed completed measurable. *)
Theorem finite_inner_completed_cartesian_product (R:realType) (V W:lmodType R)
    B C (hB:@is_inner_product R V B) (hC:@is_inner_product R W C) n v
    (e:Hom (R_n R n) V) (p:Hom V (R_n R n))
    (f:Hom (R_n R v) W) (q:Hom W (R_n R v)) r mu (E:set V) (Z:set W):
  is_finite_inner_chart B e p ->is_finite_inner_chart C f q ->
  @is_m_rectifiable R (inner_metric_space hB) r E ->
  measure_measurable (@hausdorff_measure R (inner_metric_space hB) r) E ->
  is_measure_m_rectifiable (@hausdorff_measure R (inner_metric_space hC) mu) mu Z ->
  measure_measurable (@hausdorff_measure R (inner_metric_space hC) mu) Z ->
  is_measure_m_rectifiable (@hausdorff_measure R
    (inner_metric_space (product_inner_productP hB hC)) (r+mu)) (r+mu)%N
      [set z:V*W|E z.1 /\Z z.2] /\
  measure_measurable (@hausdorff_measure R
    (inner_metric_space (product_inner_productP hB hC)) (r+mu)) [set z:V*W|E z.1 /\Z z.2].
Proof.
move=>hV hW hE hEM hZ hZM.
have hEC:=rectifiable_lipschitz_image
  (@finite_inner_chart_inverse_lipschitz R V B hB n e p E hV) hE.
have hEMC:=@finite_inner_chart_coordinates_measurable R V B hB n e p r E hV hEM.
have hZC:=@finite_inner_chart_measure_rectifiable_coordinates R W C hC v f q mu Z hW hZ.
have hZMC:=@finite_inner_chart_coordinates_measurable R W C hC v f q mu Z hW hZM.
have [hProduct hMeas]:=rectifiable_completed_cartesian_product hEC hEMC hZC hZMC.
have hChart:=finite_inner_cartesian_chart hB hC hV hW.
have hImage:finite_inner_cartesian_direct e f @`
    (EuclideanCartesianMap.euclidean_cartesian_set (p @` E) (q @` Z))=
    [set z:V*W|E z.1 /\Z z.2].
  have hMap:(fun z=>finite_inner_cartesian_direct e f z)=finite_inner_cartesian_parametrization e f.
    exact (funext (finite_inner_cartesian_directE e f)).
  apply:(eq_trans (congr1 (fun F:R_n R (n+v)->(V*W)%type=>
    F @` (EuclideanCartesianMap.euclidean_cartesian_set (p @` E) (q @` Z))) hMap)).
  exact (@finite_inner_cartesian_parametrization_image R V W B C n v e p f q E Z hV hW).
split.
- have [L [_ hBound]]:=@finite_inner_cartesian_parametrization_lipschitz R V W B C hB hC n v e p f q hV hW.
  have hLip:@is_metric_lipschitz R (inner_metric_space (@euclidean_inner_productP R (n+v)))
      (inner_metric_space (product_inner_productP hB hC))
      (EuclideanCartesianMap.euclidean_cartesian_set (p @` E) (q @` Z))
      (finite_inner_cartesian_direct e f).
    apply:metric_lipschitz_of_bound; split; first exact hBound.1.
    move=>x y hx hy; rewrite !finite_inner_cartesian_directE.
    exact (hBound.2 x y I I).
  have hResult:=hausdorff_measure_rectifiable_lipschitz_image hLip
    (rectifiable_cartesian_rectifiability_law hProduct).
  by rewrite hImage in hResult.
- have hResult:=@finite_inner_chart_image_measurable R [the lmodType R of (V*W)%type]
    (product_inner hB hC) (product_inner_productP hB hC) (n+v)%N
    (finite_inner_cartesian_direct e f) (finite_inner_cartesian_inverse p q)
    (r+mu)%N _ hChart hMeas.
  by rewrite hImage in hResult.
Qed.

(** Source for [finite_inner_completed_cartesian_product_right]:
    the actual X times Y in 3.2.48, p. 284,
    with genuinely rectifiable Y. An actual Cartesian isometry
    exchanges the factors and preserves completed measurability;
    the first factor is not silently made genuinely rectifiable. *)
Theorem finite_inner_completed_cartesian_product_right (R:realType) (V W:lmodType R)
    B C (hB:@is_inner_product R V B) (hC:@is_inner_product R W C) n v
    (e:Hom (R_n R n) V) (p:Hom V (R_n R n))
    (f:Hom (R_n R v) W) (q:Hom W (R_n R v)) r mu (E:set V) (Z:set W):
  is_finite_inner_chart B e p ->is_finite_inner_chart C f q ->
  is_measure_m_rectifiable (@hausdorff_measure R (inner_metric_space hB) r) r E ->
  measure_measurable (@hausdorff_measure R (inner_metric_space hB) r) E ->
  @is_m_rectifiable R (inner_metric_space hC) mu Z ->
  measure_measurable (@hausdorff_measure R (inner_metric_space hC) mu) Z ->
  is_measure_m_rectifiable (@hausdorff_measure R
    (inner_metric_space (product_inner_productP hB hC)) (r+mu)) (r+mu)%N
      [set z:V*W|E z.1 /\Z z.2] /\
  measure_measurable (@hausdorff_measure R
    (inner_metric_space (product_inner_productP hB hC)) (r+mu)) [set z:V*W|E z.1 /\Z z.2].
Proof.
move=>hV hW hE hEM hZ hZM.
have [hRect hMeas]:=@finite_inner_completed_cartesian_product R W V C B hC hB v n
  f q e p mu r Z E hW hV hZ hZM hE hEM.
pose P:=inner_metric_space (product_inner_productP hC hB).
pose Q:=inner_metric_space (product_inner_productP hB hC).
pose swap:=fun z:P=>((z.2,z.1):Q).
pose unswap:=fun z:Q=>((z.2,z.1):P).
have hLeft:cancel swap unswap by move=>[x y].
have hRight:cancel unswap swap by move=>[x y].
have hDistance x y:@mdist R Q (swap x) (swap y)=@mdist R P x y.
  rewrite !inner_metric_distanceE.
  change (inner_norm (product_inner_productP hB hC) (x.2-y.2,x.1-y.1)=
    inner_norm (product_inner_productP hC hB) (x-y)).
  exact (product_inner_swap_norm hC hB (x-y)).
have hImage:swap @` [set z:W*V|Z z.1 /\E z.2]=[set z:V*W|E z.1 /\Z z.2].
  apply/seteqP; split=>z.
  - by move=>[w [hwZ hwE] <-]; split.
  - move=>[hzE hzZ]; exists (z.2,z.1); first by split.
    exact (esym (surjective_pairing z)).
have hLip:@is_metric_lipschitz R P Q [set z:W*V|Z z.1 /\E z.2] swap.
  apply:metric_lipschitz_of_bound; split; first exact:ler01.
  by move=>x y _ _; rewrite hDistance mul1r.
have hResult:=hausdorff_measure_rectifiable_lipschitz_image hLip hRect.
have hResultMeas:=@hausdorff_bijective_isometry_measurable R P Q swap unswap
  hLeft hRight hDistance (mu+r)%N _ hMeas.
by rewrite hImage (addnC mu r) in hResult hResultMeas; split.
Qed.
