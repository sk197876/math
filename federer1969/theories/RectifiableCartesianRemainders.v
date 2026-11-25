(** Federer (1969), 3.2.23, p. 260: remove the null omitted
    source and target pieces before countable gluing. Genuine first-factor
    rectifiability controls the product with the target-null remainder;
    the coordinate product measure uses its two null-cylinder bounds. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets cardinality constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  EuclideanBlockCoordinates EuclideanCartesianMap EuclideanCartesianAlmost
  RectifiableSetUP RectifiableElementary RectifiableCompactChartsUP
  RectifiableProductNullFactor RectifiableProductNullSource HausdorffMeasure
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasureRestriction ProductMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [rectifiable_cartesian_chart_remainder_null]: supporting
    countable image decomposition in Federer 3.2.23, p. 260.
    The complement of all pairs of compact chart images is contained
    in the source-null product and the target-null product. Both are
    proved null; actual first-factor rectifiability is retained. *)
Theorem rectifiable_cartesian_chart_remainder_null (R:realType) m mu n v (lambda:R)
    (W:set (R_n R n)) (Z:set (R_n R v))
    (K:nat->set (R_n R m)) (C:nat->set (R_n R mu))
    (psi:nat->R_n R m->R_n R n) (gamma:nat->R_n R mu->R_n R v):
  (@is_m_rectifiable R (inner_metric_space (@euclidean_inner_productP R n)) m W) ->
  is_measure_m_rectifiable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R v)) mu) mu Z ->
  is_rectifiable_compact_chart_cover lambda W K psi ->
  is_rectifiable_compact_chart_cover lambda Z C gamma ->
  @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R (n+v))) (m+mu)
    (euclidean_cartesian_set W Z `\`
      (\bigcup_(p in @setT (nat*nat)%type)
        euclidean_cartesian_set (psi p.1 @` K p.1) (gamma p.2 @` C p.2)))=0.
Proof.
move=>hW hZ hSource hTarget.
pose P:=fun i=>psi i @` K i.
pose Q:=fun j=>gamma j @` C j.
pose A:=W `\` (\bigcup_i P i).
pose B:=Z `\` (\bigcup_j Q j).
pose rho:=@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R (n+v))) (m+mu).
have hr:=@hausdorff_measure_is_measure R
  (inner_metric_space (@euclidean_inner_productP R (n+v))) (m+mu).
have hA:@is_m_rectifiable R (inner_metric_space (@euclidean_inner_productP R n)) m A.
  apply:(rectifiable_subset _ hW); by move=>x [hx _].
have hFirst:rho (euclidean_cartesian_set A Z)=0.
  exact:(rectifiable_product_null_source hA hSource.2.2 hZ.1).
have hSecond:rho (euclidean_cartesian_set W B)=0.
  exact:(rectifiable_product_null_factor hW hTarget.2.2).
apply:(measure_null_subset hr _ (measure_null_union hr hFirst hSecond))=>p [[hpW hpZ] hNot].
have [hP|hP]:=pselect ((\bigcup_i P i) (euclidean_block_split p).1).
- have [hQ|hQ]:=pselect ((\bigcup_j Q j) (euclidean_block_split p).2).
  + have [i _ hi]:=hP; have [j _ hj]:=hQ.
    exfalso; apply:hNot; exists (i,j); first exact Logic.I; by split.
  + right; split; first exact hpW; by split.
- left; split; last exact hpZ; by split.
Qed.

(** Source for [rectifiable_cartesian_reference_remainder_null]: supporting
    null omitted set for the Cartesian product of the factor measures
    in Federer 3.2.23, p. 260. Source and target null
    complements give two zero-cost cylinders; no finiteness or
    measurability assumption on those complements is needed. *)
Theorem rectifiable_cartesian_reference_remainder_null (R:realType) m mu n v (lambda:R)
    (W:set (R_n R n)) (Z:set (R_n R v))
    (K:nat->set (R_n R m)) (C:nat->set (R_n R mu))
    (psi:nat->R_n R m->R_n R n) (gamma:nat->R_n R mu->R_n R v):
  is_rectifiable_compact_chart_cover lambda W K psi ->
  is_rectifiable_compact_chart_cover lambda Z C gamma ->
  product_measure
    (measure_restrict_is_measure (@hausdorff_measure_is_measure R
      (inner_metric_space (@euclidean_inner_productP R n)) m) W)
    (measure_restrict_is_measure (@hausdorff_measure_is_measure R
      (inner_metric_space (@euclidean_inner_productP R v)) mu) Z)
    (~` (\bigcup_(p in @setT (nat*nat)%type)
      ((psi p.1 @` K p.1) `*` (gamma p.2 @` C p.2))))=0.
Proof.
move=>hSource hTarget.
pose P:=fun i=>psi i @` K i.
pose Q:=fun j=>gamma j @` C j.
pose alpha:=measure_restrict (@hausdorff_measure R
  (inner_metric_space (@euclidean_inner_productP R n)) m) W.
pose beta:=measure_restrict (@hausdorff_measure R
  (inner_metric_space (@euclidean_inner_productP R v)) mu) Z.
have hA:measure_almost_everywhere alpha (\bigcup_i P i) by exact hSource.2.2.
have hB:measure_almost_everywhere beta (\bigcup_j Q j) by exact hTarget.2.2.
have hProduct:=product_measure_almost_everywhere_factors
  (measure_restrict_is_measure (@hausdorff_measure_is_measure R
    (inner_metric_space (@euclidean_inner_productP R n)) m) W)
  (measure_restrict_is_measure (@hausdorff_measure_is_measure R
    (inner_metric_space (@euclidean_inner_productP R v)) mu) Z) hA hB.
have hUnion:(\bigcup_(p in @setT (nat*nat)%type) ((P p.1) `*` (Q p.2)))=
    (\bigcup_i P i) `*` (\bigcup_j Q j).
  apply/seteqP; split.
  - move=>[x y] [[i j] _ [hi hj]]; split; [by exists i|by exists j].
  - move=>[x y] [[i _ hi] [j _ hj]]; exists (i,j); first exact Logic.I; by split.
rewrite hUnion; exact hProduct.
Qed.
