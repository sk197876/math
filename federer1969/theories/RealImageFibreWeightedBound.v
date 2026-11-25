(** Federer (1969), 2.10.27, pp. 190–191: supporting weighted-cover bound
    for images of fibres under a second nonexpanding map. The proof follows
    the source cover, closed first images and grouped weights of 2.10.25, p.
    189, but bounds the fibre-image cutoff directly by images of the source
    generators. This avoids assuming an isometry of slices from nonexpanding
    projections alone. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import RealHausdorffMeasure RealHausdorffNormalisation
  RealHausdorffMeasureLaws RealPowerCoverVariants MetricRealPowerCost RealPower RealPowerNaturalHausdorff
  MetricDiameterMaps RealHausdorffFibreCost RealHausdorffFibreCutoffs
  RealHausdorffProperWeighted RealHausdorffWeightedSigmaFinite LipschitzUP MetricDiameterUP MetricDiameter MetricDiameterClosure
  HausdorffLengthUP HausdorffMeasureUP HausdorffMeasure HausdorffDiameterCost HausdorffLipschitzCost
  HausdorffFibreCost HausdorffLengthMaps MetricScaleIndexedCover HausdorffProperWeighted CaratheodoryLimitUP CaratheodoryBorelRegular
  MetricScaleEnvelopeUP MetricScaleEnvelope MetricScaleEnvelopeLaws MetricScaleApproximation
  WeightedMetricEnvelopeUP WeightedMetricEnvelopeLaws WeightedMetricLimitUP WeightedMetricLimit
  WeightedGeneratorImageAssembly MeasureUP MeasureAlmostUP MeasureAlmostBasic
  NonnegativeSum NonnegativeSumSupport NonnegativeSumScale ExtendedScaledErrorBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [real_hausdorff_image_fibre_weighted_limit_bound]:
    supporting weighted-cover estimate for the first
    inequality in 2.10.27, p. 190, expanding
    the covering proof of 2.10.25, p. 189.
    Apply a nonexpanding second map g to the
    fibres of f. The cutoff masses are measured
    in g's target, and no isometry of slices
    or measurability of the fibre images is assumed. *)
Theorem real_hausdorff_image_fibre_weighted_limit_bound (R : realType) (X Y Z : metricType R)
    (f : X -> Y) (g : X -> Z) (L : R) (k m : R) (hk : (0<=k)%R) (hm : (0<=m)%R) (A : set X) (d : R) (nu : set Z -> \bar R) :
  is_metric_lipschitz_bound setT f L -> is_metric_lipschitz_bound setT g 1%R ->
  (0<L)%R -> (0<d)%R ->
  is_metric_scale_envelope (fun j : @nonempty_metric_sets R Z=>val j)
    (fun j=>metric_real_diameter_cost (real_hausdorff_normalisation hk) k (val j)) d%:E nu ->
  @real_hausdorff_measure R X (k+m)%R (addr_ge0 hk hm) A< +oo ->
  weighted_metric_limit (fun j : @nonempty_metric_sets R Y=>val j)
    (fun j=>metric_real_diameter_cost (real_hausdorff_normalisation hm) m (val j)) (@real_hausdorff_measure R Y m hm)
    (fun y=>nu (g @` (A `&` f @^-1` [set y])))<=
    (real_hausdorff_fibre_bound_constant hk hm L)%:E* @real_hausdorff_measure R X (k+m)%R (addr_ge0 hk hm) A.
Proof.
move=> hf hg hL hd hnu hfinite.
pose I := @nonempty_metric_sets R X.
pose K := @nonempty_metric_sets R Y.
pose S := fun j : I=>val j.
pose T := fun j : K=>val j.
pose c := fun j : K=>metric_real_diameter_cost (real_hausdorff_normalisation hm) m (val j).
pose psi := @real_hausdorff_measure R Y m hm.
pose C := real_hausdorff_fibre_bound_constant hk hm L.
have hC : (0<=C)%R := real_hausdorff_fibre_bound_constant_nonnegative hk hm L.
have hMeasure := @real_hausdorff_measure_is_measure R Y m hm.
have hkn (B : set X) : 0<=metric_real_diameter_cost (real_hausdorff_normalisation hk) k B.
  exact: metric_real_diameter_cost_ge0 (ltW (real_hausdorff_normalisation_positive hk)).
have hmn (B : set Y) : 0<=metric_real_diameter_cost (real_hausdorff_normalisation hm) m B.
  exact: metric_real_diameter_cost_ge0 (ltW (real_hausdorff_normalisation_positive hm)).
have hsum (B : set X) : 0<=metric_real_diameter_cost
    (real_hausdorff_normalisation (addr_ge0 hk hm)) (k+m)%R B.
  exact: metric_real_diameter_cost_ge0 (ltW (real_hausdorff_normalisation_positive (addr_ge0 hk hm))).
have hM0 := @measure_nonnegative R X (@real_hausdorff_measure R X (k+m)%R (addr_ge0 hk hm))
  (@real_hausdorff_measure_is_measure R X (k+m)%R (addr_ge0 hk hm)) A.
have hMreal : real_hausdorff_measure (addr_ge0 hk hm) A \is a fin_num by rewrite (ge0_fin_numE hM0).
pose M := fine (@real_hausdorff_measure R X (k+m)%R (addr_ge0 hk hm) A).
have hM : @real_hausdorff_measure R X (k+m)%R (addr_ge0 hk hm) A=M%:E by rewrite /M fineK.
rewrite hM -EFinM.
apply: (weighted_metric_limit_least (weighted_metric_limit_specification T c psi))=> delta lambda hdelta hlambda.
apply: (@extended_upper_bound_from_scaled_errors R _ (C*M)%R C hC)=> e he.
have [n hn] := reciprocal_metric_cutoffs_cofinal hdelta.
pose s := ((n.+1%:R : R)^-1)%R.
have hs : (0<s)%R by rewrite /s invr_gt0 ltr0n.
pose r := Order.min d (s/L)%R.
have hr : (0<r)%R by rewrite /r lt_min hd divr_gt0.
have hrd : (r<=d)%R by rewrite /r ge_min lexx.
have hrLs : (r<=s/L)%R by rewrite /r ge_min lexx orbT.
have hLr : (L*r<=s)%R.
  have hh := ler_wpM2l (ltW hL) hrLs.
  have hcancel : (L*(s/L)=s)%R by rewrite mulrC divfK ?gt_eqF.
  by rewrite hcancel in hh.
have hsmall : L%:E*r%:E<=delta.
  apply: le_trans _ hn; rewrite -EFinM lee_fin; exact hLr.
pose cost j := metric_real_diameter_cost (real_hausdorff_normalisation (addr_ge0 hk hm)) (k+m)%R (S j).
pose mu := metric_scale_envelope S cost r%:E.
have hmu := metric_scale_envelope_specification S cost r%:E.
have hsource := @caratheodory_limit_upper R X I S cost (@real_hausdorff_measure R X (k+m)%R (addr_ge0 hk hm))
  (@real_hausdorff_measure_specification R X (k+m)%R (addr_ge0 hk hm)) A r%:E mu hr hmu.
have hnear : mu A<(M+e)%R%:E.
  rewrite hM in hsource; apply: le_lt_trans hsource _; rewrite lte_fin ltrDl; exact he.
have [G [hG [hdiam [hcover hcost]]]] := metric_scale_envelope_approximation hmu hnear.
have hqnon (j : I) : closure (f @` S j) !=set0.
  have [x hx] := set_valP j; exists (f x); apply: subset_closure; by exists x.
pose q (j : I) : K := Sub (closure (f @` S j)) (mem_set (hqnon j)).
pose a (j : I) := fine (metric_real_diameter_cost (real_hausdorff_normalisation hk) k (S j)).
have hcostk j (hj : G j) : metric_real_diameter_cost (real_hausdorff_normalisation hk) k (S j) \is a fin_num.
  rewrite (ge0_fin_numE (hkn (S j))).
  apply: (@real_bounded_hausdorff_generator_cost_finite R X k hk (S j)).
  exact: le_lt_trans (hdiam j hj) (ltry r).
have haE j (hj : G j) : (a j)%:E=metric_real_diameter_cost (real_hausdorff_normalisation hk) k (S j) by rewrite /a (fineK (hcostk j hj)).
have ha j (hj : G j) : (0<=a j)%R.
  have hh := hkn (S j); by rewrite -(haE j hj) lee_fin in hh.
have htargetdiam j (hj : G j) : extended_metric_diameter (T (q j))<=delta.
  change (is_true (extended_metric_diameter (closure (f @` S j))<=delta)).
  rewrite extended_metric_diameter_closure.
  apply: le_trans (@extended_metric_diameter_lipschitz R X Y f L hf (S j)) _.
  apply: le_trans (lee_wpmul2l (hf.1 : 0<=L%:E) (hdiam j hj)) hsmall.
have hbudget : nonnegative_sum G (fun j=>(a j)%:E*c (q j))<=(C*(M+e))%R%:E.
  have hh : nonnegative_sum G (fun j=>(a j)%:E*c (q j))<=
      nonnegative_sum G (fun j=>C%:E*cost j).
    apply: nonnegative_sum_mono=> j hj; rewrite (haE j hj).
    exact: (@real_hausdorff_closed_image_fibre_cost_bound R X Y f L k m hk hm hf hL (S j)).
  rewrite nonnegative_sum_scale in hh=> //; last exact: (fun j _=>hsum (S j)).
  have hCE : 0<=C%:E by rewrite lee_fin.
  have hscaled := lee_wpmul2l hCE (ltW hcost).
  exact: le_trans hh hscaled.
have hbudgetfin : nonnegative_sum G (fun j=>(a j)%:E*c (q j))< +oo.
  exact: le_lt_trans hbudget (ltry (C*(M+e))%R).
have hpoint y : nu (g @` (A `&` f @^-1` [set y]))<=weighted_generator_sum (fun j=>T (q j)) G a y.
  pose F := [set j | G j /\ T (q j) y].
  pose J := @nonempty_metric_sets R Z.
  pose u (j : I) : J := nonempty_metric_image g j.
  have hF : countable F := sub_countable (subset_card_le (fun j (hj : F j)=>hj.1)) hG.
  have hFd j (hj : F j) : extended_metric_diameter (val (u j))<=d%:E.
    have hh := @extended_metric_diameter_lipschitz R X Z g 1%R hg (S j).
    rewrite mul1e in hh.
    apply: le_trans hh (le_trans (hdiam j hj.1) _); rewrite lee_fin; exact hrd.
  have hFc : (g @` (A `&` f @^-1` [set y])) `<=` \bigcup_(j in F) val (u j).
    move=> z [x [hxA hxy] <-]; have [j hj hxj] := hcover x hxA.
    exists j; last by exists x.
    split=> //; change (closure (f @` S j) y); apply: subset_closure.
    exists x=> //; exact hxy.
  have hh := @metric_scale_envelope_indexed_cover R Z J I (fun j=>val j)
    (fun j=>metric_real_diameter_cost (real_hausdorff_normalisation hk) k (val j)) d%:E nu hnu
    (g @` (A `&` f @^-1` [set y])) F u hF
    (fun j _=>@metric_real_diameter_cost_ge0 R Z (real_hausdorff_normalisation hk) k (val (u j)) (ltW (real_hausdorff_normalisation_positive hk))) hFd hFc.
  have hc : nonnegative_sum F (fun j=>metric_real_diameter_cost (real_hausdorff_normalisation hk) k (val (u j)))<=
      nonnegative_sum F (fun j=>metric_real_diameter_cost (real_hausdorff_normalisation hk) k (S j)).
    apply: nonnegative_sum_mono=> j hj.
    have hdg := @extended_metric_diameter_lipschitz R X Z g 1%R hg (S j).
    rewrite mul1e in hdg.
    apply: (@metric_real_power_cost_monotone R (real_hausdorff_normalisation hk) k
      _ _ (ltW (real_hausdorff_normalisation_positive hk)) hk _ hdg).
    exact: metric_diameter_nonnegative (extended_metric_diameter_specification _).
  apply: le_trans hh (le_trans hc _).
  have heq : nonnegative_sum F (fun j=>metric_real_diameter_cost (real_hausdorff_normalisation hk) k (S j))=
      weighted_generator_sum (fun j=>T (q j)) G a y.
    apply: nonnegative_sum_ext=> j hj; exact: esym (haE j hj.1).
  by rewrite heq.
have hdom : measure_almost_everywhere psi [set y | nu (g @` (A `&` f @^-1` [set y]))<=
    weighted_generator_sum (fun j=>T (q j)) G a y].
  apply: (@measure_almost_everywhere_mono R Y psi hMeasure setT _ _
    (measure_almost_everywhere_true hMeasure))=> y _; exact: hpoint.
have [H [u [hHu hHuCost]]] := @weighted_generator_image_assembly R Y I K T c psi G q a delta
  (fun y=>nu (g @` (A `&` f @^-1` [set y]))) hMeasure
  (fun j=>hmn (val j)) hG ha htargetdiam
  (fun j _=>@real_hausdorff_zero_cost_generator_null R Y m hm (val j)) hbudgetfin hdom.
have hh := le_trans (weighted_metric_envelope_lower hlambda hHu) (le_trans hHuCost hbudget).
by rewrite mulrDr in hh.
Qed.
