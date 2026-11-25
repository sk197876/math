(** Federer (1969), 2.10.25, pp. 188–189: supporting weighted bound for a
    fixed source fibre cutoff. Cover A at a sufficiently small source
    cutoff, map generators to their closed images and group their degree-k
    costs as finite real coefficients. Infinite intermediate groups are
    removed only after proving their target sets null. The construction
    proves an admissible weighted cover and does not change the coefficient
    domain of 2.10.24. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import RealHausdorffMeasure RealHausdorffNormalisation RealPowerCoverVariants MetricRealPowerCost LipschitzUP MetricDiameterUP MetricDiameter MetricDiameterClosure
  HausdorffLengthUP HausdorffMeasureUP HausdorffMeasure HausdorffDiameterCost HausdorffLipschitzCost
  RealHausdorffFibreCost RealHausdorffProperWeighted CaratheodoryLimitUP CaratheodoryBorelRegular
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

(** Source for [real_hausdorff_fibre_weighted_limit_bound]: supporting
    fixed-cutoff weighted inequality in the proof of
    2.10.25, p. 189. A positive Lipschitz bound and
    finite source measure suffice here; zero bounds and
    infinite source mass are treated separately in the
    final theorem. The source fibre cutoff is any
    positive finite real, generalising the printed 1/i. *)
Theorem real_hausdorff_fibre_weighted_limit_bound (R : realType) (X Y : metricType R)
    (f : X -> Y) (L : R) (k m : R) (hk : (0<=k)%R) (hm : (0<=m)%R) (A : set X) (d : R) (nu : set X -> \bar R) :
  is_metric_lipschitz_bound setT f L -> (0<L)%R -> (0<d)%R ->
  is_metric_scale_envelope (fun j : @nonempty_metric_sets R X=>val j)
    (fun j=>metric_real_diameter_cost (real_hausdorff_normalisation hk) k (val j)) d%:E nu ->
  @real_hausdorff_measure R X (k+m)%R (addr_ge0 hk hm) A< +oo ->
  weighted_metric_limit (fun j : @nonempty_metric_sets R Y=>val j)
    (fun j=>metric_real_diameter_cost (real_hausdorff_normalisation hm) m (val j)) (@real_hausdorff_measure R Y m hm)
    (fun y=>nu (A `&` f @^-1` [set y]))<=
    (real_hausdorff_fibre_bound_constant hk hm L)%:E* @real_hausdorff_measure R X (k+m)%R (addr_ge0 hk hm) A.
Proof.
move=> hf hL hd hnu hfinite.
have hkn (T0 : set X) : 0<=metric_real_diameter_cost (real_hausdorff_normalisation hk) k T0.
  exact: metric_real_diameter_cost_ge0 (ltW (real_hausdorff_normalisation_positive hk)).
have hmn (T0 : set Y) : 0<=metric_real_diameter_cost (real_hausdorff_normalisation hm) m T0.
  exact: metric_real_diameter_cost_ge0 (ltW (real_hausdorff_normalisation_positive hm)).
have hkmn (T0 : set X) :
    0<=metric_real_diameter_cost (real_hausdorff_normalisation (addr_ge0 hk hm)) (k+m)%R T0.
  exact: metric_real_diameter_cost_ge0 (ltW (real_hausdorff_normalisation_positive (addr_ge0 hk hm))).
pose I := @nonempty_metric_sets R X.
pose K := @nonempty_metric_sets R Y.
pose S := fun j : I=>val j.
pose T := fun j : K=>val j.
pose c := fun j : K=>metric_real_diameter_cost (real_hausdorff_normalisation hm) m (val j).
pose psi := @real_hausdorff_measure R Y m hm.
pose C := real_hausdorff_fibre_bound_constant hk hm L.
have hC : (0<=C)%R := real_hausdorff_fibre_bound_constant_nonnegative hk hm L.
have hYmu := @real_hausdorff_measure_is_measure R Y m hm.
have hM0 := @measure_nonnegative R X (@real_hausdorff_measure R X (k+m)%R (addr_ge0 hk hm))
  (@real_hausdorff_measure_is_measure R X (k+m)%R (addr_ge0 hk hm)) A.
have hMreal : (@real_hausdorff_measure R X (k+m)%R (addr_ge0 hk hm)) A \is a fin_num by rewrite (ge0_fin_numE hM0).
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
  rewrite nonnegative_sum_scale in hh=> //; last exact: (fun j _=>hkmn (S j)).
  have hCE : 0<=C%:E by rewrite lee_fin.
  have hscaled := lee_wpmul2l hCE (ltW hcost).
  exact: le_trans hh hscaled.
have hbudgetfin : nonnegative_sum G (fun j=>(a j)%:E*c (q j))< +oo.
  exact: le_lt_trans hbudget (ltry (C*(M+e))%R).
have hpoint y : nu (A `&` f @^-1` [set y])<=weighted_generator_sum (fun j=>T (q j)) G a y.
  pose F := [set j | G j /\ T (q j) y].
  have hF : countable F := sub_countable (subset_card_le (fun j (hj : F j)=>hj.1)) hG.
  have hFd j (hj : F j) : extended_metric_diameter (S j)<=d%:E.
    apply: le_trans (hdiam j hj.1) _; rewrite lee_fin; exact hrd.
  have hFc : (A `&` f @^-1` [set y]) `<=` \bigcup_(j in F) S j.
    move=> x [hxA hxy]; have [j hj hxj] := hcover x hxA; exists j=> //; split=> //.
    change (closure (f @` S j) y); apply: subset_closure; exists x=> //; exact hxy.
  have hh := @metric_scale_envelope_lower R X I S (fun j=>metric_real_diameter_cost (real_hausdorff_normalisation hk) k (S j))
    d%:E nu hnu (A `&` f @^-1` [set y]) F hF hFd hFc.
  have heq : nonnegative_sum F (fun j=>metric_real_diameter_cost (real_hausdorff_normalisation hk) k (S j))=
      weighted_generator_sum (fun j=>T (q j)) G a y.
    apply: nonnegative_sum_ext=> j hj; exact: esym (haE j hj.1).
  by rewrite heq in hh.
have hdom : measure_almost_everywhere psi [set y | nu (A `&` f @^-1` [set y])<=
    weighted_generator_sum (fun j=>T (q j)) G a y].
  apply: (@measure_almost_everywhere_mono R Y psi hYmu setT _ _
    (measure_almost_everywhere_true hYmu))=> y _; exact: hpoint.
have [H [u [hHu hHuCost]]] := @weighted_generator_image_assembly R Y I K T c psi G q a delta
  (fun y=>nu (A `&` f @^-1` [set y])) hYmu
  (fun j=>hmn (val j)) hG ha htargetdiam
  (fun j _=>@real_hausdorff_zero_cost_generator_null R Y m hm (val j)) hbudgetfin hdom.
have hh := le_trans (weighted_metric_envelope_lower hlambda hHu) (le_trans hHuCost hbudget).
by rewrite mulrDr in hh.
Qed.
