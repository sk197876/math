(** Federer (1969), 2.10.25, pp. 188–189: supporting weighted bound for a
    fixed source fibre cutoff. Cover A at a sufficiently small source
    cutoff, map generators to their closed images and group their degree-k
    costs as finite real coefficients. Infinite intermediate groups are
    removed only after proving their target sets null. The construction
    proves an admissible weighted cover and does not change the coefficient
    domain of 2.10.24. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import LipschitzUP MetricDiameterUP MetricDiameter MetricDiameterClosure
  HausdorffLengthUP HausdorffMeasureUP HausdorffMeasure HausdorffDiameterCost HausdorffLipschitzCost
  HausdorffFibreCost HausdorffProperWeighted CaratheodoryLimitUP CaratheodoryBorelRegular
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

(** Source for [hausdorff_fibre_weighted_limit_bound]: supporting
    fixed-cutoff weighted inequality in the proof of
    2.10.25, p. 189. A positive Lipschitz bound and
    finite source measure suffice here; zero bounds and
    infinite source mass are treated separately in the
    final theorem. The source fibre cutoff is any
    positive finite real, generalising the printed 1/i. *)
Theorem hausdorff_fibre_weighted_limit_bound (R : realType) (X Y : metricType R)
    (f : X -> Y) (L : R) (k m : nat) (A : set X) (d : R) (nu : set X -> \bar R) :
  is_metric_lipschitz_bound setT f L -> (0<L)%R -> (0<d)%R ->
  is_metric_scale_envelope (fun j : @nonempty_metric_sets R X=>val j)
    (fun j=>hausdorff_diameter_cost k (val j)) d%:E nu ->
  @hausdorff_measure R X (k+m) A< +oo ->
  weighted_metric_limit (fun j : @nonempty_metric_sets R Y=>val j)
    (fun j=>hausdorff_diameter_cost m (val j)) (@hausdorff_measure R Y m)
    (fun y=>nu (A `&` f @^-1` [set y]))<=
    (hausdorff_fibre_bound_constant k m L)%:E* @hausdorff_measure R X (k+m) A.
Proof.
move=> hf hL hd hnu hfinite.
pose I := @nonempty_metric_sets R X.
pose K := @nonempty_metric_sets R Y.
pose S := fun j : I=>val j.
pose T := fun j : K=>val j.
pose c := fun j : K=>hausdorff_diameter_cost m (val j).
pose psi := @hausdorff_measure R Y m.
pose C := hausdorff_fibre_bound_constant k m L.
have hC : (0<=C)%R := hausdorff_fibre_bound_constant_nonnegative k m (ltW hL).
have hm := @hausdorff_measure_is_measure R Y m.
have hM0 := @measure_nonnegative R X (@hausdorff_measure R X (k+m))
  (@hausdorff_measure_is_measure R X (k+m)) A.
have hMreal : hausdorff_measure (k+m) A \is a fin_num by rewrite (ge0_fin_numE hM0).
pose M := fine (@hausdorff_measure R X (k+m) A).
have hM : @hausdorff_measure R X (k+m) A=M%:E by rewrite /M fineK.
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
pose cost j := hausdorff_diameter_cost (k+m) (S j).
pose mu := metric_scale_envelope S cost r%:E.
have hmu := metric_scale_envelope_specification S cost r%:E.
have hsource := @caratheodory_limit_upper R X I S cost (@hausdorff_measure R X (k+m))
  (@hausdorff_measure_specification R X (k+m)) A r%:E mu hr hmu.
have hnear : mu A<(M+e)%R%:E.
  rewrite hM in hsource; apply: le_lt_trans hsource _; rewrite lte_fin ltrDl; exact he.
have [G [hG [hdiam [hcover hcost]]]] := metric_scale_envelope_approximation hmu hnear.
have hqnon (j : I) : closure (f @` S j) !=set0.
  have [x hx] := set_valP j; exists (f x); apply: subset_closure; by exists x.
pose q (j : I) : K := Sub (closure (f @` S j)) (mem_set (hqnon j)).
pose a (j : I) := fine (hausdorff_diameter_cost k (S j)).
have hcostk j (hj : G j) : hausdorff_diameter_cost k (S j) \is a fin_num.
  rewrite (ge0_fin_numE (hausdorff_diameter_cost_nonnegative k (S j))).
  apply: bounded_hausdorff_generator_cost_finite.
  exact: le_lt_trans (hdiam j hj) (ltry r).
have haE j (hj : G j) : (a j)%:E=hausdorff_diameter_cost k (S j) by rewrite /a (fineK (hcostk j hj)).
have ha j (hj : G j) : (0<=a j)%R.
  have hh := hausdorff_diameter_cost_nonnegative k (S j); by rewrite -(haE j hj) lee_fin in hh.
have htargetdiam j (hj : G j) : extended_metric_diameter (T (q j))<=delta.
  change (is_true (extended_metric_diameter (closure (f @` S j))<=delta)).
  rewrite extended_metric_diameter_closure.
  apply: le_trans (@extended_metric_diameter_lipschitz R X Y f L hf (S j)) _.
  apply: le_trans (lee_wpmul2l (hf.1 : 0<=L%:E) (hdiam j hj)) hsmall.
have hbudget : nonnegative_sum G (fun j=>(a j)%:E*c (q j))<=(C*(M+e))%R%:E.
  have hh : nonnegative_sum G (fun j=>(a j)%:E*c (q j))<=
      nonnegative_sum G (fun j=>C%:E*cost j).
    apply: nonnegative_sum_mono=> j hj; rewrite (haE j hj).
    exact: (@hausdorff_closed_image_fibre_cost_bound R X Y f L k m hf (S j)).
  rewrite nonnegative_sum_scale in hh=> //; last exact: (fun j _=>hausdorff_diameter_cost_nonnegative (k+m) (S j)).
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
  have hh := @metric_scale_envelope_lower R X I S (fun j=>hausdorff_diameter_cost k (S j))
    d%:E nu hnu (A `&` f @^-1` [set y]) F hF hFd hFc.
  have heq : nonnegative_sum F (fun j=>hausdorff_diameter_cost k (S j))=
      weighted_generator_sum (fun j=>T (q j)) G a y.
    apply: nonnegative_sum_ext=> j hj; exact: esym (haE j hj.1).
  by rewrite heq in hh.
have hdom : measure_almost_everywhere psi [set y | nu (A `&` f @^-1` [set y])<=
    weighted_generator_sum (fun j=>T (q j)) G a y].
  apply: (@measure_almost_everywhere_mono R Y psi hm setT _ _
    (measure_almost_everywhere_true hm))=> y _; exact: hpoint.
have [H [u [hHu hHuCost]]] := @weighted_generator_image_assembly R Y I K T c psi G q a delta
  (fun y=>nu (A `&` f @^-1` [set y])) hm
  (fun j=>hausdorff_diameter_cost_nonnegative m (val j)) hG ha htargetdiam
  (fun j _=>@hausdorff_zero_cost_generator_null R Y m (val j)) hbudgetfin hdom.
have hh := le_trans (weighted_metric_envelope_lower hlambda hHu) (le_trans hHuCost hbudget).
by rewrite mulrDr in hh.
Qed.
