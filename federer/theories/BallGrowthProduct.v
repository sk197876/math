(** Federer (1969), 3.4.4, p. 318: real-degree
    product positivity via actual products of competing finite measures. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology lra ring.
From Federer Require Import MetricCartesianProductUP MetricCartesianRectangleBounds MetricClosedBalls
  CountableOpenBaseUP StructureProductClosedMeasurable MeasureUP MeasurePushforward MeasureRestriction
  MeasureBasic ProductMeasure BallGrowthProbabilityUP RealPower RealPowerSuccessor.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [ball_growth_probability_product]: the product
    lower-bound step in 3.4.4, p. 318, expanding
    the cited 2.10.27 argument for the actual real degrees.
    A product ball lies in the product of its factor balls.
    Actual product rectangle values, closed-set measurability, and
    power addition prove all probability and growth laws. *)
Theorem ball_growth_probability_product (R:realType) (P X Y:metricType R)
    (pair:X->Y->P) (first:P->X) (second:P->Y)
    (hp:is_metric_cartesian_product pair first second)
    (A:set X) (B:set Y) (K L p q:R)
    (alpha:set X->\bar R) (beta:set Y->\bar R)
    (U:nat->set X) (V:nat->set Y):
  is_countable_open_base U ->is_countable_open_base V ->
  continuous (fun z:X*Y=>pair z.1 z.2) ->continuous first ->continuous second ->
  (0<q)%R ->is_ball_growth_probability A K p alpha ->
  is_ball_growth_probability B L q beta ->
  exists mu:set P->\bar R,
    is_ball_growth_probability [set z | A (first z) /\ B (second z)] (K*L)%R (p+q)%R mu.
Proof.
move=>hU hV hPair hFirst hSecond hQ hAlpha hBeta.
pose hA:=ball_growth_measure hAlpha.
pose hB:=ball_growth_measure hBeta.
pose mu:=paired_product_measure pair hA hB.
have hMu:is_measure mu:=paired_product_is_measure pair hA hB.
have hClosed C:closed C ->measure_measurable mu C.
  move=>hC.
  have hPre:closed ((fun z:X*Y=>pair z.1 z.2) @^-1` C).
    apply:preimage_closed=>// z _;exact:hPair z.
  have hMeas:=@structure_product_closed_measurable R (Topological.clone X _)
    (Topological.clone Y _) alpha beta hA hB U V hU hV
    (fun (C:set X) (hC:closed C)=>@ball_growth_closed_measurable R X A K p alpha hAlpha C hC)
    (fun (C:set Y) (hC:closed C)=>@ball_growth_closed_measurable R Y B L q beta hBeta C hC) _ hPre.
  have hPush:=(@measure_pushforward_restrictions_iff R (Choice.clone (X*Y)%type _)
    (Choice.clone P _) (fun z:X*Y=>pair z.1 z.2)
    (product_measure hA hB) C).1 hMeas setT.
  have hWhole:measure_restrict (product_measure hA hB) setT=product_measure hA hB.
    apply:funext=>S;by rewrite /measure_restrict setTI.
  by rewrite hWhole in hPush.
exists mu;constructor.
- exact:hMu.
- by rewrite /mu paired_product_whole_value (ball_growth_whole hAlpha) (ball_growth_whole hBeta) mul1e.
- exact:hClosed.
- apply:closedI.
  + apply:preimage_closed;last exact:ball_growth_original_source_closed hAlpha.
    move=>z _;exact:hFirst z.
  + apply:preimage_closed;last exact:ball_growth_original_source_closed hBeta.
    move=>z _;exact:hSecond z.
- rewrite /mu (@paired_product_coordinate_rectangle_value R P X Y pair first second hp
    alpha beta hA hB A B
    (@ball_growth_closed_measurable R X A K p alpha hAlpha A (ball_growth_original_source_closed hAlpha))
    (@ball_growth_closed_measurable R Y B L q beta hBeta B (ball_growth_original_source_closed hBeta)))
    (ball_growth_original_source_mass hAlpha) (ball_growth_original_source_mass hBeta).
  by rewrite mul1e.
- exact:mulr_gt0 (ball_growth_coefficient_positive hAlpha) (ball_growth_coefficient_positive hBeta).
- exact:addr_ge0 (ball_growth_degree_nonnegative hAlpha) (ltW hQ).
- move=>z r hr.
  have hContain w (hw:metric_closed_ball z r w):
      metric_closed_ball (first z) r (first w) /\metric_closed_ball (second z) r (second w).
    split.
    + have h:=(metric_product_first_nonexpanding hp).2 z w Logic.I Logic.I.
      rewrite mul1r in h;exact:le_trans h hw.
    + have h:=(metric_product_second_nonexpanding hp).2 z w Logic.I Logic.I.
      rewrite mul1r in h;exact:le_trans h hw.
  have hRectangle:=@paired_product_rectangle_bound R P X Y pair first second hp alpha beta hA hB
    (metric_closed_ball z r) (metric_closed_ball (first z) r) (metric_closed_ball (second z) r)
    (@ball_growth_closed_measurable R X A K p alpha hAlpha _ (@metric_closed_ball_closed R X (first z) r))
    (@ball_growth_closed_measurable R Y B L q beta hBeta _ (@metric_closed_ball_closed R Y (second z) r)) hContain.
  have hLeft:=@ball_growth_bound R X A K p alpha hAlpha (first z) r hr.
  have hRight:=@ball_growth_bound R Y B L q beta hBeta (second z) r hr.
  have hRightNonnegative:=measure_nonnegative hB (metric_closed_ball (second z) r).
  have hLeftNonnegative:(0<=(K*real_power r p)%R%:E)%E.
    rewrite lee_fin;exact:mulr_ge0 (ltW (ball_growth_coefficient_positive hAlpha)) (real_power_nonnegative r p).
  have hProduct:=le_trans (lee_wpmul2r hRightNonnegative hLeft) (lee_wpmul2l hLeftNonnegative hRight).
  apply:le_trans hRectangle (le_trans hProduct _).
  rewrite -EFinM.
  have hPower:(real_power r p*real_power r q=real_power r (p+q))%R.
    case:(eqVneq r 0%R)=>hR.
    + subst r.
      have hSum:(0<p+q)%R by have hP:=ball_growth_degree_nonnegative hAlpha;lra.
      have hQNe:q!=0%R by rewrite gt_eqF.
      have hSumNe:(p+q)%R!=0%R by rewrite gt_eqF.
      by rewrite (@real_power_zero_base R q hQNe) (@real_power_zero_base R (p+q)%R hSumNe) mulr0.
    + have hPositive:(0<r)%R by rewrite lt_neqAle eq_sym hR hr.
      by rewrite real_power_add_exponents_positive.
  have hReorder:((K*real_power r p)*(L*real_power r q)=K*L*(real_power r p*real_power r q))%R by ring.
  by rewrite hReorder hPower.
Qed.
