(** Federer (1969), 3.4.4, pp. 317–318: actual
    regressions of the original Cantor construction and least-degree conclusion. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology lra ring.
From Federer Require Import Hom GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  InnerNorm InnerMetric HilbertFormCompactness RealNormUP NormMetric NormDifferentialUP
  NormRegularity ContinuousMultilinearUP ContinuousMultilinearSealed RealMetricBackground
  PowerCantorPairUP PowerCantorPair EqualCostFirstEndpoint BinaryCantorFlatExtension BinaryCantorOrder
  FirstZeroFormDifferential CantorBallProbability BallGrowthProbabilityUP BallGrowthHausdorffLower
  RealPower RealHausdorffNormalisation RealHausdorffMeasure CriticalValueSharpness
  CriticalValueLeastDegree CriticalValueProblem LinearRankUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section SharpnessExamples.
Variable R:realType.
Local Notation E1:=(inner_metric_space (@euclidean_inner_productP R 1)).
Local Notation N1:=(inner_norm (@euclidean_inner_productP R 1)).
Local Notation hN1:=(inner_norm_real_norm (@euclidean_inner_productP R 1)).
Local Notation NS:=(fun t:R^o=>`|t|).
Local Notation hNS:=(@scalar_absolute_value_norm R).
Local Notation Z:=(fun i=>@ContinuousMultilinear.space R i (R_n R 1) R^o N1 NS hN1 hNS).
Local Notation ev:=(fun i=>@ContinuousMultilinear.evaluation R i (R_n R 1) R^o N1 NS hN1 hNS).
Local Notation ZN:=(fun i=>@ContinuousMultilinear.norm R i (R_n R 1) R^o N1 NS hN1 hNS).

(** Source for [critical_sharp_quarter_nonnegative]: the actual
    degree beta=1/4 in the concrete original example of
    3.4.4, p. 318. No degree-validity premise
    is supplied to the regression. *)
Lemma critical_sharp_quarter_nonnegative:(0<=(1/4:R)).
Proof. by rewrite divr_ge0 // ler0n. Qed.

(** Source for [critical_sharp_flat_cantor_quarters]: an actual
    class-two instance of 3.4.4, p. 318,
    with original binary Cantor degrees alpha=3/4 and beta=1/4.
    The original source contains zero; the actual differential
    there is zero, while the exact target image has positive
    Gamma-normalized quarter-dimensional measure. *)
Example critical_sharp_flat_cantor_quarters:
  exists A B:set (real_line_metric R),exists u v:R->R,exists g:E1->R^o,
    is_power_cantor_pair 1 (3/4) (fun _:nat=>2%N) A u /\
    is_power_cantor_pair 1 (1/4) (fun _:nat=>2%N) B v /\
    norm_class hN1 hNS (fun _=>True) g 2 /\
    (fun t:real_line_metric R=>g (EuclideanOneCoordinate.euclidean_one_embed t)) @` A=B /\
    has_norm_differential N1 NS (fun _=>True) g (EuclideanOneCoordinate.euclidean_one_embed 0) 0 /\
    (0<@real_hausdorff_measure R [the metricType R of real_line_metric R]
      (1/4) critical_sharp_quarter_nonnegative B)%E.
Proof.
have hAlpha:(0<(3/4:R)) by lra.
have hAlphaUpper:(3/4:R)<1 by lra.
have hBeta:(0<(1/4:R)) by lra.
have hBetaUpper:(1/4:R)<1 by lra.
have hRatio:((3/4)/(1/4):R)=3 by field.
have hOrder:(2%:R:R)<(3/4)/(1/4) by rewrite hRatio;lra.
have hTwo (j:nat):(2<=2)%N by [].
have [A [u hA]]:=@power_cantor_pair_exists R 1 (3/4) (fun _:nat=>2%N)
  ltr01 hAlpha hAlphaUpper hTwo.
have [B [v hB]]:=@power_cantor_pair_exists R 1 (1/4) (fun _:nat=>2%N)
  ltr01 hBeta hBetaUpper hTwo.
have [g [hG [hImage hFlat]]]:=@binary_cantor_flat_extension_exists R (3/4) (1/4) 2 A B u v
  hAlpha hAlphaUpper hBeta hBetaUpper hOrder hA hB.
have hOrigin:A 0:=@power_cantor_original_zero_endpoint R 1 (3/4) (fun _:nat=>2%N) A u hA.
have hZ i:is_continuous_multilinear_space N1 NS (@ev i) (@ZN i).
  exact:ContinuousMultilinear.laws.
have hRange:(1<=1<=2)%N by [].
have hZero:=@first_zero_form_is_zero_differential R (R_n R 1) R^o N1 NS hN1 hNS
  Z ev ZN hZ (fun _=>True) g (EuclideanOneCoordinate.euclidean_one_embed 0) (@hFlat 0 hOrigin 1 hRange).
have [mu hMu]:=@original_cantor_ball_probability_exists R (1/4) (fun _:nat=>2%N) B v hBeta hBetaUpper hB.
pose b:=real_hausdorff_normalisation critical_sharp_quarter_nonnegative.
have hb:0<b:=real_hausdorff_normalisation_positive critical_sharp_quarter_nonnegative.
have hK:=ball_growth_coefficient_positive hMu.
have hLower:=@ball_growth_probability_power_measure_lower R [the metricType R of real_line_metric R]
  B (real_power 2 (1/4)) (1/4) b mu hMu hb.
have hPositive:(0<@real_hausdorff_measure R [the metricType R of real_line_metric R]
    (1/4) critical_sharp_quarter_nonnegative B)%E.
  apply:lt_le_trans _ hLower;rewrite lte_fin;exact:divr_gt0 hb hK.
exists A,B,u,v,g;split;first exact:hA.
split;first exact:hB.
split;first exact:hG.
split;first exact:hImage.
by split.
Qed.

(** Source for [critical_sharp_rank_one_plane]: a nonvacuous
    rank-one, class-three whole-plane example of 3.4.4,
    pp. 317–318, whose actual image has positive
    measure at a real degree strictly above 5/4. *)
Example critical_sharp_rank_one_plane:
  exists s:R,exists hs:0<=s,exists B:set (R_n R 2),exists f:R_n R 2->R_n R 2,
    5/4<s /\
    norm_class (inner_norm_real_norm (@euclidean_inner_productP R 2))
      (inner_norm_real_norm (@euclidean_inner_productP R 2)) (fun _=>True) f 3 /\
    (forall x,B x ->exists D:Hom (R_n R 2) (R_n R 2),
      has_norm_differential (inner_norm (@euclidean_inner_productP R 2))
        (inner_norm (@euclidean_inner_productP R 2)) (fun _=>True) f x D /\has_linear_rank D 1) /\
    (0<@real_hausdorff_measure R
      (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R 2)))
      s hs (f @` B))%E.
Proof.
have hGamma:0<(5/4:R) by lra.
have hUpper:(5/4:R)<1%:R+(2-1)%:R/3%:R.
  change ((5/4:R)<1+1/3);lra.
exact:(@federer_3_4_4 R 2 1 3 (5/4) (erefl true) (erefl true) hGamma hUpper).
Qed.

(** Source for [critical_sharp_zero_degree_excluded]: the
    minimality proof of 3.4.1 and 3.4.4, pp. 310,
    317–318, excludes the proposed universal degree zero
    for class-two maps of the line with zero differential. *)
Example critical_sharp_zero_degree_excluded:
  ~@critical_value_nullity_degree R 1 0 2 0 (lexx 0).
Proof.
move=>hUniversal.
have hp:0<=(0%:R+(1-0)%:R/2%:R:R) by rewrite subn0 add0r divr_ge0 // ler0n.
have hLeast:=@critical_value_least_degree R 1 0 2 hp (erefl true) (erefl true).
have hBound:=@critical_value_degree_least R 1 0 2
  (0%:R+(1-0)%:R/2%:R) hp hLeast 0 (lexx 0) hUniversal.
move:hBound;rewrite subn0 add0r.
by lra.
Qed.
End SharpnessExamples.
