(** Federer (1969), 3.2.31, pp. 268–269: supporting
    measurable class-one pieces before small linear rescaling.
    Use the actual approximation theorem, as in 3.2.29, p. 268. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric HilbertFormCompactness
  NormRegularity LipschitzUP LipschitzBasic EuclideanLipschitzClassZero EuclideanClassZeroContinuity
  ContinuousEqualizerClosed ClassOneAgreementCoverUP LipschitzClassOneApproximation
  EuclideanLebesgueDimensions MeasureUP MeasureBasic ExtendedRealReciprocalBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [lipschitz_class_one_agreement_cover]: supporting
    local rescaling reduction in Federer 3.2.31, pp. 268–269.
    The actual 3.1.16 approximants at reciprocal tolerances give
    closed agreement sets with conull union. Existence is proved
    from the independent laws, and no family is selected globally.
    Positive source dimension is explicit; the source-zero branch
    of 3.2.31 has only target degree zero and is separate. *)
Theorem lipschitz_class_one_agreement_cover (R:realType) m n
    (F:inner_metric_space (@euclidean_inner_productP R m.+1)->
      inner_metric_space (@euclidean_inner_productP R n)) L:
  is_metric_lipschitz_bound setT F L ->
  exists G C,@is_class_one_agreement_cover R m n F G C.
Proof.
move=>hLip.
pose r j:=(((j.+1)%:R:R)^-1)%R.
have hr j:0<r j by rewrite /r invr_gt0 ltr0n.
have hex j:exists g:R_n R m.+1->R_n R n,
    norm_class (inner_norm_real_norm (@euclidean_inner_productP R m.+1))
      (inner_norm_real_norm (@euclidean_inner_productP R n)) setT g 1 /\
    (@euclidean_lebesgue_measure R m.+1 (~` [set x|F x=g x])<(r j)%:E)%E.
  exact (lipschitz_class_one_small_disagreement hLip (hr j)).
have [G hG]:=choice hex.
pose C j:=[set x|F x=G j x].
exists G,C; constructor.
- move=>j; exact:(hG j).1.
- move=>j; apply:continuous_equalizer_closed; first exact:metric_hausdorff.
  + exact (euclidean_class_zero_continuous (euclidean_lipschitz_norm_class_zero (metric_lipschitz_of_bound hLip))).
  + exact (euclidean_class_zero_continuous (norm_class_continuous (hG j).1)).
- by move=>j x hx.
- pose mu:=@euclidean_lebesgue_measure R m.+1.
  pose hm:=euclidean_lebesgue_is_measure R m.+1.
  apply/eqP; rewrite eq_le (measure_nonnegative hm) andbT.
  apply:(@extended_real_reciprocal_upper_bound R _ 0%R)=>j.
  have hSub:(~` \bigcup_j C j) `<=` ~` C j.
    move=>x hn hCx; apply:hn; by exists j.
  rewrite add0r; exact (ltW (le_lt_trans (measure_mono hm hSub) (hG j).2)).
Qed.
