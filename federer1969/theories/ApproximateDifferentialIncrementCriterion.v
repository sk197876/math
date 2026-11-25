(** Federer (1969), 3.1.4, p. 216: a density-zero exceptional
    set for every relative remainder tolerance gives the approximate
    differential. The omitted zero increment is null in positive dimension. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology lra.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  InnerNorm RealNormUP RealMetricBackground EuclideanLebesgueDimensions
  EuclideanApproximateContext EuclideanApproximateTranslation EuclideanZeroDensityUnion
  EuclideanNoncenteredVitali EuclideanClosedBallVolume MetricClosedBalls
  CenteredBallRelations CenteredNullSetDensity PartialFunctionUP MeasureSetDensity
  MeasureApproximateLimitUP LocalZeroDensity ApproximateDifferentialUP
  ApproximateDifferentialRemainder ApproximateDifferentialAffine.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(** Source for [approximate_differential_increment_density_criterion]:
    the final inference in Federer 3.1.4, p. 216. Strict
    remainder-exception sets suffice, by halving the target tolerance.
    The positive source dimension is required for the punctured-domain
    convention of 3.1.2, as documented for that definition. *)
Theorem approximate_differential_increment_density_criterion (R : realType) n
    (Y : lmodType R) (NY : Y -> R) (hNY : is_real_norm NY)
    (f : R_n R n.+1 -> Y) (a : R_n R n.+1) (L : Hom (R_n R n.+1) Y) :
  (forall e : R, 0<e ->
    partial_function_graph (measure_set_density (@euclidean_lebesgue_measure R n.+1)
      (@centered_closed_ball_relation R
        [the metricType R of inner_metric_space (@euclidean_inner_productP R n.+1)])
      [set h | e*inner_norm (@euclidean_inner_productP R n.+1) h < NY (f (a+h)-f a-L h)])
      0 0%E) ->
  has_approximate_differential NY setT f a L.
Proof.
move=> hs; split=> // W hW.
pose X := inner_metric_space (@euclidean_inner_productP R n.+1).
pose mu := @euclidean_lebesgue_measure R n.+1.
pose V := @centered_closed_ball_relation R [the metricType R of X].
pose NX := inner_norm (@euclidean_inner_productP R n.+1).
have [e he heW] := (metricType_numDomainType.nbhs_mdistP (0 : real_line_metric R) W).1 hW.
have he2 : 0<e/2 by rewrite divr_gt0 // ltr0n.
pose B := [set h : X | e/2*NX h<NY (f (a+h)-f a-L h)].
have hB := hs (e/2) he2.
have hzero : partial_function_graph (measure_set_density mu V [set (0 : X)]) 0 0%E.
  apply: (@centered_null_set_density_zero R [the metricType R of X] mu [set (0 : X)] 0
    (euclidean_lebesgue_is_measure R n.+1)).
  - move=> x r hr; split; first exact: euclidean_closed_ball_positive.
    by rewrite /mu (euclidean_closed_ball_normalized_volume x (ltW hr)) fin_numE.
  - exact: positive_euclidean_singleton_null.
have hbad := euclidean_zero_density_union hzero hB.
pose C := ~` partial_function_preimage (approximate_remainder_quotient NY setT f a L) W.
have hshift : partial_function_graph (measure_set_density mu V
    ((fun h : X=>a+h) @^-1` C)) 0 0%E.
  apply: (@local_zero_density_mono R [the metricType R of X] mu V _ ([set (0 : X)] `|` B)
    setT 0 (euclidean_approximate_context R n.+1) openT Logic.I _ hbad)=> h _ hc.
  case: (eqVneq h 0)=> [h0|hn]; first by left.
  right; apply: contrapT=> hnb; apply: hc.
  have hpos : 0<NX h by rewrite /NX inner_norm_gt0.
  have herr : NY (f (a+h)-f a-L h)<=e/2*NX h by rewrite leNgt; exact/negP.
  pose q := NY (f (a+h)-f a-L h)/NX h.
  exists q; split.
  - apply: (@approximate_remainder_quotient_graph R n.+1 Y NY setT f a L (a+h) q).2.
    split=> //; split; first by rewrite -subr_eq0 addrC addKr.
    have hdiff : a+h-a=h by rewrite addrAC subrr add0r.
    by rewrite /q hdiff.
  - apply: heW.
    change (is_true (`|0-q|<e)).
    rewrite sub0r normrN ger0_norm; last first.
      exact: divr_ge0 (real_seminorm_nonnegative hNY.1 _) (ltW hpos).
    rewrite /q ltr_pdivrMr //.
    apply: le_lt_trans herr _; rewrite ltr_pM2r //; lra.
have hh := @euclidean_zero_density_translation_inverse R n.+1 a (0 : X) C hshift.
by rewrite addr0 in hh.
Qed.
