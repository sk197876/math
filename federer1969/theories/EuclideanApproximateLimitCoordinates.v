(** Federer (1969), 3.1.4, p. 214: reduction to a scalar target.
    A Euclidean approximate limit is equivalent to its coordinate
    limits together with density zero of its missing domain. The latter
    condition remains necessary when the target has dimension zero. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology num_normedtype lra.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  InnerNormedTopology EuclideanCoordinateTopology EuclideanLebesgueHaar
  EuclideanLebesgueDimensions EuclideanApproximateContext EuclideanZeroDensityUnion
  EuclideanFiniteZeroDensity CenteredBallRelations RealMetricBackground
  PartialFunctionUP PartialFunctionPreimages PartialFunctionPostcomposition
  MeasureSetDensity MeasureApproximateLimitUP ApproximateLimitComposition LocalZeroDensity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import numFieldTopology.Exports Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(** Source for [euclidean_approximate_limit_coordinate_criterion]:
    supporting finite-coordinate reduction in the opening sentence
    of proof of Federer 3.1.4, p. 214. The explicit missing-domain
    condition includes the empty coordinate family; for a nonempty
    family it already follows from any one coordinate limit. *)
Theorem euclidean_approximate_limit_coordinate_criterion (R : realType) m n
    (f : partial_function (inner_metric_space (@euclidean_inner_productP R m))
      (inner_metric_space (@euclidean_inner_productP R n))) a y :
  is_measure_approximate_limit (@euclidean_lebesgue_measure R m)
    (@centered_closed_ball_relation R
      [the metricType R of inner_metric_space (@euclidean_inner_productP R m)]) f a y <->
  partial_function_graph (measure_set_density (@euclidean_lebesgue_measure R m)
    (@centered_closed_ball_relation R
      [the metricType R of inner_metric_space (@euclidean_inner_productP R m)])
    (~` partial_function_domain f)) a 0%E /\
  forall j : 'I_n, @is_measure_approximate_limit R
    [the metricType R of inner_metric_space (@euclidean_inner_productP R m)]
    [the topologicalType of real_line_metric R] (@euclidean_lebesgue_measure R m)
    (@centered_closed_ball_relation R
      [the metricType R of inner_metric_space (@euclidean_inner_productP R m)])
    (partial_function_postcompose f (fun v=>(v j : real_line_metric R))) a (y j).
Proof.
pose X := inner_metric_space (@euclidean_inner_productP R m).
pose Y := inner_metric_space (@euclidean_inner_productP R n).
pose mu := @euclidean_lebesgue_measure R m.
pose V := @centered_closed_ball_relation R [the metricType R of X].
pose F j := partial_function_postcompose f (fun v=>(v j : real_line_metric R)).
split.
- move=> hf; split.
  + have ht : nbhs y setT.
      exact: (@filterT _ (nbhs y) (@nbhs_filter _ y)).
    have hh := @hf setT ht.
    have he : partial_function_preimage f setT=partial_function_domain f.
      apply/seteqP; split=> x; [by move=> [v [hv _]]; exists v|by move=> [v hv]; exists v].
    rewrite he in hh; exact hh.
  + move=> j; exact: approximate_limit_continuous_postcompose
      (@euclidean_coordinate_continuous R n j y) hf.
- move=> [hdom hcoords] W hW.
  have [e he heW] := (metricType_numDomainType.nbhs_mdistP y W).1 hW.
  pose d := (e / (n.+1)%:R)%R.
  have hden : ((0 : R)<(n.+1)%:R)%R by rewrite ltr0n.
  have hd : (0<d)%R by rewrite /d divr_gt0.
  pose U j := [set z : real_line_metric R | `|y j-z|<d].
  have hU j : nbhs (y j : real_line_metric R) (U j).
    apply: (metricType_numDomainType.nbhs_mdistP (y j : real_line_metric R) (U j)).2.
    exists d; first exact hd.
    by move=> z hz; exact hz.
  pose N j := ~` partial_function_preimage (F j) (U j).
  have hN j : partial_function_graph (measure_set_density mu V (N j)) a 0%E.
    exact: (@hcoords j (U j) (hU j)).
  have hbad := euclidean_zero_density_union hdom (euclidean_finite_union_density_zero hN).
  apply: (@local_zero_density_mono R [the metricType R of X] mu V
    (~` partial_function_preimage f W) ((~` partial_function_domain f) `|` \bigcup_j N j)
    setT a (euclidean_approximate_context R m) openT Logic.I _ hbad)=> x _ hx.
  case: (pselect (partial_function_domain f x))=> [[v hv]|hn]; last by left.
  case: (pselect (exists j, N j x))=> [[j hj]|hall]; first by right; exists j.
  exfalso; apply: hx; exists v; split=> //; apply: heW.
  have hcoord j : `|y j-v j|<d.
    have hpre : partial_function_preimage (F j) (U j) x.
      apply: contrapT=> hn; apply: hall; by exists j.
    move: hpre=> [u [[w [hw hwu]] hu]].
    have hwv := partial_function_single_valued hw hv.
    by move: hu; rewrite /U /= -hwu hwv.
  have hbound : mdist y v<=n%:R*d.
    rewrite inner_metric_distanceE -inner_norm_topologyE.
    apply: le_trans (euclidean_norm_coordinate_sum (y-v)) _.
    apply: le_trans (_ : \sum_(j<n) `|(y-v) j|<=\sum_(j<n) d) _.
    + apply: ler_sum=> j _; rewrite !ffunE; exact: ltW (hcoord j).
    + by rewrite sumr_const card_ord -[(_ *+ n)]mulr_natl.
  apply: le_lt_trans hbound _.
  have hde : (n.+1)%:R*d=e by rewrite /d mulrC mulfVK ?(gt_eqF hden).
  rewrite -hde ltr_pM2r // ltr_nat; exact: ltnSn.
Qed.
