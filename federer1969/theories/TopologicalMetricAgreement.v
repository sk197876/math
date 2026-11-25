(** Federer (1969), 2.10.1, p. 170: the alternative construction agrees with
    the metric construction. This proves the agreement also for the
    corrected whole-space open-cover convention used in general topological
    spaces. The stronger printed A-cover formula is already proved for
    metric spaces. Uniform ball covers give the reverse inequality to its
    arbitrary-cover refinement estimate. Source context, corrected paper
    reference and the local topological correction:
    TopologicalCaratheodoryUP.v and MetricRefinementCharacterization.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import MetricDiameterUP MetricDiameter MetricScaleEnvelopeUP
  CaratheodoryLimitUP CaratheodoryBorelRegular MetricRefinementCharacterization
  TopologicalCaratheodoryUP TopologicalOpenRefinementBound OpenRefiningEnvelopeUP
  OpenRefiningEnvelope ContinuousMetricBallCover ExtendedRealBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [topological_caratheodory_metric_agreement]:
    direct equality of the metric and alternative constructions
    in Federer 2.10.1, p. 170, corrected reference
    Federer1955 Theorem 2.5, pp. 291–292. The corrected
    whole-space-open-cover version equals the original metric
    measure, including infinite values and arbitrary target
    sets. No generator measurability assumption is imposed. *)
Theorem topological_caratheodory_metric_agreement (R : realType) (X : metricType R)
    (J : choiceType) (S : J -> set X) (cost : J -> \bar R)
    (mu psi : set X -> \bar R) :
  is_topological_caratheodory S cost mu -> is_caratheodory_limit S cost psi ->
  (forall j, 0<=cost j) -> forall A, mu A=psi A.
Proof.
move=> hm hp hc A; apply/eqP; rewrite eq_le; apply/andP; split.
- rewrite (@metric_caratheodory_open_cover_characterization R X J S cost psi A hp hc).
  apply: extended_real_inf_greatest=> t ht.
  apply: (@global_open_refinement_bound_controls_measure R X J S cost mu A t hm).
  move=> H [hHo hHc].
  have hAcov : A `<=` \bigcup_(U in H) U by move=> x _; exact: hHc x I.
  exact (ht H hHo hAcov).
- apply: (caratheodory_limit_least hp)=> delta nu hd hn.
  have [n hsmall] := reciprocal_metric_cutoffs_cofinal hd.
  pose d : R := ((n.+1%:R)^-1)%R.
  have hd0 : (0<d)%R by rewrite /d invr_gt0 ltr0n.
  pose f : X -> X := fun x => x.
  have hf : continuous f by move=> x; exact: cvg_id.
  pose H := continuous_metric_ball_cover f d.
  have hH : is_whole_space_open_cover H.
    exact: continuous_metric_ball_cover_whole hf hd0.
  pose omega := open_refining_envelope S cost H.
  have hw := open_refining_envelope_specification S cost H.
  have hbound : nu A<=omega A.
    apply: (open_refining_envelope_greatest hw)=> G hG hr hcov.
    have hdiam j : G j -> extended_metric_diameter (S j)<=delta.
      move=> hj.
      apply: le_trans (_ : extended_metric_diameter (S j)<=d%:E) hsmall.
      apply: (metric_diameter_least (extended_metric_diameter_specification (S j))).
      - rewrite lee_fin; exact: ltW hd0.
      - move=> x y hx hy; rewrite lee_fin; apply: ltW.
        exact (@continuous_ball_cover_generator_image_bound R X J X S f d j (hr j hj) x y hx hy).
    exact (@metric_scale_envelope_lower R X J S cost delta nu hn A G hG hdiam hcov).
  exact: le_trans hbound (@topological_caratheodory_upper R X J S cost mu hm A H omega hH hw).
Qed.
