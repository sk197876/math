(** Federer (1969), 2.10.1, p. 170, alternative characterisation as an
    infimum over open-refinement bounds. The local erratum p. 3, book p. 170
    lines 24 and 35, corrects the reference to [F12]: Federer, On Lebesgue
    area (1955) Uniform ball covers give one inequality; the
    measurable-layer and summable-error construction gives the reverse
    inequality. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology lra.
From Federer Require Import NonnegativeSum MetricClosedBalls MetricDiameterUP MetricDiameter
  MetricScaleEnvelopeUP MetricScaleEnvelope CaratheodoryLimitUP CaratheodoryLimitMeasure
  CaratheodoryBorelRegular OpenRefinementBoundUP MetricRefinementApproximation ExtendedRealBounds MeasureUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [open_refinement_bound_controls_metric_measure]:
    direct uniform-ball-cover direction of the alternative
    formula in Federer 2.10.1, p. 170, corrected reference
    Federer1955 Theorem 2.5, p. 291. Uniform open ball
    covers of the whole space suffice; their refinements have
    arbitrarily small admissible diameters. *)
Lemma open_refinement_bound_controls_metric_measure (R : realType) (X : metricType R)
    (J : choiceType) (S : J -> set X) (cost : J -> \bar R)
    (mu : set X -> \bar R) (A : set X) (t : \bar R) :
  is_caratheodory_limit S cost mu ->
  is_open_refinement_bound S cost A t -> mu A<=t.
Proof.
move=> hmu ht; apply: (caratheodory_limit_least hmu)=> delta nu hd hn.
have [n hsmall] := reciprocal_metric_cutoffs_cofinal hd.
pose d : R := ((n.+1%:R)^-1)%R.
have hd0 : (0<d)%R by rewrite /d invr_gt0 ltr0n.
pose H := [set U : set X | exists x, U=[set y | (mdist x y<d/2)%R]].
have hopen U : H U -> open U.
  move=> [x ->]; exact: metric_open_ball_open.
have hcover : A `<=` \bigcup_(U in H) U.
  move=> x _; exists [set y | (mdist x y<d/2)%R]; first by exists x.
  by rewrite /= mdistxx divr_gt0 // ltr0n.
have [G [hGc [hGcov [href hcost]]]] := ht H hopen hcover.
have hdiam j : G j -> extended_metric_diameter (S j)<=delta.
  move=> hj; have [U [[x ->] hSU]] := href j hj.
  apply: le_trans (_ : extended_metric_diameter (S j)<=d%:E) hsmall.
  apply: (metric_diameter_least (extended_metric_diameter_specification (S j))).
  - rewrite lee_fin; exact: ltW hd0.
  - move=> y z hy hz; rewrite lee_fin.
    have hxy : (mdist x y<d/2)%R := hSU y hy.
    have hxz : (mdist x z<d/2)%R := hSU z hz.
    have htri := metric_triangle y x z; rewrite (metric_sym y x) in htri.
    have hdd : (d/2+d/2=d)%R by rewrite -mulr2n -[LHS]mulr_natr divfK ?pnatr_eq0.
    have hh := ltrD hxy hxz; rewrite hdd in hh.
    exact: le_trans htri (ltW hh).
exact: le_trans (@metric_scale_envelope_lower R X J S cost delta nu hn A G hGc hdiam hGcov)
  (ltW hcost).
Qed.

(** Source for [metric_caratheodory_open_cover_characterization]:
    direct full alternative infimum formula of Federer 2.10.1,
    p. 170, corrected reference Federer1955 Theorem 2.5,
    pp. 291–292. Every threshold satisfies the printed
    property for all open covers of A. The infimum may be
    infinite, and neither A nor the generator family need be
    Borel or separable. This theorem concerns metric spaces. *)
Theorem metric_caratheodory_open_cover_characterization (R : realType) (X : metricType R)
    (J : choiceType) (S : J -> set X) (cost : J -> \bar R)
    (mu : set X -> \bar R) (A : set X) :
  is_caratheodory_limit S cost mu -> (forall j, 0<=cost j) ->
  mu A=extended_real_inf [set t | is_open_refinement_bound S cost A t].
Proof.
move=> hmu hc.
apply/eqP; rewrite eq_le; apply/andP; split.
- apply: extended_real_inf_greatest=> t ht.
  exact: open_refinement_bound_controls_metric_measure hmu ht.
- case hval: (mu A)=> [M| |].
  + apply/lee_addgt0Pr=> e he.
    have hb : mu A<(M+e)%R%:E by rewrite hval lte_fin ltrDl.
    have ht := @metric_caratheodory_open_refinement_bound R X J S cost mu A
      (M+e)%R%:E hmu hc hb.
    rewrite -EFinD; exact: extended_real_inf_lower ht.
  + exact: leey.
  + have hm := caratheodory_limit_is_measure hmu hc.
    by have := measure_nonnegative hm A; rewrite hval.
Qed.
