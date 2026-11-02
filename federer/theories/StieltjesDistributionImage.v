(** Federer (1969), 2.5.18(3), p. 112: if phi measures X, phi(X) < oo, u is
    an R valued phi measurable function and g(t) = phi{x : u(x) < t} for t
    in R, then "for the proof we define psi^+ as in 2.5.17 and observe that
    u_#(phi){t : a < t < b} = g(b) - g(a) = psi^+{t : a < t < b} whenever
    -oo < a < b < oo and g is continuous at a. Consequently u_#(phi) and
    psi^+ agree on all Borel sets". Here the statement is proved for every
    pair psi^+, psi^- of measures induced by g. Since g is nondecreasing,
    psi^- = 0 by 2.5.17. On the intervals {t : l <= t < r} whose end points
    are points of continuity of g both measures take the value g(r) - g(l):
    for u_#(phi) by the Caratheodory splitting of {x : u(x) < r} by {x :
    u(x) < l}, for psi^+ by the identity g(r) - g(l) = psi^+{t : l < t < r}
    of 2.5.17 and the vanishing of psi^+ at points of continuity. The points
    of discontinuity form a countable set by 2.5.16, p. 109, and
    HalfOpenIntervalAgreement.v extends the agreement to all Borel sets. The
    open interval form of Federer's display is used only through this
    half-open variant. The integral formula of 2.5.18(3) is proved
    separately in StieltjesDistributionFunction.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals
  constructive_ereal topology normedtype.
From mathcomp Require Import lra.
From Federer Require Import RealMetricBackground RealMetricCompleteness TopologicalBorel MeasureUP
  MeasureBasic MeasurePushforward MeasurableBorelFamily MeasurableFunctionUP PartialFunctionUP
  PartialFunctionBasic
  PartialFunctionPreimages RadonMeasureUP BorelRegularMeasureUP FunctionLatticeRegularityUP
  RealIntegralFunctionalUP MeasureIntegralUP MeasureSubsetIntegral SummableRealFunctionUP
  CompactSupportFunctionUP CurveVariationUP CurveArcLength CurveDiscontinuities StieltjesSums
  StieltjesIntegral StieltjesDaniellIntegral StieltjesMonotone StieltjesContinuityPoints
  StieltjesDistributionFunction StieltjesImageMeasures StieltjesInducedPairLaws
  HalfOpenIntervalAgreement.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section DistributionImage.
Variable R : realType.
Variable X : choiceType.
Variables (phi : set X -> \bar R) (u : X -> R).
Hypothesis hm : is_measure phi.
Hypothesis hfin : (phi setT < +oo)%E.
Hypothesis hu : is_measure_measurable_function phi (partial_function_total (u : X -> real_line_metric R)).
Local Notation g := (distribution_function phi u).

(** Source for [image_measure_borel_measurable]: the Borel sets are
    u_#(phi) measurable, because the inverse images of open sets under
    the phi measurable function u are phi measurable, Federer 2.3.2,
    p. 72, 2.1.2, p. 54, and 2.2.1, p. 60; supporting lemma for
    2.5.18(3), p. 112. *)
Lemma image_measure_borel_measurable (B : set R) :
  borel_set B -> measure_measurable (measure_pushforward u phi) B.
Proof.
apply: (open_measurable_implies_borel_measurable (measure_pushforward_is_measure u hm)).
move=> U hU T; rewrite /measure_pushforward.
have hU' : open (U : set (real_line_metric R)) by exact: hU.
have h := measurable_function_open_preimage hu hU'.
rewrite partial_function_total_preimage in h.
by rewrite setDE !preimage_setI preimage_setC -setDE; exact: h.
Qed.

(** Source for [image_measure_half_open_finite]: u_#(phi) is finite,
    since phi(X) < oo, Federer 2.5.18(3), p. 112; supporting lemma. *)
Lemma image_measure_half_open_finite (a b : R) : (measure_pushforward u phi `[a, b[ < +oo)%E.
Proof.
apply: le_lt_trans hfin; rewrite /measure_pushforward.
exact (measure_mono hm (subsetT _)).
Qed.

(** Source for [image_measure_half_open]: u_#(phi){t : l <= t < r} =
    g(r) - g(l) for l <= r, Federer 2.5.18(3), p. 112; supporting lemma
    for the displayed identity there. *)
Lemma image_measure_half_open (l r : R) :
  l <= r -> measure_pushforward u phi `[l, r[ = (g r - g l)%:E.
Proof.
move=> hlr; rewrite /measure_pushforward.
have -> : u @^-1` `[l, r[ = cell_set u l r.
  apply/seteqP; split=> x; rewrite /cell_set /= in_itv /=.
  - by move=> /andP[h1 h2].
  - by move=> [h1 h2]; rewrite h1 h2.
by rewrite -(cell_set_measure hm hfin hu hlr) fineK //; exact: cell_set_finite.
Qed.

Variables psip psim : set R -> \bar R.
Hypothesis hpair : is_induced_measure_pair g psip psim.

(** Source for [distribution_induced_negative_zero]: g is nondecreasing,
    hence psi^- = 0, Federer 2.5.18(3) and 2.5.17, p. 111-112. *)
Lemma distribution_induced_negative_zero : psim = (fun _ => 0%E).
Proof.
exact: (induced_measure_pair_monotone (distribution_function_variation u hm hfin)
  (distribution_function_nondecreasing u hm hfin) hpair).1.
Qed.

(** Source for [distribution_induced_half_open]: psi^+{t : l <= t < r} =
    g(r) - g(l) whenever l < r and g is continuous at l and r, Federer
    2.5.18(3), p. 112, from 2.5.17, p. 111; supporting lemma. *)
Lemma distribution_induced_half_open (l r : R) :
  l < r -> g @ l --> g l -> g @ r --> g r -> psip `[l, r[ = (g r - g l)%:E.
Proof.
move=> hlr hcl hcr.
have hk := distribution_function_variation u hm hfin.
have [hmp [_ [_ [_ [_ [_ [_ [_ [_ [_ [hpoint [hincr _]]]]]]]]]]]] :=
  induced_measure_pair_laws hk hpair.
have [h _] := hincr l r hlr hcl hcr.
rewrite distribution_induced_negative_zero /= sube0 in h.
rewrite h; apply/le_anti/andP; split.
- have hsub : `[l, r[ `<=` `]l, r[ `|` [set l].
    move=> x; rewrite /= !in_itv /= => /andP[h1 h2].
    move: h1; rewrite le_eqVlt => /orP[/eqP <-|h1]; first by right.
    by left; rewrite h1 h2.
  apply: le_trans (measure_mono hmp hsub) _.
  by apply: le_trans (measure_union_le _ _ hmp) _; rewrite (hpoint l hcl).1 adde0.
- apply: (measure_mono hmp)=> x; rewrite /= !in_itv /= => /andP[h1 h2].
  by rewrite (ltW h1) h2.
Qed.

(** Source for [distribution_image_induced_borel]: "Consequently
    u_#(phi) and psi^+ agree on all Borel sets", Federer 2.5.18(3),
    p. 112. Direct formalisation for every pair psi^+, psi^- induced by
    the phi distribution function g of u, together with psi^- = 0. *)
Theorem distribution_image_induced_borel :
  psim = (fun _ => 0%E) /\ forall B, borel_set B -> measure_pushforward u phi B = psip B.
Proof.
split; first exact: distribution_induced_negative_zero.
have hk := distribution_function_variation u hm hfin.
have [hmp [hmn [_ [_ [hborp [_ [_ [_ [_ [hbound _]]]]]]]]]] := induced_measure_pair_laws hk hpair.
pose C := curve_jump_points (g : R -> real_line_metric R).
have hC : countable C := curve_jump_points_countable hk.
have hcont : forall x, ~ C x -> g @ x --> g x.
  move=> x hx; apply: contrapT=> hn; apply: hx.
  exact/(curve_jump_points_iff hk (@real_line_metric_complete R) x).
apply: (half_open_agreement_borel (measure_pushforward_is_measure u hm) hmp
  image_measure_borel_measurable (borel_regular_borel_measurable hmp hborp)
  image_measure_half_open_finite _ hC).
- move=> a b; case: (ltP a b)=> hab; last by rewrite (half_open_interval_empty hab) (measure_empty hmp) ltry.
  have hsub : `[a, b[ `<=` `]a - 1, b[.
    by move=> x; rewrite /= !in_itv /= => /andP[h1 h2]; rewrite h2 andbT; lra.
  apply: le_lt_trans (measure_mono hmp hsub) _.
  have hab' : a - 1 <= b by lra.
  apply: le_lt_trans _ (ltry (total_variation g (a - 1) b)).
  apply: le_trans _ (hbound _ _ hab').
  exact: lee_paddr (measure_nonnegative hmn _) (lexx _).
- move=> l r hlr hl hr.
  by rewrite (image_measure_half_open (ltW hlr)) (distribution_induced_half_open hlr (hcont l hl) (hcont r hr)).
Qed.

(** Source for [distribution_image_open_interval]: "u_#(phi){t : a < t
    < b} = g(b) - g(a) = psi^+{t : a < t < b} whenever -oo < a < b < oo
    and g is continuous at a", Federer 2.5.18(3), p. 112. Direct
    formalisation, derived from the Borel agreement and the half-open
    identity at u_#(phi). *)
Corollary distribution_image_open_interval (a b : R) :
  a < b -> g @ a --> g a ->
  measure_pushforward u phi `]a, b[ = (g b - g a)%:E /\ psip `]a, b[ = (g b - g a)%:E.
Proof.
move=> hab hca.
have [_ hB] := distribution_image_induced_borel.
have hk := distribution_function_variation u hm hfin.
have [hmp [_ [_ [_ [_ [_ [_ [_ [_ [_ [hpoint _]]]]]]]]]]] := induced_measure_pair_laws hk hpair.
have hopen : psip `]a, b[ = psip `[a, b[.
  apply/le_anti/andP; split.
  - apply: (measure_mono hmp)=> x; rewrite /= !in_itv /= => /andP[h1 h2].
    by rewrite (ltW h1) h2.
  - have hsub : `[a, b[ `<=` `]a, b[ `|` [set a].
      move=> x; rewrite /= !in_itv /= => /andP[h1 h2].
      move: h1; rewrite le_eqVlt => /orP[/eqP <-|h1]; first by right.
      by left; rewrite h1 h2.
    apply: le_trans (measure_mono hmp hsub) _.
    by apply: le_trans (measure_union_le _ _ hmp) _; rewrite (hpoint a hca).1 adde0.
have hhalf : psip `[a, b[ = (g b - g a)%:E.
  by rewrite -(hB _ (half_open_interval_borel a b)) (image_measure_half_open (ltW hab)).
have hO : measure_pushforward u phi `]a, b[ = psip `]a, b[.
  by apply: hB; apply: open_borel_set; exact: interval_open.
by rewrite hO hopen hhalf.
Qed.

End DistributionImage.
