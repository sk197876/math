(** Federer (1969), 2.5.18(2), p. 112: "Therefore g_# maps the measures
    induced by h o g onto the measures induced by h." The formalisation in
    StieltjesImageMeasures.v adds the hypothesis im g = R. This file proves
    that the added hypothesis cannot be omitted: for the continuous
    increasing map g(x) = x/(1 + |x|) of R onto ]-1, 1[ and h(x) = x, the
    set {t : 2 <= t <= 3} has measure 0 for the image under g of every
    measure induced by h o g, since no point of R is mapped into it, but
    measure 1 for the measure induced by h, which is the Lebesgue measure
    L^1 (StieltjesLebesgueInduced.v). *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  constructive_ereal topology normedtype.
From mathcomp Require Import lra.
From Federer Require Import RealMetricBackground CurveArcLength MeasureUP MeasureBasic
  MeasurePushforward LebesgueScalarMeasure StieltjesMonotone StieltjesImageMeasures
  StieltjesInducedPairLaws StieltjesLebesgueInduced.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section ImageSurjectivity.
Variable R : realType.

(** Source for [bounded_increasing]: the map g(x) = x/(1 + |x|) of the
    counterexample to the unrestricted form of Federer 2.5.18(2), p. 112;
    a continuous increasing map of R onto ]-1, 1[ (supporting definition). *)
Definition bounded_increasing (x : R) : R := x / (1 + `|x|).

(** Source for [bounded_increasing_denominator]: supporting positivity
    of the denominator 1 + |x| for the counterexample to Federer
    2.5.18(2), p. 112. *)
Lemma bounded_increasing_denominator (x : R) : 0 < 1 + `|x|.
Proof. by rewrite ltr_pwDl. Qed.

(** Source for [bounded_increasing_continuous]: g is continuous, a
    hypothesis of Federer 2.5.18(2), p. 112, for the counterexample. *)
Lemma bounded_increasing_continuous : continuous bounded_increasing.
Proof.
move=> x; apply: (@continuousM R R^o id (fun y => (1 + `|y|)^-1) x); first exact: cvg_id.
apply: (@continuousV R R^o (fun y => 1 + `|y|) x).
  by rewrite gt_eqF // bounded_increasing_denominator.
apply: (@continuousD R R^o R^o (fun _ => 1) (fun y => `|y|) x); first exact: cvg_cst.
exact: (@norm_continuous _ R^o).
Qed.

(** Source for [bounded_increasing_increasing]: g is increasing,
    g(s) < g(t) whenever s < t, as Federer 2.5.18(2), p. 112, requires;
    supporting lemma for the counterexample. *)
Lemma bounded_increasing_increasing (x y : R) : x < y -> bounded_increasing x < bounded_increasing y.
Proof.
move=> hxy; rewrite /bounded_increasing.
rewrite ltr_pdivrMr ?bounded_increasing_denominator // mulrAC.
rewrite ltr_pdivlMr ?bounded_increasing_denominator //.
case: (leP 0 x)=> hx; case: (leP 0 y)=> hy.
- rewrite !ger0_norm //; nra.
- lra.
- rewrite ger0_norm // ltr0_norm //; nra.
- rewrite !ltr0_norm //; nra.
Qed.

(** Source for [bounded_increasing_bound]: |g(x)| < 1, so im g is a
    subset of ]-1, 1[ and im g is not R, the hypothesis whose omission
    from Federer 2.5.18(2), p. 112, is refuted (supporting lemma). *)
Lemma bounded_increasing_bound (x : R) : `|bounded_increasing x| < 1.
Proof.
have hd := bounded_increasing_denominator x.
rewrite /bounded_increasing normrM normfV (@ger0_norm _ (1 + `|x|)) ?(ltW hd) //.
rewrite ltr_pdivrMr // mul1r; lra.
Qed.

(** Source for [bounded_increasing_nondecreasing]: supporting monotonicity
    used to give h o g finite variation on segments, Federer 2.5.17,
    p. 110, in the counterexample to 2.5.18(2), p. 112. *)
Lemma bounded_increasing_nondecreasing (x y : R) :
  x <= y -> bounded_increasing x <= bounded_increasing y.
Proof.
rewrite le_eqVlt=> /orP[/eqP -> //|hxy].
exact: ltW (bounded_increasing_increasing hxy).
Qed.

(** Source for [stieltjes_image_requires_onto]: the hypothesis im g = R
    added to Federer 2.5.18(2), p. 112, cannot be omitted (. Here g is
    continuous and increasing, h and h o g have finite variation on every
    segment, and the image under g of the measure psi^+ induced by h o g
    differs from the measure psi^+ induced by h. Local counterexample. *)
Theorem stieltjes_image_requires_onto :
  exists g h : R -> R,
    continuous g /\ (forall x y, x < y -> g x < g y) /\
    curve_locally_finite_variation (h : R -> real_line_metric R) /\
    curve_locally_finite_variation ((h \o g) : R -> real_line_metric R) /\
    forall psip psim psip' psim' : set R -> \bar R,
      is_induced_measure_pair (h \o g) psip psim -> is_induced_measure_pair h psip' psim' ->
      measure_pushforward g psip <> psip'.
Proof.
exists bounded_increasing, (fun t : R => t).
split; first exact: bounded_increasing_continuous.
split; first exact: bounded_increasing_increasing.
split; first exact: identity_locally_finite_variation.
split; first exact: (monotone_locally_finite_variation bounded_increasing_nondecreasing).
move=> psip psim psip' psim' [P [Q [_ [_ [hm _]]]]] hpair' he.
have [hL _] := identity_induced_lebesgue hpair'.
have hpre : bounded_increasing @^-1` `[2%:R, 3%:R] = set0 :> set R.
  apply/seteqP; split=> x // /=; rewrite in_itv /= => /andP[h2 _].
  have := bounded_increasing_bound x; rewrite ltNge=> /negP; apply.
  by apply: le_trans (ler_norm _); apply: le_trans h2; rewrite ler1n.
have h0 : measure_pushforward bounded_increasing psip `[2%:R, 3%:R] = 0%E.
  by rewrite /measure_pushforward hpre (measure_empty hm).
have h1 : psip' `[2%:R, 3%:R] = 1%E.
  by rewrite hL lebesgue_scalar_segment ?ler_nat // -natrB.
by move: h0; rewrite he h1 => /eqP; rewrite eqe oner_eq0.
Qed.

(** Source for [stieltjes_image_unrestricted_false]: the sentence of Federer
    2.5.18(2), p. 112, "g_# maps the measures induced by h o g onto the
    measures induced by h" is false for continuous increasing g without im g
    = R, even when h and h o g have finite variation on every segment. *)
Theorem stieltjes_image_unrestricted_false :
  ~ (forall g h : R -> R, continuous g -> (forall x y, x < y -> g x < g y) ->
      curve_locally_finite_variation (h : R -> real_line_metric R) ->
      curve_locally_finite_variation ((h \o g) : R -> real_line_metric R) ->
      forall psip psim : set R -> \bar R, is_induced_measure_pair (h \o g) psip psim ->
        is_induced_measure_pair h (measure_pushforward g psip) (measure_pushforward g psim)).
Proof.
move=> hall.
have [g [h [hgc [hinc [hh [hhg hne]]]]]] := stieltjes_image_requires_onto.
have [psip [psim hpair]] := induced_measure_pair_exists hhg.
have [psip' [psim' hpair']] := induced_measure_pair_exists hh.
have himg := hall g h hgc hinc hh hhg psip psim hpair.
have [he _] := induced_measure_pair_unique himg hpair'.
exact: hne psip psim psip' psim' hpair hpair' he.
Qed.

End ImageSurjectivity.
