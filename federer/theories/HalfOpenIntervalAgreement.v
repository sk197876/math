(** Federer (1969), 2.5.18(3), p. 112: "u_#(phi){t : a < t < b} = g(b) -
    g(a) = psi^+{t : a < t < b} whenever -oo < a < b < oo and g is
    continuous at a. Consequently u_#(phi) and psi^+ agree on all Borel
    sets." This module supplies the measure theoretic step behind the word
    "Consequently". Two measures over R for which the Borel sets are
    measurable and the bounded intervals have finite measure, and which
    agree on the intervals {x : l <= x < r} whose end points avoid a
    countable set C, agree on all Borel sets. Every point is the limit of an
    increasing sequence of points outside C, because every open interval
    contains points outside C; continuity from below and from above
    (2.1.3(4), (5), p. 55) extends the agreement to all intervals {x : a <=
    x < b}. The dyadic argument of LebesgueLineCharacterisation.v then gives
    agreement on open sets, and the open outer approximation of Borel sets,
    2.2.2, p. 61, gives agreement on Borel sets. Neither measure is assumed
    to be Borel regular. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals
  constructive_ereal topology normedtype.
From mathcomp Require Import lra.
From Federer Require Import RealMetricBackground TopologicalBorel MeasureUP MeasureBasic
  MeasureFiniteAdditivity MeasureFiniteClosure MeasureContinuityBelow MeasureContinuityAbove
  ExtendedRealOrderLimit ExtendedIncreasingLimitSupremum ArchimedeanReciprocal
  IntervalBumpFunctions BorelOpenApproximation LebesgueLineCharacterisation
  StieltjesInducedUniqueness.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section AvoidingApproximation.
Variable R : realType.

(** Source for [running_maximum]: the maxima max{w_0, ..., w_n} of the
    first terms of a sequence; supporting definition for the increasing
    approximation of a point by points outside a countable set in
    Federer 2.5.18(3), p. 112. *)
Fixpoint running_maximum (w : nat -> R) (n : nat) : R :=
  if n is m.+1 then Order.max (running_maximum w m) (w m.+1) else w 0%N.

(** Source for [running_maximum_succ]: the recursion
    max{w_0, ..., w_(n+1)} = max{max{w_0, ..., w_n}, w_(n+1)}; supporting
    lemma for Federer 2.5.18(3), p. 112. *)
Lemma running_maximum_succ (w : nat -> R) (n : nat) :
  running_maximum w n.+1 = Order.max (running_maximum w n) (w n.+1).
Proof. by []. Qed.

(** Source for [running_maximum_ge]: w_n <= max{w_0, ..., w_n};
    supporting lemma for Federer 2.5.18(3), p. 112. *)
Lemma running_maximum_ge (w : nat -> R) (n : nat) : w n <= running_maximum w n.
Proof. by case: n=> [|n]; [exact: lexx | rewrite running_maximum_succ le_max lexx orbT]. Qed.

(** Source for [running_maximum_mono]: the maxima increase with n;
    supporting lemma for Federer 2.5.18(3), p. 112. *)
Lemma running_maximum_mono (w : nat -> R) (n m : nat) :
  (n <= m)%N -> running_maximum w n <= running_maximum w m.
Proof.
elim: m=> [|m ih]; first by rewrite leqn0 => /eqP ->.
rewrite leq_eqVlt => /orP[/eqP ->|]; first exact: lexx.
rewrite ltnS => hnm; apply: le_trans (ih hnm) _.
by rewrite running_maximum_succ le_max lexx.
Qed.

(** Source for [running_maximum_value]: max{w_0, ..., w_n} is one of the
    terms w_i; supporting lemma for Federer 2.5.18(3), p. 112. *)
Lemma running_maximum_value (w : nat -> R) (n : nat) : exists i, running_maximum w n = w i.
Proof.
elim: n=> [|n [i hi]]; first by exists 0%N.
rewrite running_maximum_succ hi; case: (leP (w i) (w n.+1))=> _.
- by exists n.+1.
- by exists i.
Qed.

(** Source for [avoiding_left_approximation]: every real number a is the
    limit of an increasing sequence of numbers below a outside a given
    countable set C; supporting lemma for the passage from the points of
    continuity of g to all points in Federer 2.5.18(3), p. 112. *)
Lemma avoiding_left_approximation (C : set R) (a : R) : countable C ->
  exists z : nat -> R, (forall n m, (n <= m)%N -> z n <= z m) /\ (forall n, z n < a) /\
    (forall n, ~ C (z n)) /\ (forall x, x < a -> exists n, x < z n).
Proof.
move=> hC.
have hw : forall n : nat, exists w, (a - n.+1%:R^-1 < w < a) /\ ~ C w.
  move=> n; apply: (open_interval_avoid_countable hC).
  by rewrite ltrBlDr ltrDl invr_gt0 ltr0Sn.
have [w hw'] := choice hw.
exists (running_maximum w); split; first exact: running_maximum_mono.
split.
  by move=> n; have [i ->] := running_maximum_value w n; have /andP[_ h] := (hw' i).1.
split.
  by move=> n; have [i ->] := running_maximum_value w n; exact: (hw' i).2.
move=> x hx.
have hax : 0 < a - x by rewrite subr_gt0.
have [n hn] := real_reciprocal_below hax.
exists n; have /andP[h1 _] := (hw' n).1.
apply: lt_le_trans (running_maximum_ge w n).
move: hn h1; set e := n.+1%:R^-1 => hn h1.
by lra.
Qed.

(** Source for [half_open_interval_borel]: the interval
    {x : l <= x < r} is a Borel set, the difference of two closed
    segments, Federer 2.2.1, p. 60; supporting lemma for 2.5.18(3),
    p. 112. *)
Lemma half_open_interval_borel (l r : R) : borel_set `[l, r[.
Proof.
have -> : `[l, r[ = `[l, r] `\` `[r, r].
  apply/seteqP; split=> y; rewrite /= !in_itv /=.
  - move=> /andP[h1 h2]; split; first by rewrite h1 ltW.
    by move=> /andP[h3 _]; move: h2; rewrite ltNge h3.
  - move=> [/andP[h1 h2] hn]; rewrite h1 /= lt_neqAle h2 andbT.
    by apply/negP=> /eqP hy; apply: hn; rewrite hy lexx.
by apply: borel_set_difference; apply: closed_borel_set; exact: segment_closed_real.
Qed.

(** Source for [half_open_interval_empty]: {x : l <= x < r} is empty
    unless l < r; supporting lemma for Federer 2.5.18(3), p. 112. *)
Lemma half_open_interval_empty (l r : R) : r <= l -> `[l, r[ = set0.
Proof.
move=> hrl; apply/seteqP; split=> y // ; rewrite /= in_itv /= => /andP[h1 h2].
by have := le_lt_trans h1 h2; rewrite ltNge hrl.
Qed.

End AvoidingApproximation.

Section HalfOpenAgreement.
Variable R : realType.
Variables (mu1 mu2 : set R -> \bar R) (C : set R).
Hypothesis hm1 : is_measure mu1.
Hypothesis hm2 : is_measure mu2.
Hypothesis hb1 : forall A, borel_set A -> measure_measurable mu1 A.
Hypothesis hb2 : forall A, borel_set A -> measure_measurable mu2 A.
Hypothesis hf1 : forall a b : R, (mu1 `[a, b[ < +oo)%E.
Hypothesis hf2 : forall a b : R, (mu2 `[a, b[ < +oo)%E.
Hypothesis hC : countable C.
Hypothesis hagree : forall l r : R, l < r -> ~ C l -> ~ C r -> mu1 `[l, r[ = mu2 `[l, r[.

(** Source for [half_open_agree_left_avoiding]: the agreement on
    {x : l <= x < b} for l outside C and arbitrary b, by continuity from
    below, Federer 2.1.3(4), p. 55; supporting lemma for 2.5.18(3),
    p. 112. *)
Lemma half_open_agree_left_avoiding (l b : R) : ~ C l -> mu1 `[l, b[ = mu2 `[l, b[.
Proof.
move=> hl.
have [z [hzm [hzb [hzC hzlim]]]] := avoiding_left_approximation b hC.
pose F n := `[l, z n[.
have hF1 : forall n, measure_measurable mu1 (F n) by move=> n; exact: hb1 (half_open_interval_borel l (z n)).
have hF2 : forall n, measure_measurable mu2 (F n) by move=> n; exact: hb2 (half_open_interval_borel l (z n)).
have hmono : forall n m, (n <= m)%N -> F n `<=` F m.
  move=> n m hnm y; rewrite /F /= !in_itv /= => /andP[h1 h2].
  by rewrite h1 /=; exact: lt_le_trans h2 (hzm n m hnm).
have hU : \bigcup_n F n = `[l, b[.
  apply/seteqP; split=> y.
  - move=> [n _]; rewrite /F /= !in_itv /= => /andP[h1 h2].
    by rewrite h1 /=; exact: lt_trans h2 (hzb n).
  - rewrite /= in_itv /= => /andP[h1 h2]; have [n hn] := hzlim y h2.
    by exists n=> //; rewrite /F /= in_itv /= h1 hn.
have hseq : (fun n => mu1 (F n)) = (fun n => mu2 (F n)).
  apply/funext=> n; rewrite /F; case: (ltP l (z n))=> h.
  - exact: hagree h hl (hzC n).
  - by rewrite (half_open_interval_empty h) (measure_empty hm1) (measure_empty hm2).
have h1 := measure_continuity_below hm1 hF1 hmono.
have h2 := measure_continuity_below hm2 hF2 hmono.
rewrite hU in h1 h2; rewrite hseq in h1.
exact: (extended_order_limit_unique h1.2 h2.2).
Qed.

(** Source for [half_open_agree_all]: the agreement on every interval
    {x : a <= x < b}, by continuity from above, Federer 2.1.3(5), p. 55;
    supporting lemma for 2.5.18(3), p. 112. *)
Lemma half_open_agree_all (a b : R) : mu1 `[a, b[ = mu2 `[a, b[.
Proof.
have [z [hzm [hza [hzC hzlim]]]] := avoiding_left_approximation a hC.
pose F n := `[z n, b[.
have hF1 : forall n, measure_measurable mu1 (F n) by move=> n; exact: hb1 (half_open_interval_borel (z n) b).
have hF2 : forall n, measure_measurable mu2 (F n) by move=> n; exact: hb2 (half_open_interval_borel (z n) b).
have hmono : forall n m, (n <= m)%N -> F m `<=` F n.
  move=> n m hnm y; rewrite /F /= !in_itv /= => /andP[h1 h2].
  by rewrite h2 andbT; exact: le_trans (hzm n m hnm) h1.
have hI : \bigcap_n F n = `[a, b[.
  apply/seteqP; split=> y.
  - move=> hy; have := hy 0%N Logic.I; rewrite /F /= !in_itv /= => /andP[_ hyb].
    rewrite hyb andbT leNgt; apply/negP=> hya; have [n hn] := hzlim y hya.
    by have := hy n Logic.I; rewrite /F /= in_itv /= => /andP[h _]; move: hn; rewrite ltNge h.
  - rewrite /= in_itv /= => /andP[h1 h2] n _; rewrite /F /= in_itv /= h2 andbT.
    exact: le_trans (ltW (hza n)) h1.
have hseq : (fun n => mu1 (F n)) = (fun n => mu2 (F n)).
  by apply/funext=> n; exact: half_open_agree_left_avoiding (hzC n).
have h1 := measure_continuity_above hm1 hF1 hmono (hf1 (z 0%N) b).
have h2 := measure_continuity_above hm2 hF2 hmono (hf2 (z 0%N) b).
rewrite hI in h1 h2; rewrite hseq in h1.
exact: (extended_order_limit_unique h1.2 h2.2).
Qed.

(** Source for [dyadic_union_borel_measurable]: the finite unions of
    dyadic cells are measurable for a measure measuring the Borel sets,
    Federer 2.1.3, p. 55; supporting lemma for 2.5.18(3), p. 112. *)
Lemma dyadic_union_borel_measurable (mu : set R -> \bar R) (V : set R) (n k : nat) :
  is_measure mu -> (forall A, borel_set A -> measure_measurable mu A) ->
  measure_measurable mu (dyadic_union V n k).
Proof.
move=> hm hb; elim: k=> [|k ih].
  have -> : dyadic_union V n 0 = set0 by apply/seteqP; split=> x // [j []].
  by apply: hb; apply: open_borel_set; exact: open0.
case: (pselect (dyadic_cell n k `<=` V))=> hk.
- have -> : dyadic_union V n k.+1 = dyadic_cell n k `|` dyadic_union V n k.
    apply/seteqP; split=> x.
    + move=> [j [hj hjV hx]]; move: hj; rewrite ltnS leq_eqVlt => /orP[/eqP hjk|hjk].
        by left; rewrite -hjk.
      by right; exists j.
    + by move=> [hx|[j [hj hjV hx]]]; [exists k | exists j; split=> //; exact: ltnW].
  exact: (measure_measurable_union hm (hb _ (half_open_interval_borel _ _)) ih).
- have -> : dyadic_union V n k.+1 = dyadic_union V n k.
    apply/seteqP; split=> x.
    + move=> [j [hj hjV hx]]; move: hj; rewrite ltnS leq_eqVlt => /orP[/eqP hjk|hjk].
        by exfalso; apply: hk; rewrite -hjk.
      by exists j.
    + by move=> [j [hj hjV hx]]; exists j; split=> //; exact: ltnW.
  exact: ih.
Qed.

(** Source for [dyadic_union_half_open_agree]: the two measures agree
    on the finite unions of dyadic cells, by finite additivity, Federer
    2.1.3, p. 55; supporting lemma for 2.5.18(3), p. 112. *)
Lemma dyadic_union_half_open_agree (V : set R) (n k : nat) :
  mu1 (dyadic_union V n k) = mu2 (dyadic_union V n k).
Proof.
have hcell : forall j, mu1 (dyadic_cell n j) = mu2 (dyadic_cell n j).
  by move=> j; exact: half_open_agree_all.
elim: k=> [|k ih].
  have -> : dyadic_union V n 0 = set0 by apply/seteqP; split=> x // [j []].
  by rewrite (measure_empty hm1) (measure_empty hm2).
case: (pselect (dyadic_cell n k `<=` V))=> hk.
- have heq : dyadic_union V n k.+1 = dyadic_cell n k `|` dyadic_union V n k.
    apply/seteqP; split=> x.
    + move=> [j [hj hjV hx]]; move: hj; rewrite ltnS leq_eqVlt => /orP[/eqP hjk|hjk].
        by left; rewrite -hjk.
      by right; exists j.
    + by move=> [hx|[j [hj hjV hx]]]; [exists k | exists j; split=> //; exact: ltnW].
  have hdis : forall x, dyadic_cell n k x -> dyadic_union V n k x -> False.
    by move=> x hx [j [hj _ hjx]]; exact: dyadic_cell_disjoint hj hjx hx.
  rewrite heq (measure_disjoint_union (hb1 (half_open_interval_borel _ _)) hdis).
  by rewrite (measure_disjoint_union (hb2 (half_open_interval_borel _ _)) hdis) hcell ih.
- have -> : dyadic_union V n k.+1 = dyadic_union V n k.
    apply/seteqP; split=> x.
    + move=> [j [hj hjV hx]]; move: hj; rewrite ltnS leq_eqVlt => /orP[/eqP hjk|hjk].
        by exfalso; apply: hk; rewrite -hjk.
      by exists j.
    + by move=> [j [hj hjV hx]]; exists j; split=> //; exact: ltnW.
  exact: ih.
Qed.

(** Source for [half_open_open_agree]: the two measures agree on open
    sets, by continuity from below along the dyadic unions, Federer
    2.1.3(4), p. 55; supporting lemma for 2.5.18(3), p. 112. *)
Lemma half_open_open_agree (V : set R) : open V -> mu1 V = mu2 V.
Proof.
move=> hV; rewrite -(dyadic_union_open hV).
have hmeas1 := fun n => dyadic_union_borel_measurable V n (dyadic_bound n) hm1 hb1.
have hmeas2 := fun n => dyadic_union_borel_measurable V n (dyadic_bound n) hm2 hb2.
have hmono : forall n m, (n <= m)%N ->
    dyadic_union V n (dyadic_bound n) `<=` dyadic_union V m (dyadic_bound m).
  by move=> n m hnm; exact: (@dyadic_union_monotone_le R V n m hnm).
have h1 := measure_continuity_below hm1 hmeas1 hmono.
have h2 := measure_continuity_below hm2 hmeas2 hmono.
have heq : (fun n => mu1 (dyadic_union V n (dyadic_bound n)))
    = (fun n => mu2 (dyadic_union V n (dyadic_bound n))).
  by apply/funext=> n; exact: dyadic_union_half_open_agree.
rewrite heq in h1.
exact: (extended_order_limit_unique h1.2 h2.2).
Qed.

End HalfOpenAgreement.

(** Source for [open_agree_borel_le]: if two measures agree on open
    sets, the first measures the Borel sets and is finite on bounded
    intervals, then the second does not exceed the first on Borel sets,
    by the open outer approximation of Federer 2.2.2(2), p. 61;
    supporting lemma for 2.5.18(3), p. 112. *)
Lemma open_agree_borel_le (R : realType) (mu1 mu2 : set R -> \bar R) :
  is_measure mu1 -> is_measure mu2 -> (forall A, borel_set A -> measure_measurable mu1 A) ->
  (forall a b : R, (mu1 `[a, b[ < +oo)%E) -> (forall V, open V -> mu1 V = mu2 V) ->
  forall B, borel_set B -> (mu2 B <= mu1 B)%E.
Proof.
move=> hm1 hm2 hb1 hf1 hV B hB.
pose W := fun n : nat => `](- n%:R : R), n%:R[.
have hW : forall n, open (W n) /\ (mu1 (W n) < +oo)%E.
  move=> n; split; first by apply: interval_open.
  apply: le_lt_trans (measure_mono hm1 (_ : W n `<=` `[- n%:R, n%:R[)) (hf1 _ _).
  by move=> y; rewrite /W /= !in_itv /= => /andP[h1 h2]; rewrite (ltW h1) h2.
have hcover : B `<=` \bigcup_n W n.
  move=> y _; have /andP[_ hy] := truncn_itv (normr_ge0 y).
  exists (Num.truncn `|y|).+1=> //; move: hy; rewrite /W /= in_itv /= ltr_norml.
  by [].
apply/lee_addgt0Pr=> e he.
have ho : forall U, open U -> measure_measurable mu1 U.
  by move=> U hU; apply: hb1; exact: open_borel_set.
have [O [hO [hBO hOB]]] := metric_borel_open_approximation hm1 ho hB hW hcover he.
apply: le_trans (measure_mono hm2 hBO) _.
rewrite -(hV O hO).
have hsplit := hb1 _ hB O.
have hOB' : O `&` B = B.
  by apply/seteqP; split=> y; [move=> [] | move=> hy; split=> //; exact: hBO].
by rewrite hsplit hOB'; exact: leeD (lexx _) (ltW hOB).
Qed.

(** Source for [half_open_agreement_borel]: two measures over R which
    measure the Borel sets, are finite on bounded intervals and agree on
    the intervals {x : l <= x < r} with end points outside a countable
    set agree on all Borel sets; the step "Consequently u_#(phi) and
    psi^+ agree on all Borel sets" of Federer 2.5.18(3), p. 112. *)
Theorem half_open_agreement_borel (R : realType) (mu1 mu2 : set R -> \bar R) (C : set R) :
  is_measure mu1 -> is_measure mu2 ->
  (forall A, borel_set A -> measure_measurable mu1 A) ->
  (forall A, borel_set A -> measure_measurable mu2 A) ->
  (forall a b : R, (mu1 `[a, b[ < +oo)%E) -> (forall a b : R, (mu2 `[a, b[ < +oo)%E) ->
  countable C -> (forall l r : R, l < r -> ~ C l -> ~ C r -> mu1 `[l, r[ = mu2 `[l, r[) ->
  forall B, borel_set B -> mu1 B = mu2 B.
Proof.
move=> hm1 hm2 hb1 hb2 hf1 hf2 hC hagree B hB.
have hV : forall V, open V -> mu1 V = mu2 V.
  by move=> V hV; exact: (half_open_open_agree hm1 hm2 hb1 hb2 hf1 hf2 hC hagree hV).
apply/le_anti/andP; split.
- exact: (open_agree_borel_le hm2 hm1 hb2 hf2 (fun V hV' => esym (hV V hV')) hB).
- exact: (open_agree_borel_le hm1 hm2 hb1 hf1 hV hB).
Qed.
