(** Federer (1969), 2.5.17, p. 111: the one dimensional Lebesgue measure L^1
    "is the Borel regular measure characterized by the property that b - a =
    L^1{x : a <= x <= b} whenever -oo < a < b < oo". Two Borel regular
    measures over R with this property agree on the half-open dyadic cells
    {x : -n + j 2^-n <= x < -n + (j + 1) 2^-n}, hence by finite additivity
    on the finite unions W_n of the cells of rank n with j < 2n 2^n which
    are contained in a given open set V; the sets W_n increase to V, so the
    measures agree on V by continuity from below. Finally a Borel regular
    measure which is finite on the open intervals {x : -n < x < n} is
    approximated from outside by open sets, 2.2.3 and 2.2.2, so the two
    measures agree on every set. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  constructive_ereal topology normedtype.
From mathcomp Require Import ring lra zify.
From Stdlib Require Import Lia.
From Federer Require Import RealMetricBackground TopologicalBorel BorelRegularMeasureUP
  BorelRegularApproximation RadonMeasureUP MeasureUP MeasureBasic MeasureSplit
  MeasureFiniteAdditivity MeasureFiniteClosure MeasureContinuityBelow ExtendedRealOrderLimit
  ExtendedIncreasingLimitSupremum ArchimedeanReciprocal IntervalBumpFunctions
  CompactSupportFunctionUP FunctionLatticeRegularityUP RealIntegralFunctionalUP
  StieltjesDaniellIntegral LebesgueLineMeasure StieltjesBorelRegularity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section Characterisation.
Variable R : realType.
Local Notation KR := (@compactly_supported_continuous_functions R R).

(** Source for [dyadic_step]: the length 2^-n of the dyadic cells of
    rank n, used for Federer 2.5.17, p. 111. *)
Definition dyadic_step (n : nat) : R := (2 ^+ n)^-1.

(** Source for [dyadic_left]: the left end -n + j 2^-n of the dyadic cell
    of rank n and index j, Federer 2.5.17, p. 111. *)
Definition dyadic_left (n j : nat) : R := - n%:R + j%:R * dyadic_step n.

(** Source for [dyadic_cell]: the half-open dyadic cell
    {x : -n + j 2^-n <= x < -n + (j + 1) 2^-n}, Federer 2.5.17, p. 111. *)
Definition dyadic_cell (n j : nat) : set R := `[dyadic_left n j, dyadic_left n j + dyadic_step n[.

(** Source for [dyadic_bound]: the number 2n 2^n of cells of rank n
    covering {x : -n <= x < n}, Federer 2.5.17, p. 111. *)
Definition dyadic_bound (n : nat) : nat := (n.*2 * 2 ^ n)%N.

(** Source for [dyadic_union]: the union of the cells of rank n with
    index below k contained in V, Federer 2.5.17, p. 111. *)
Definition dyadic_union (V : set R) (n k : nat) : set R :=
  [set x | exists j, [/\ (j < k)%N, dyadic_cell n j `<=` V & dyadic_cell n j x]].

(** Source for [dyadic_step_gt0]: the cells have positive length,
    Federer 2.5.17, p. 111. *)
Lemma dyadic_step_gt0 (n : nat) : 0 < dyadic_step n.
Proof. by rewrite /dyadic_step invr_gt0 exprn_gt0. Qed.

(** Source for [dyadic_step_succ]: 2^-(n+1) + 2^-(n+1) = 2^-n, Federer
    2.5.17, p. 111. *)
Lemma dyadic_step_succ (n : nat) : dyadic_step n.+1 + dyadic_step n.+1 = dyadic_step n.
Proof.
have hp : (2 ^+ n : R) != 0 by rewrite expf_neq0 // pnatr_eq0.
by rewrite /dyadic_step exprS; field; rewrite hp.
Qed.

(** Source for [dyadic_left_succ_index]: consecutive left ends differ by
    the step, Federer 2.5.17, p. 111. *)
Lemma dyadic_left_succ_index (n j : nat) : dyadic_left n j.+1 = dyadic_left n j + dyadic_step n.
Proof. by rewrite /dyadic_left -addn1 natrD mulrDl mul1r addrA. Qed.

(** Source for [dyadic_left_refine]: the cell of rank n and index j
    starts where the cell of rank n+1 and index 2^(n+1) + 2j starts,
    Federer 2.5.17, p. 111. *)
Lemma dyadic_left_refine (n j : nat) : dyadic_left n.+1 (2 ^ n.+1 + j.*2)%N = dyadic_left n j.
Proof.
have hp : (2 ^+ n : R) != 0 by rewrite expf_neq0 // pnatr_eq0.
rewrite /dyadic_left /dyadic_step natrD natrX -muln2 natrM exprS -[n.+1]addn1 natrD.
by field; rewrite hp.
Qed.

(** Source for [dyadic_cell_refine]: every cell of rank n is the union of
    two cells of rank n+1, Federer 2.5.17, p. 111. *)
Lemma dyadic_cell_refine (n j : nat) (x : R) :
  dyadic_cell n j x ->
  dyadic_cell n.+1 (2 ^ n.+1 + j.*2)%N x \/ dyadic_cell n.+1 (2 ^ n.+1 + j.*2).+1 x.
Proof.
rewrite /dyadic_cell /= !in_itv /= dyadic_left_succ_index dyadic_left_refine.
rewrite -(dyadic_step_succ n) => /andP[h1 h2].
case: (ltP x (dyadic_left n j + dyadic_step n.+1))=> h.
- by left; rewrite h1.
- by right; rewrite -addrA h2.
Qed.

(** Source for [dyadic_cell_refine_sub]: the two cells of rank n+1 are
    contained in the cell of rank n, Federer 2.5.17, p. 111. *)
Lemma dyadic_cell_refine_sub (n j : nat) (b : bool) :
  dyadic_cell n.+1 (2 ^ n.+1 + j.*2 + b)%N `<=` dyadic_cell n j.
Proof.
have hs := dyadic_step_gt0 n.+1.
move=> x; rewrite /dyadic_cell /= !in_itv /= -(dyadic_step_succ n).
case: b; rewrite ?addn1 ?addn0 ?dyadic_left_succ_index dyadic_left_refine => /andP[h1 h2];
  apply/andP; split; lra.
Qed.

(** Source for [dyadic_cell_disjoint]: cells of the same rank with
    different indices are disjoint, Federer 2.5.17, p. 111. *)
Lemma dyadic_cell_disjoint (n j k : nat) (x : R) :
  (j < k)%N -> dyadic_cell n j x -> dyadic_cell n k x -> False.
Proof.
move=> hjk; rewrite /dyadic_cell /= !in_itv /= => /andP[_ h2] /andP[h3 _].
have hs := dyadic_step_gt0 n.
have hle : dyadic_left n j + dyadic_step n <= dyadic_left n k.
  rewrite -dyadic_left_succ_index /dyadic_left lerD2l ler_pM2r // ler_nat; exact: hjk.
lra.
Qed.

(** Source for [dyadic_cell_locate]: every x with -n <= x < n lies in the
    cell of rank n and index floor((x + n) 2^n), whose index is below
    2n 2^n, Federer 2.5.17, p. 111. *)
Lemma dyadic_cell_locate (n : nat) (x : R) :
  - n%:R <= x -> x < n%:R -> exists j, (j < dyadic_bound n)%N /\ dyadic_cell n j x.
Proof.
move=> h1 h2.
have hp : (0 : R) < 2 ^+ n by rewrite exprn_gt0.
have h0 : 0 <= (x + n%:R) * 2 ^+ n by apply: mulr_ge0; [lra | exact: ltW].
have /andP[ht1 ht2] := truncn_itv h0.
exists (Num.truncn ((x + n%:R) * 2 ^+ n)); split.
- rewrite -(@ltr_nat R); apply: le_lt_trans ht1 _.
  rewrite /dyadic_bound natrM natrX -muln2 natrM (ltr_pM2r hp); lra.
- have hinv : 0 < (2 ^+ n : R)^-1 by rewrite invr_gt0.
  rewrite /dyadic_cell /= in_itv /= /dyadic_left /dyadic_step; apply/andP; split.
  + by have := ler_wpM2r (ltW hinv) ht1; rewrite mulfK ?gt_eqF // => hh; lra.
  + rewrite -(ltr_pM2r hinv) mulfK ?gt_eqF // -addn1 natrD mulrDl mul1r in ht2.
    by lra.
Qed.

(** Source for [half_open_interval_measure]: a Borel regular measure with
    mu{x : a <= x <= b} = b - a gives the same value to
    {x : a <= x < b}, Federer 2.5.17, p. 111. *)
Lemma half_open_interval_measure (mu : set R -> \bar R) (a b : R) :
  is_measure mu -> is_borel_regular_measure mu ->
  (forall c d : R, c <= d -> mu `[c, d] = (d - c)%:E) -> a <= b -> mu `[a, b[ = (b - a)%:E.
Proof.
move=> hm hr hseg hab.
have hb : measure_measurable mu [set b].
  apply: (borel_regular_borel_measurable hm hr); apply: closed_borel_set.
  have -> : [set b] = `[b, b].
    apply/seteqP; split=> y; rewrite /= in_itv /=; first by move=> ->; rewrite lexx.
    by move=> /andP[h1 h2]; apply/le_anti; rewrite h2 h1.
  exact: segment_closed_real.
have hsplit := hb `[a, b].
have hpt : `[a, b] `&` [set b] = `[b, b].
  apply/seteqP; split=> y; rewrite /= !in_itv /=.
  - by move=> [/andP[_ _] ->]; rewrite lexx.
  - move=> /andP[h1 h2]; have hy : y = b by apply/le_anti; rewrite h2 h1.
    by split; [rewrite hy hab lexx | exact: hy].
have hho : `[a, b] `\` [set b] = `[a, b[.
  apply/seteqP; split=> y; rewrite /= !in_itv /=.
  - by move=> [/andP[h1 h2] hne]; rewrite h1 lt_neqAle h2 andbT; apply/eqP.
  - by move=> /andP[h1 h2]; split; [rewrite h1 ltW | move=> hy; move: h2; rewrite hy ltxx].
rewrite hpt hho (hseg b b (lexx b)) subrr add0e in hsplit.
by rewrite -hsplit hseg.
Qed.

Variables mu1 mu2 : set R -> \bar R.
Hypothesis hm1 : is_measure mu1.
Hypothesis hm2 : is_measure mu2.
Hypothesis hr1 : is_borel_regular_measure mu1.
Hypothesis hr2 : is_borel_regular_measure mu2.
Hypothesis hs1 : forall a b : R, a <= b -> mu1 `[a, b] = (b - a)%:E.
Hypothesis hs2 : forall a b : R, a <= b -> mu2 `[a, b] = (b - a)%:E.

(** Source for [dyadic_cell_measurable]: the cells are measurable for a
    Borel regular measure, Federer 2.2.3, p. 61, used in 2.5.17, p. 111. *)
Lemma dyadic_cell_measurable (mu : set R -> \bar R) (n j : nat) :
  is_measure mu -> is_borel_regular_measure mu -> measure_measurable mu (dyadic_cell n j).
Proof.
move=> hm hr.
have -> : dyadic_cell n j = `[dyadic_left n j, dyadic_left n j + dyadic_step n]
    `\` [set dyadic_left n j + dyadic_step n].
  apply/seteqP; split=> y; rewrite /dyadic_cell /= !in_itv /=.
  - by move=> /andP[h1 h2]; split; [rewrite h1 ltW | move=> hy; move: h2; rewrite hy ltxx].
  - by move=> [/andP[h1 h2] hne]; rewrite h1 lt_neqAle h2 andbT; apply/eqP.
apply: (measure_measurable_difference hm).
- by apply: (borel_regular_borel_measurable hm hr); apply: closed_borel_set; exact: segment_closed_real.
- apply: (borel_regular_borel_measurable hm hr); apply: closed_borel_set.
  set c := dyadic_left n j + dyadic_step n.
  have -> : [set c] = `[c, c].
    apply/seteqP; split=> y; rewrite /= in_itv /=; first by move=> ->; rewrite lexx.
    by move=> /andP[h1 h2]; apply/le_anti; rewrite h2 h1.
  exact: segment_closed_real.
Qed.

(** Source for [dyadic_union_measurable]: the finite unions of cells are
    measurable, Federer 2.1.3, p. 55, used in 2.5.17, p. 111. *)
Lemma dyadic_union_measurable (mu : set R -> \bar R) (V : set R) (n k : nat) :
  is_measure mu -> is_borel_regular_measure mu -> measure_measurable mu (dyadic_union V n k).
Proof.
move=> hm hr; elim: k=> [|k ih].
  have -> : dyadic_union V n 0 = set0 by apply/seteqP; split=> x // [j []].
  apply: (borel_regular_borel_measurable hm hr); apply: open_borel_set; exact: open0.
case: (pselect (dyadic_cell n k `<=` V))=> hk.
- have -> : dyadic_union V n k.+1 = dyadic_cell n k `|` dyadic_union V n k.
    apply/seteqP; split=> x.
    + move=> [j [hj hjV hx]]; move: hj; rewrite ltnS leq_eqVlt => /orP[/eqP hjk|hjk].
        by left; rewrite -hjk.
      by right; exists j.
    + by move=> [hx|[j [hj hjV hx]]]; [exists k | exists j; split=> //; exact: ltnW].
  exact: (measure_measurable_union hm (dyadic_cell_measurable n k hm hr) ih).
- have -> : dyadic_union V n k.+1 = dyadic_union V n k.
    apply/seteqP; split=> x.
    + move=> [j [hj hjV hx]]; move: hj; rewrite ltnS leq_eqVlt => /orP[/eqP hjk|hjk].
        by exfalso; apply: hk; rewrite -hjk.
      by exists j.
    + by move=> [j [hj hjV hx]]; exists j; split=> //; exact: ltnW.
  exact: ih.
Qed.

(** Source for [dyadic_union_agree]: the two measures agree on the finite
    unions of cells, by finite additivity, Federer 2.1.3, p. 55, used in
    2.5.17, p. 111. *)
Lemma dyadic_union_agree (V : set R) (n k : nat) : mu1 (dyadic_union V n k) = mu2 (dyadic_union V n k).
Proof.
have hcell : forall j, mu1 (dyadic_cell n j) = mu2 (dyadic_cell n j).
  move=> j; have hs := ltW (dyadic_step_gt0 n).
  have hle : dyadic_left n j <= dyadic_left n j + dyadic_step n by rewrite lerDl.
  by rewrite /dyadic_cell (half_open_interval_measure hm1 hr1 hs1 hle)
    (half_open_interval_measure hm2 hr2 hs2 hle).
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
  rewrite heq (measure_disjoint_union (dyadic_cell_measurable n k hm1 hr1) hdis).
  by rewrite (measure_disjoint_union (dyadic_cell_measurable n k hm2 hr2) hdis) hcell ih.
- have -> : dyadic_union V n k.+1 = dyadic_union V n k.
    apply/seteqP; split=> x.
    + move=> [j [hj hjV hx]]; move: hj; rewrite ltnS leq_eqVlt => /orP[/eqP hjk|hjk].
        by exfalso; apply: hk; rewrite -hjk.
      by exists j.
    + by move=> [j [hj hjV hx]]; exists j; split=> //; exact: ltnW.
  exact: ih.
Qed.

(** Source for [dyadic_union_monotone]: the unions W_n of the cells of
    rank n increase with n, Federer 2.5.17, p. 111. *)
Lemma dyadic_union_monotone (V : set R) (n : nat) :
  dyadic_union V n (dyadic_bound n) `<=` dyadic_union V n.+1 (dyadic_bound n.+1).
Proof.
move=> x [j [hj hjV hx]].
have hb : forall b : bool, (2 ^ n.+1 + j.*2 + b < dyadic_bound n.+1)%N.
  move=> b; move: hj; rewrite /dyadic_bound expnS.
  by case: b; rewrite /=; nia.
case: (dyadic_cell_refine hx)=> hx'.
- exists (2 ^ n.+1 + j.*2)%N; split=> //.
    by have := hb false; rewrite addn0.
  by apply: subset_trans hjV; have := @dyadic_cell_refine_sub n j false; rewrite addn0.
- exists (2 ^ n.+1 + j.*2).+1%N; split=> //.
    by have := hb true; rewrite addn1.
  by apply: subset_trans hjV; have := @dyadic_cell_refine_sub n j true; rewrite addn1.
Qed.

(** Source for [dyadic_union_monotone_le]: the unions increase along
    n <= m, Federer 2.5.17, p. 111. *)
Lemma dyadic_union_monotone_le (V : set R) (n m : nat) :
  (n <= m)%N -> dyadic_union V n (dyadic_bound n) `<=` dyadic_union V m (dyadic_bound m).
Proof.
elim: m=> [|m ih]; first by rewrite leqn0 => /eqP ->.
rewrite leq_eqVlt => /orP[/eqP ->//|]; rewrite ltnS => hnm.
exact: (subset_trans (ih hnm) (@dyadic_union_monotone V m)).
Qed.

(** Source for [dyadic_union_open]: an open set is the union of the sets
    W_n, Federer 2.5.17, p. 111. *)
Lemma dyadic_union_open (V : set R) :
  open V -> \bigcup_n dyadic_union V n (dyadic_bound n) = V.
Proof.
move=> hV; apply/seteqP; split=> x.
  by move=> [n _ [j [_ hjV hx]]]; exact: hjV.
move=> hx.
have hn : nbhs x V by apply: open_nbhs_nbhs; split.
have [e he hball] := (nbhs_ballP x V).1 hn.
have he' : 0 < e := he.
have [n1 hn1] := real_reciprocal_below he'.
have /andP[_ hn0] := truncn_itv (normr_ge0 x).
set n0 := (Num.truncn `|x|).+1 in hn0.
pose n := maxn n0 n1.
have hxn : `|x| < n%:R.
  apply: lt_le_trans hn0 _; rewrite ler_nat; exact: leq_maxl.
have hstep : dyadic_step n < e.
  apply: le_lt_trans hn1; rewrite /dyadic_step lef_pV2 ?posrE ?ltr0n ?exprn_gt0 //.
  rewrite -natrX ler_nat; apply: (@leq_trans n.+1); first by rewrite ltnS leq_maxr.
  exact: ltn_expl.
have /andP[hxl hxr] : - n%:R < x < n%:R by rewrite -ltr_norml.
have [j [hj hjx]] := dyadic_cell_locate (ltW hxl) hxr.
exists n=> //; exists j; split=> //.
move=> y hy; apply: hball; rewrite /ball /=.
move: hjx hy; rewrite /dyadic_cell /= !in_itv /= => /andP[h1 h2] /andP[h3 h4].
by rewrite ltr_norml; apply/andP; split; lra.
Qed.

(** Source for [borel_regular_interval_open_agree]: two Borel regular
    measures giving every segment its length agree on open sets, Federer
    2.5.17, p. 111. *)
Lemma borel_regular_interval_open_agree (V : set R) : open V -> mu1 V = mu2 V.
Proof.
move=> hV; rewrite -(dyadic_union_open hV).
have hmeas1 := fun n => dyadic_union_measurable V n (dyadic_bound n) hm1 hr1.
have hmeas2 := fun n => dyadic_union_measurable V n (dyadic_bound n) hm2 hr2.
have hmono : forall n m, (n <= m)%N -> dyadic_union V n (dyadic_bound n) `<=` dyadic_union V m (dyadic_bound m).
  by move=> n m hnm; exact: (@dyadic_union_monotone_le V n m hnm).
have h1 := measure_continuity_below hm1 hmeas1 hmono.
have h2 := measure_continuity_below hm2 hmeas2 hmono.
have heq : (fun n => mu1 (dyadic_union V n (dyadic_bound n)))
    = (fun n => mu2 (dyadic_union V n (dyadic_bound n))).
  by apply/funext=> n; exact: dyadic_union_agree.
rewrite heq in h1.
exact: (extended_order_limit_unique h1.2 h2.2).
Qed.

(** Source for [borel_regular_interval_le]: mu2 <= mu1 for two Borel
    regular measures giving every segment its length, by the open outer
    approximation of 2.2.2 and 2.2.3, Federer 2.5.17, p. 111. *)
Lemma borel_regular_interval_le (A : set R) : (mu2 A <= mu1 A)%E.
Proof.
have [B [hAB [hB hmB]]] := borel_regular_cover hr1 A.
rewrite hmB.
have hBm := borel_regular_borel_measurable hm1 hr1 hB.
pose W := fun n : nat => `](- n%:R : R), n%:R[.
have hW : forall n, open (W n) /\ (mu1 (W n) < +oo)%E.
  move=> n; split; first by apply: interval_open.
  apply: le_lt_trans (measure_mono hm1 (_ : W n `<=` `[- n%:R, n%:R])) _.
    by move=> y; rewrite /W /= !in_itv /= => /andP[h1 h2]; rewrite !ltW.
  by rewrite hs1 ?ltry //; have := ler0n R n; lra.
have hcover : B `<=` \bigcup_n W n.
  move=> y _; have /andP[_ hy] := truncn_itv (normr_ge0 y).
  exists (Num.truncn `|y|).+1=> //; move: hy; rewrite /W /= in_itv /= ltr_norml.
  by [].
apply/lee_addgt0Pr=> e he.
have [O [hO [hBO hOB]]] := borel_regular_open_approximation hm1 hr1 hBm hW hcover he.
apply: le_trans (measure_mono hm2 (subset_trans hAB hBO)) _.
rewrite -(borel_regular_interval_open_agree hO).
have hsplit := hBm O.
have hOB' : O `&` B = B by apply/seteqP; split=> y; [move=> []|move=> hy; split=> //; exact: hBO].
rewrite hsplit hOB'; exact: leeD (lexx _) (ltW hOB).
Qed.

End Characterisation.

(** Source for [borel_regular_interval_unique]: two Borel regular
    measures over R giving every segment {x : a <= x <= b} the value
    b - a are equal, Federer 2.5.17, p. 111. *)
Theorem borel_regular_interval_unique (R : realType) (mu1 mu2 : set R -> \bar R) :
  is_measure mu1 -> is_measure mu2 -> is_borel_regular_measure mu1 -> is_borel_regular_measure mu2 ->
  (forall a b : R, a <= b -> mu1 `[a, b] = (b - a)%:E) ->
  (forall a b : R, a <= b -> mu2 `[a, b] = (b - a)%:E) -> mu1 = mu2.
Proof.
move=> hm1 hm2 hr1 hr2 hs1 hs2; apply/funext=> A; apply/le_anti/andP; split.
- exact: borel_regular_interval_le hm2 hm1 hr2 hr1 hs2 hs1 A.
- exact: borel_regular_interval_le hm1 hm2 hr1 hr2 hs1 hs2 A.
Qed.

(** Source for [lebesgue_line_measure_characterisation]: the one
    dimensional Lebesgue measure L^1 of Federer 2.5.17, p. 111, is the
    Borel regular measure characterised by b - a = L^1{x : a <= x <= b};
    it is the K(R) regular measure representing the Riemann integral. *)
Theorem lebesgue_line_measure_characterisation (R : realType) :
  exists L1 : set R -> \bar R,
    is_measure L1 /\ is_borel_regular_measure L1 /\ is_radon_measure L1 /\
    is_function_lattice_regular (@compactly_supported_continuous_functions R R) L1 /\
    is_real_integral_functional L1 (@compactly_supported_continuous_functions R R)
      (induced_daniell (fun x : R => x)) /\
    (forall a b : R, a <= b -> L1 `[a, b] = (b - a)%:E) /\
    forall mu : set R -> \bar R, is_measure mu -> is_borel_regular_measure mu ->
      (forall a b : R, a <= b -> mu `[a, b] = (b - a)%:E) -> mu = L1.
Proof.
have [L1 [hm [hrad [hbor [hr [hi [_ hseg]]]]]]] := @lebesgue_line_measure_borel_regular R.
exists L1; do 6!(split=> //).
by move=> mu hmu hbmu hsmu; exact: borel_regular_interval_unique hmu hm hbmu hbor hsmu hseg.
Qed.
