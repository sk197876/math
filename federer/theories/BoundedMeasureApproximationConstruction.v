(** Private existence proof for the bounded finite-measure approximants in
    Federer (1969), 2.4.16, p. 90. Source context and the
    restriction-versus-clipping variation are recorded in
    BoundedMeasureApproximationUP.v. The countable measurable cover is
    replaced by finite prefix unions; each prefix is intersected with
    {|f|<=n+1}. All points, including null pieces, are retained eventually. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionUP PartialFunctionBasic
  MeasureUP MeasureBasic MeasureSplit MeasureFiniteClosure MeasureGauge
  MeasurableFunctionUP MeasurableNormSuperlevels MeasurableNormedBasic
  MeasurableTotalPiecewise CountablyMeasurableUP CountablyMeasurableSequences BoundedMeasureApproximationUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [bounded_measure_approximation_exists]: existence
    of the sequence in Federer 2.4.16, p. 90, with the
    stronger eventual restriction property described in the specification. *)
Theorem bounded_measure_approximation_exists (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : X -> real_norm_metric_space (scalar_absolute_value_norm R)) :
  is_countably_measure_measurable_function mu (0%R : real_norm_metric_space (scalar_absolute_value_norm R))
    (partial_function_total f) -> exists g, is_bounded_measure_approximation mu f g.
Proof.
move=> hf; have hmeas := countably_measurable_function_measurable hf.
have [C [hcover hC]] := (countably_measurable_sequence_iff hm _).1
  (countably_measurable_function_locus hf).
pose F n := \bigcup_(i in [set i | (i < n)%N]) C i.
have hF0 : F 0%N=set0 by apply/seteqP; split=> x // [i hi _]; move: hi; rewrite /= ltn0.
have hFS n : F n.+1 = F n `|` C n.
  apply/seteqP; split=> x.
  - move=> [i hi hix]; move: hi; rewrite /= ltnS leq_eqVlt=> /orP[/eqP he|hin].
    + right; by rewrite -he.
    + left; by exists i.
  - move=> [[i hi hix]|hx].
    + exists i=> //; exact: ltn_trans hi (ltnSn n).
    + exists n=> //; exact: ltnSn.
have hFm n : measure_measurable mu (F n).
  elim: n=> [|n ih]; first by rewrite hF0; exact: measure_measurable_empty hm.
  rewrite hFS; exact: (@measure_measurable_union R X mu hm _ _ ih (hC n).1).
have hFf n : mu (F n) < +oo.
  elim: n=> [|n ih]; first by rewrite hF0 (measure_empty hm); exact: ltry.
  rewrite hFS; apply: le_lt_trans (@measure_binary_cover R X mu hm _ _ _ (fun x hx => hx)) _.
  exact: (lte_add_pinfty ih (hC n).2).
have hFmon n m : (n <= m)%N -> F n `<=` F m.
  move=> hnm x [i hin hix]; exists i=> //; exact: leq_trans hin hnm.
pose D n := F n `\` partial_norm_superlevel (fun y : R => `|y|%R) (partial_function_total f) (n.+1%:R)%:E.
have hDm n : measure_measurable mu (D n).
  exact: (@measure_measurable_difference R X mu hm _ _ (hFm n)
    (@measurable_norm_superlevel R X R^o _ (scalar_absolute_value_norm R) mu hm _ hmeas n.+1%:R)).
have hDb n x : D n x -> (`|f x| <= n.+1%:R)%R.
  move=> [_ hn]; rewrite leNgt; apply/negP=> hx; apply: hn.
  exists (f x); split=> //; by rewrite lte_fin.
have hDmon n m : (n <= m)%N -> D n `<=` D m.
  move=> hnm x hd; split; first exact: (hFmon n m hnm x hd.1).
  move=> [y [hy hmy]].
  have hfn : (`|f x| <= m.+1%:R)%R.
    apply: le_trans (hDb n x hd) _; by rewrite ler_nat.
  by move: hmy; rewrite /= -(hy : f x=y) lte_fin ltNge hfn.
pose g n x := (if pselect (D n x) then f x else 0%R : real_norm_metric_space (scalar_absolute_value_norm R)).
have hg0 n x : ~ D n x -> g n x=0%R by move=> hx; rewrite /g; case: pselect.
have hgon n x : D n x -> g n x=f x by move=> hx; rewrite /g; case: pselect.
exists g; constructor.
- move=> n; apply: (@measurable_total_piecewise R X _ mu hm (D n) f (fun _ => 0%R) (hDm n) hmeas).
  exact: (@measurable_normed_total_constant R X R^o _ (scalar_absolute_value_norm R) mu hm 0%R).1.
- move=> n; exists (D n); split=> //; split.
  + apply: le_lt_trans _ (hFf n); apply: (@measure_mono R X mu hm)=> x [hx _]; exact hx.
  split; first exact: hg0.
  move=> x; rewrite /g; case: pselect=> hx.
  + exact: hDb n x hx.
  + by rewrite normr0 ler0n.
- move=> n x; rewrite /g; case: pselect=> hx; [by right|by left].
- move=> n x; have [hx|hx] := pselect (D n x).
  + by rewrite (hgon n x hx) (hgon n.+1 x (hDmon n n.+1 (leqnSn n) x hx)).
  + rewrite (hg0 n x hx) normr0; exact: normr_ge0.
- move=> x; have [hfx|hfx] := eqVneq (f x) 0%R.
  + exists 0%N=> n _; by rewrite /g hfx; case: pselect.
  have hloc : partial_function_nonzero_locus (0%R : real_norm_metric_space (scalar_absolute_value_norm R))
      (partial_function_total f) x.
    exists (f x); split=> //; by apply/eqP.
  rewrite hcover in hloc; have [i _ hix] := hloc.
  pose k := Num.bound `|f x|%R.
  have hk : (`|f x| < k%:R)%R by apply: archi_boundP; exact: normr_ge0.
  exists (maxn i.+1 k)=> n hkn; apply: hgon; split.
  + exists i=> //; exact: leq_trans (leq_maxl _ _) hkn.
  + move=> [y [hy hny]].
    have hn : (`|f x| <= n.+1%:R)%R.
      apply: le_trans (ltW hk) _; rewrite ler_nat.
      exact: leq_trans (leq_trans (leq_maxr _ _) hkn) (leqnSn n).
    by move: hny; rewrite /= -(hy : f x=y) lte_fin ltNge hn.
Qed.
