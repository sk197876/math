(** Federer (1969), 2.5.17, p. 111: if g(x) = x for all x in R, then mu is
    the Riemann integral, and psi^+ is the 1 dimensional Lebesgue measure
    L^1 over R; this is the Borel regular measure characterised by the
    property that b - a = L^1{x : a <= x <= b} whenever -oo < a < b < oo.
    The K(R) regular measure of the Riemann integral is shown to satisfy
    L^1{x : a < x < b} = L^1{x : a <= x <= b} = b - a. The upper bound comes
    from condition (2) of p. 111; the lower bound uses the
    greatest-lower-bound clause of the envelope of 2.5.2 and a Dini type
    argument on compact segments. Borel regularity and the uniqueness clause
    are not recorded here. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets reals
  constructive_ereal topology normedtype.
From mathcomp Require Import ring lra.
From Federer Require Import RealMetricBackground ExtendedRealBoundsUP ExtendedRealBounds
  CurveVariationUP CurveArcLength FunctionLatticeUP FunctionLatticeRegularityUP
  MonotoneDaniellIntegralUP RegularDaniellEnvelope DaniellCoverUP RealIntegralFunctionalUP
  MeasureUP MeasureBasic CompactSupportFunctionUP CompactSupportFunctionLattice StieltjesSums
  StieltjesIntegral StieltjesDaniellIntegral StieltjesMonotone.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [compact_increasing_eventually_above]: supporting Dini
    type estimate, Federer 2.5.17, p. 111: an increasing sequence of
    continuous functions whose limit exceeds every number below c on a
    compact set eventually exceeds c - e there. The proof is the open
    cover argument of 2.5.13, p. 107. *)
Lemma compact_increasing_eventually_above (R : realType) (K : set R) (h : nat -> R -> R) (c e : R) :
  compact K -> (forall n, continuous (h n)) ->
  (forall n m, (n <= m)%N -> forall x, h n x <= h m x) ->
  (forall x, K x -> forall r, r < c -> exists n, r < h n x) -> 0 < e ->
  exists N, forall n, (N <= n)%N -> forall x, K x -> c - e < h n x.
Proof.
move=> hK hc hmon hlim he.
pose U := fun n : nat => interior [set x | c - e < h n x].
have hU : forall n, open (U n) by move=> n; exact: open_interior.
have hcov : cover_compact K by rewrite -compact_cover.
have hce : c - e < c by lra.
have hsub : K `<=` cover [set: nat] U.
  move=> x hx; have [n hn] := hlim x hx (c - e) hce; exists n=> //.
  have hd : 0 < h n x - (c - e) by lra.
  have hb : nbhs x (h n @^-1` ball (h n x) (h n x - (c - e))) :=
    hc n x _ (nbhsx_ballx (h n x) (h n x - (c - e)) hd).
  suff : nbhs x [set y | c - e < h n y] by [].
  apply: filterS hb=> y /=; rewrite /ball /= ltr_norml=> /andP[h1 h2].
  by rewrite /=; lra.
have [D _ hD] := hcov nat [set: nat] U (fun n _ => hU n) hsub.
pose N := \max_(i : D) val i.
exists N=> n hNn x hx.
have [m hmD hxm0] := hD x hx.
have hxm : c - e < h m x := interior_subset hxm0.
have hmD' : m \in D := hmD.
have hmN : (m <= N)%N := leq_bigmax (F := fun i : D => val i) [` hmD']%fset.
exact (lt_le_trans hxm (hmon m n (leq_trans hmN hNn) x)).
Qed.

Section LebesgueLine.
Variable R : realType.
Local Notation KR := (@compactly_supported_continuous_functions R R).
Local Notation id_fun := (fun x : R => x).
Let hmono : forall x y : R, x <= y -> id_fun x <= id_fun y := fun x y h => h.
Let hg : curve_locally_finite_variation (id_fun : R -> real_line_metric R) :=
  monotone_locally_finite_variation hmono.
Local Notation mu := (induced_daniell id_fun).

(** Source for [riemann_integral_interval_lower]: for a sequence
    suiting {x : a < x < b} in K(R), the cost sup mu(f_n) of the Riemann
    integral is at least b - a, the lower estimate of
    L^1{x : a < x < b} in Federer 2.5.17, p. 111. *)
Lemma riemann_integral_interval_lower (a b : R) (f : nat -> R -> R) (c : \bar R) :
  a <= b -> is_daniell_suiting_sequence KR `]a, b[ f -> is_daniell_sequence_cost mu f c ->
  ((b - a)%:E <= c)%E.
Proof.
move=> hab [hfpos [hfmon hflim]] hcost.
have hL := @compactly_supported_continuous_functions_lattice R R.
have hMD := induced_daniell_monotone_daniell hg hmono.
have hc0 : forall n, ((mu (f n))%:E <= c)%E.
  by move=> n; exact (extended_real_supremum_upper hcost (ex_intro _ n erefl)).
have hmu0 : forall n, 0 <= mu (f n).
  by move=> n; exact (induced_daniell_nonnegative hg hmono (hfpos n).1 (hfpos n).2).
apply/lee_subgt0Pr=> e he.
case: (lerP (b - a) (e / 2))=> [hsmall|hbig].
  apply: le_trans (hc0 0%N); rewrite lee_fin.
  by have := hmu0 0%N; lra.
pose d := e / 4.
pose eps := e / (2 * (b - a)).
have hba : 0 < b - a by lra.
have heps : 0 < eps by rewrite /eps divr_gt0 // mulr_gt0 ?ltr0n.
have heps1 : eps * (b - a) = e / 2 by rewrite /eps; field; lra.
pose h := fun n x => Order.min (f n x) 1.
have hh : forall n, KR (h n) by move=> n; exact (function_lattice_truncation hL ler01 (hfpos n).1).
have hh0 : forall n x, 0 <= h n x by move=> n x; rewrite le_min ler01 andbT; exact: (hfpos n).2.
have hhf : forall n x, h n x <= f n x by move=> n x; rewrite ge_min lexx.
have hhmon : forall n m, (n <= m)%N -> forall x, h n x <= h m x.
  by move=> n m hnm x; rewrite /h le_min ge_min (hfmon n m hnm x) /= ge_min lexx orbT.
have hhlim : forall x, `[a + d, b - d] x -> forall r, r < 1 -> exists n, r < h n x.
  move=> x; rewrite /= in_itv /= => /andP[h1 h2] r hr.
  have hx : `]a, b[ x by rewrite /= in_itv /=; apply/andP; split; rewrite /d in h1 h2; lra.
  have [n hn] := hflim x hx r hr.
  by exists n; rewrite lt_min hn hr.
have [N hN] := compact_increasing_eventually_above (@segment_compact R (a + d) (b - d))
  (fun n => KR_continuous (hh n)) hhmon hhlim heps.
have hbound : (1 - eps) * (b - a - 2 * d) <= mu (f N).
  have hle : mu (h N) <= mu (f N).
    exact (monotone_daniell_integral_monotone hMD (hh N) (hfpos N).1 (hhf N)).
  apply: le_trans _ hle.
  have [M0 [hM00 hz0]] := compact_support_bound (hh N).
  have /andP[ha1 ha2] : - `|a| <= a <= `|a| by rewrite -ler_norml.
  have /andP[hb1 hb2] : - `|b| <= b <= `|b| by rewrite -ler_norml.
  pose M := M0 + `|a| + `|b| + 1.
  have hM0 : 0 <= M by rewrite /M; have := normr_ge0 a; have := normr_ge0 b; lra.
  have hzM : forall x, h N x <> 0 -> `|x| < M.
    by move=> x hx; have := hz0 x hx; rewrite /M; have := normr_ge0 a; have := normr_ge0 b; lra.
  rewrite -(induced_daniell_eq hg (KR_continuous (hh N)) (compact_support_bound (hh N)) hM0 hzM).
  have hcont := KR_continuous (hh N).
  have hMa : - M <= a + d by rewrite /M /d; have := normr_ge0 b; have := normr_ge0 M0; lra.
  have hab' : a + d <= b - d by rewrite /d; lra.
  have hbM : b - d <= M by rewrite /M /d; have := normr_ge0 a; lra.
  have hMb : - M <= b - d by lra.
  rewrite -(stieltjes_integral_cat hg hcont hMb hbM) -(stieltjes_integral_cat hg hcont hMa hab').
  have h1 := stieltjes_integral_lower_bound hg hmono (m := 0) hcont hMa (fun x _ => hh0 N x).
  have h3 := stieltjes_integral_lower_bound hg hmono (m := 0) hcont hbM (fun x _ => hh0 N x).
  have h2 := stieltjes_integral_lower_bound hg hmono (m := 1 - eps) hcont hab'
    (fun x hx => ltW (hN N (leqnn N) x hx)).
  move: h1 h2 h3; rewrite !mul0r /= => h1 h2 h3.
  have heq : (1 - eps) * (b - d - (a + d)) = (1 - eps) * (b - a - 2 * d) by ring.
  by lra.
apply: le_trans (hc0 N); rewrite lee_fin; apply: le_trans _ hbound.
have hepsge0 : 0 <= eps by exact: ltW.
have hd : d = e / 4 by [].
have hmono' : eps * (b - a - 2 * d) <= eps * (b - a) by apply: ler_wpM2l=> //; lra.
by rewrite mulrBl mul1r; lra.
Qed.

(** Source for [lebesgue_line_measure_exists]: the Lebesgue measure L^1
    over R of Federer 2.5.17, p. 111: the K(R) regular measure of the
    Riemann integral, with L^1{x : a < x < b} = L^1{x : a <= x <= b}
    = b - a whenever a <= b. *)
Theorem lebesgue_line_measure_exists :
  exists L1 : set R -> \bar R, is_measure L1 /\ is_function_lattice_regular KR L1 /\
    is_real_integral_functional L1 KR mu /\
    (forall a b : R, a <= b -> L1 `]a, b[ = (b - a)%:E) /\
    (forall a b : R, a <= b -> L1 `[a, b] = (b - a)%:E).
Proof.
have [psi [hm [hr [hi hbd]]]] := stieltjes_monotone_representation hg hmono.
have hL := @compactly_supported_continuous_functions_lattice R R.
have henv := regular_representing_measure_envelope hL hm hi hr.
exists psi; split=> //; split=> //; split=> //.
have hopen : forall a b, a <= b -> psi `]a, b[ = (b - a)%:E.
  move=> a b hab; apply/le_anti/andP; split; first exact: hbd.
  apply: (daniell_cover_greatest henv)=> f c hf hc.
  exact (riemann_integral_interval_lower hab hf hc).
split=> // a b hab; apply/le_anti/andP; split.
- apply/lee_addgt0Pr=> e he.
  have hsub : `[a, b] `<=` `]a - e / 2, b + e / 2[.
    by move=> x; rewrite /= !in_itv /= => /andP[h1 h2]; apply/andP; split; lra.
  have hmm := measure_mono hm hsub.
  apply: le_trans hmm _.
  have hab' : a - e / 2 <= b + e / 2 by lra.
  by rewrite (hopen _ _ hab') -EFinD lee_fin; lra.
- rewrite -(hopen a b hab); apply: (measure_mono hm)=> x.
  by rewrite /= !in_itv /= => /andP[h1 h2]; apply/andP; split; exact: ltW.
Qed.

End LebesgueLine.
