(** Federer (1969), 2.7.13, printed pp. 130–131: the proof applies
    "Lebesgue's increasing convergence theorem" (2.4.7, p. 84) to total real
    valued functions, once on each coset g G^x for the measure beta and once
    on X for the measure gamma, and it uses that a nonnegative function with
    integral 0 vanishes almost everywhere ("T(w) and T(u) are gamma almost
    equal to 0", p. 130). This module states these facts for summable total
    real functions in the form needed there. The increasing hypotheses hold
    either everywhere or almost everywhere; in the second case the limit is
    a real function which is the pointwise limit almost everywhere, obtained
    from the bounded increasing limit of 2.5.7
    (TotalScalarLpIncreasingLimit.v). The local erratum has no entry for pp.
    84 or 130–131. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals
  constructive_ereal.
From Federer Require Import PartialFunctionUP PartialFunctionBasic PartialExtendedOrderLoci MeasureUP
  MeasureAlmostUP MeasureAlmostBasic MeasureIntegralUP MeasureIntegralUniqueness
  MeasureIntegralComparison MeasureIntegralAlmostEquality MeasureConullZeroIntegral
  MeasureNonnegativeZero ExtendedRealOrderLimit ExtendedIncreasingLimitSupremum SummableRealFunctionUP
  SummableRealArithmetic RealTotalIntegralLimits RealIncreasingIntegralLimit
  RealIntegralIncreasingContinuity MonotoneDaniellIntegralUP MonotoneDaniellIntegralSum TotalScalarLpUP
  TotalLoneSummability TotalScalarLpIncreasingLimit RealLowerLimitReplacement.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section SummableIncreasingLimits.
Variable R : realType.
Variable X : choiceType.
Variable mu : set X -> \bar R.
Hypothesis hm : is_measure mu.

(** Source for [constant_extended_increases]: a constant sequence
    increases to its value, the trivial case of the convergence
    convention of Federer 2.1.1, p. 51, used with 2.4.7, p. 84, in
    2.7.13, pp. 130–131. Supporting lemma. *)
Lemma constant_extended_increases (c : \bar R) : extended_increases_to (fun _ : nat => c) c.
Proof.
split=> [n m _|]; first exact: lexx.
by split=> [b hb|b hb]; exists 0%N=> n _.
Qed.

(** Source for [extended_increases_to_upper]: each term of an
    increasing sequence is at most its limit, Federer 2.1.1, p. 51,
    used with 2.4.7, p. 84, in 2.7.13, pp. 130–131. Supporting
    lemma. *)
Lemma extended_increases_to_upper (u : nat -> \bar R) l :
  extended_increases_to u l -> forall n, (u n <= l)%E.
Proof.
move=> [hmon [_ hup]] n; rewrite leNgt; apply/negP=> hlt.
have [N hN] := hup _ hlt.
have h := hN (maxn n N) (leq_maxr n N).
have h' := hmon n (maxn n N) (leq_maxl n N).
by have := lt_le_trans h h'; rewrite ltxx.
Qed.

(** Source for [summable_total_almost_equal_integral]: functions which
    agree almost everywhere have the same integral, since upper and
    lower functions are defined by inequalities holding almost
    everywhere, Federer 2.4.2, p. 81, with the convention of 2.3.1,
    p. 72; used in 2.7.13, pp. 130–131, for total real functions.
    Supporting lemma. *)
Lemma summable_total_almost_equal_integral (f g : X -> R) a :
  is_measure_integral mu (real_total_integrand f) a ->
  measure_almost_everywhere mu [set x | f x = g x] ->
  is_measure_integral mu (real_total_integrand g) a.
Proof.
move=> hi he; apply: (measure_integral_almost_equal hm hi).
apply: (measure_almost_everywhere_mono hm _ he)=> x hx.
exists (f x)%:E; split; first exact/real_total_integrand_graph.
by apply/real_total_integrand_graph; rewrite hx.
Qed.

(** Source for [summable_total_integral_le_almost]: monotonicity of the
    integral, Federer 2.4.4(5), p. 82, for total real functions with
    f <= g almost everywhere; used in 2.7.13, pp. 130–131. Supporting
    lemma. *)
Lemma summable_total_integral_le_almost (f g : X -> R) (a b : \bar R) :
  is_measure_integral mu (real_total_integrand f) a ->
  is_measure_integral mu (real_total_integrand g) b ->
  measure_almost_everywhere mu [set x | f x <= g x] -> (a <= b)%E.
Proof.
move=> hf hg hle; apply: (measure_integral_monotone hm hf hg).
apply: (measure_almost_everywhere_mono hm _ hle)=> x hx.
exists (f x)%:E, (g x)%:E; split; first exact/real_total_integrand_graph.
by split; [exact/real_total_integrand_graph|rewrite lee_fin].
Qed.

(** Source for [summable_total_nonnegative_zero_almost]: "hence T(w)
    and T(u) are gamma almost equal to 0", Federer 2.7.13, proof,
    p. 130: a function which is nonnegative almost everywhere and has
    integral 0 vanishes almost everywhere, since c phi{f > c} <=
    integral f d phi for c > 0 by 2.4.4(5), p. 82. Supporting lemma. *)
Lemma summable_total_nonnegative_zero_almost (f : X -> R) :
  is_measure_integral mu (real_total_integrand f) 0%E ->
  measure_almost_everywhere mu [set x | 0 <= f x] ->
  measure_almost_everywhere mu [set x | f x = 0].
Proof.
move=> hi hp.
have hp' : measure_almost_everywhere mu (partial_extended_nonnegative_locus (real_total_integrand f)).
  apply: (measure_almost_everywhere_mono hm _ hp)=> x hx.
  by exists (f x)%:E; split; [exact/real_total_integrand_graph|rewrite lee_fin].
have h := nonnegative_integral_zero_almost_equal hm hi hp'.
apply: (measure_almost_everywhere_mono hm _ h)=> x [z [hz h0]].
move/real_total_integrand_graph: hz; rewrite -h0 => he.
by case: he.
Qed.

(** Source for [summable_total_dominated_zero_integral]: "if u is the
    characteristic function of any set with alpha measure 0, there
    exists a w in Phi with w >= u and integral w d alpha = 0", Federer
    2.7.13, proof, p. 130: a function between 0 and a nonnegative
    function with integral 0 has integral 0. Supporting lemma. *)
Lemma summable_total_dominated_zero_integral (f h : X -> R) :
  is_measure_integral mu (real_total_integrand f) 0%E -> (forall x, 0 <= h x <= f x) ->
  is_measure_integral mu (real_total_integrand h) 0%E.
Proof.
move=> hi hb.
have hf0 : measure_almost_everywhere mu [set x | 0 <= f x].
  apply: (measure_almost_everywhere_mono hm _ (measure_almost_everywhere_true hm))=> x _.
  by have /andP [h0 hle] := hb x; exact: le_trans h0 hle.
have hz := summable_total_nonnegative_zero_almost hi hf0.
apply: (measure_almost_zero_integral hm).
apply: (measure_almost_everywhere_mono hm _ hz)=> x /= hx.
apply/real_total_integrand_graph; congr (_%:E).
have /andP [h0 hle] := hb x; apply/eqP; rewrite eq_le h0 andbT; by rewrite -hx.
Qed.

(** Source for [summable_increasing_limit_integral]: "Lebesgue's
    increasing convergence theorem implies T(u_h) increases to T(u)",
    Federer 2.7.13, proof, p. 130, with 2.4.7, p. 84: if summable
    functions f_n with integrals a_n increase everywhere to g and a_n
    converges to the real number b, then g is summable with integral
    b. Supporting lemma; the first function is subtracted to reduce
    to nonnegative functions. *)
Lemma summable_increasing_limit_integral (f : nat -> X -> R) (g : X -> R) (a : nat -> R) (b : R) :
  (forall n, is_measure_integral mu (real_total_integrand (f n)) (a n)%:E) ->
  real_functions_increase_to f g ->
  extended_order_limit (fun n => (a n)%:E) b%:E ->
  is_measure_integral mu (real_total_integrand g) b%:E.
Proof.
move=> hi hinc hlim.
pose v n x := f n x - f 0%N x.
pose w x := g x - f 0%N x.
have hv n : is_measure_integral mu (real_total_integrand (v n)) (a n - a 0%N)%:E.
  have hh := real_total_integral_subtract hm (hi n) (hi 0%N); exact: hh.
have hw := @real_nonnegative_increasing_integral_limit R X mu hm v w
  (fun n => (a n - a 0%N)%:E) (b - a 0%N)%:E.
have hw' : is_measure_integral mu (real_total_integrand w) (b - a 0%N)%:E.
  apply: hw=> //.
  - move=> n x; rewrite /v subr_ge0.
    by have := (hinc x).1 0%N n (leq0n n); rewrite lee_fin.
  - move=> n x; rewrite /v lerD2r.
    by have := (hinc x).1 n n.+1 (leqnSn n); rewrite lee_fin.
  - by move=> x; exact: (@real_order_limit_translate R (fun n => f n x) (g x) (- f 0%N x) (hinc x).2).
  - exact: (@real_order_limit_translate R a b (- a 0%N) hlim).
have hs := real_total_integral_add hm hw' (hi 0%N).
have -> : g = (fun x => w x + f 0%N x) by apply: funext=> x; rewrite /w subrK.
by rewrite subrK in hs.
Qed.

(** Source for [summable_almost_increasing_limit]: Lebesgue's
    increasing convergence theorem, Federer 2.4.7, p. 84, in the form
    used for T(u_h) in 2.7.13, proof, p. 130: if summable functions
    f_n with integrals a_n <= M increase almost everywhere, then some
    summable real function g is their limit almost everywhere, and a_n
    increases to the integral of g. Supporting theorem. The functions
    are first made nonnegative and increasing everywhere by
    subtracting f_0 off a null set; the bounded increasing limit of
    2.5.7 (bounded_increasing_lp_replacement) supplies g. *)
Theorem summable_almost_increasing_limit (f : nat -> X -> R) (a : nat -> R) (M : R) :
  (forall n, is_measure_integral mu (real_total_integrand (f n)) (a n)%:E) ->
  (forall n, measure_almost_everywhere mu [set x | f n x <= f n.+1 x]) ->
  (forall n, a n <= M) ->
  exists (g : X -> R) (b : R), [/\ is_measure_integral mu (real_total_integrand g) b%:E,
    extended_increases_to (fun n => (a n)%:E) b%:E &
    measure_almost_everywhere mu [set x | extended_increases_to (fun n => (f n x)%:E) (g x)%:E]].
Proof.
move=> hi hmon hM.
pose Y0 := [set x | forall n, f n x <= f n.+1 x].
have hY0 : measure_almost_everywhere mu Y0.
  have hall := @measure_almost_everywhere_countable R X [the choiceType of (nat : Type)]
    mu hm setT (fun n => [set x | f n x <= f n.+1 x]) (countableP setT) (fun n _ => hmon n).
  apply: (measure_almost_everywhere_mono hm _ hall)=> x hx n; exact: hx n I.
have hY0le x : Y0 x -> forall n m, (n <= m)%N -> f n x <= f m x.
  move=> hx; apply: (@homo_leq R (fun n => f n x) (fun v w => is_true (v <= w))).
  - by move=> v; exact: lexx.
  - by move=> w v z hvw hwz; exact: le_trans hvw hwz.
  - exact: hx.
pose h n x := if `[< Y0 x >] then f n x - f 0%N x else 0.
have hh0 n x : 0 <= h n x.
  rewrite /h; case: (asboolP (Y0 x))=> hx //.
  by rewrite subr_ge0; exact: hY0le hx 0%N n (leq0n n).
have hhle n m x : (n <= m)%N -> h n x <= h m x.
  move=> hnm; rewrite /h; case: (asboolP (Y0 x))=> hx //.
  by rewrite lerD2r; exact: hY0le hx n m hnm.
have hhi n : is_measure_integral mu (real_total_integrand (h n)) (a n - a 0%N)%:E.
  have hs := real_total_integral_subtract hm (hi n) (hi 0%N).
  apply: (summable_total_almost_equal_integral hs).
  apply: (measure_almost_everywhere_mono hm _ hY0)=> x hx.
  by rewrite /= /h (asboolT hx).
have hhlp n : total_scalar_lp mu 1%E (h n).
  by apply: (summable_real_total_lone hm); exists (a n - a 0%N); exact: hhi n.
have hnorm n : (total_scalar_lp_norm mu 1%E (h n) <= (M - a 0%N)%:E)%E.
  have habs : (fun x => `|h n x|) = h n by apply: funext=> x; rewrite ger0_norm.
  have hn := @total_lone_norm_from_absolute_integral R X mu hm (h n) (a n - a 0%N) (hhlp n).2.1.
  rewrite hn; first by rewrite lee_fin lerD2r.
  by rewrite habs; exact: hhi n.
have [hHlp [hH0 [_ hZ]]] := @bounded_increasing_lp_replacement R X mu hm 1%E (M - a 0%N) h
  hhlp hh0 (fun n m x hnm => hhle n m x hnm) hnorm.
pose H := real_lower_limit_replacement h.
have [c hc] := total_lone_summable_real hm hHlp.
pose Z := [set x | extended_increases_to (fun n => (h n x)%:E) (H x)%:E].
pose h' n x := if `[< Z x >] then h n x else 0.
pose H' x := if `[< Z x >] then H x else 0.
have hh'i n : is_measure_integral mu (real_total_integrand (h' n)) (a n - a 0%N)%:E.
  apply: (summable_total_almost_equal_integral (hhi n)).
  apply: (measure_almost_everywhere_mono hm _ hZ)=> x hx.
  by rewrite /= /h' (asboolT hx).
have hH'i : is_measure_integral mu (real_total_integrand H') c%:E.
  apply: (summable_total_almost_equal_integral hc).
  apply: (measure_almost_everywhere_mono hm _ hZ)=> x hx.
  by rewrite /= /H' (asboolT hx).
have hinc' : real_functions_increase_to h' H'.
  move=> x; rewrite /h' /H'; case: (asboolP (Z x))=> hx //.
  exact: constant_extended_increases.
have hlimc := real_integral_increasing_continuity hm hh'i hH'i hinc'.
exists (fun x => H x + f 0%N x), (c + a 0%N); split.
- have hs := real_total_integral_add hm hc (hi 0%N); exact: hs.
- have hs := extended_increases_to_add hlimc (constant_extended_increases (a 0%N)%:E).
  have he : (fun n => (a n - a 0%N + a 0%N)%:E) = (fun n => (a n)%:E).
    by apply: funext=> n; rewrite subrK.
  by rewrite he in hs.
- apply: (measure_almost_everywhere_mono hm _ (measure_almost_everywhere_and hm hY0 hZ)).
  move=> x [hx0 hxz].
  have hs := extended_increases_to_add hxz (constant_extended_increases (f 0%N x)%:E).
  have he : (fun n => (h n x + f 0%N x)%:E) = (fun n => (f n x)%:E).
    by apply: funext=> n; rewrite /h (asboolT hx0) subrK.
  by rewrite he in hs.
Qed.

End SummableIncreasingLimits.
