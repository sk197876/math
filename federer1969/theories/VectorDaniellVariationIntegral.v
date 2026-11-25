(** Federer (1969), 2.5.12, pp. 103–104: under the hypotheses (4) and (5)
    the variation integral lambda(f) = sup T(Q cap {w : nu o w <= f}) is a
    monotone Daniell integral on L+, and the L+ regular measure phi
    associated with lambda exists by 2.5.3. The proof follows the first two
    paragraphs of the printed proof: additivity through the splitting clause
    of (4), applied to h = inf{nu o w, f}, positive homogeneity,
    monotonicity, and increasing continuity through the sequence xi_n with
    nu o xi_n = inf{h_n, nu o w} and the continuity condition of (5) applied
    to w - xi_n. The identity nu o (w - xi) = nu o w - h used twice in the
    printed proof is isolated as a lemma. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality
  reals constructive_ereal topology.
From mathcomp Require Import ring lra.
From Federer Require Import RealNormUP NormMetric RealMetricBackground FunctionLatticeUP
  FunctionLatticeLaws MonotoneDaniellIntegralUP ExtendedRealOrderLimit ExtendedRealBoundsUP
  ExtendedRealLimitBounds MeasureUP RealIntegralFunctionalUP FunctionLatticeRegularityUP
  RegularDaniellRepresentation VectorDaniellHypotheses.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section VariationIntegral.
Variable R : realType.
Variable X : choiceType.
Variable E : lmodType R.
Variable N : E -> R.
Hypothesis hN : is_real_norm N.
Variable L : set (X -> R).
Variable Q : set (X -> E).
Variable T : (X -> E) -> R.
Hypothesis hL : is_function_lattice L.
Hypothesis hQ : is_vector_function_space Q.
Hypothesis hM : is_vector_lattice_module hN L Q.
Hypothesis hT : is_vector_variation_functional N L Q T.

Local Notation Lp := (positive_function_lattice L).
Local Notation lam := (variation_integral N Q T).

Let hLp : is_function_lattice Lp := positive_function_lattice_laws hL.

(** Source for [variation_admissible_zero]: the zero map is admissible
    for every f in L+, so the supremum defining lambda(f) in Federer
    2.5.12(5), p. 103, is over a nonempty set. *)
Lemma variation_admissible_zero (f : X -> R) :
  Lp f -> (Q `&` [set w | function_le (fun x => N (w x)) f]) (fun _ => 0).
Proof.
move=> [_ hf0]; split; first exact: (vector_function_space_zero hQ).
by move=> x; rewrite (real_seminorm_zero hN.1); exact: hf0.
Qed.

(** Source for [variation_has_sup]: the set T(Q cap {w : nu o w <= f})
    of Federer 2.5.12(5), p. 103, is nonempty and bounded above. *)
Lemma variation_has_sup (f : X -> R) :
  Lp f -> has_sup [set T w | w in Q `&` [set w | function_le (fun x => N (w x)) f]].
Proof.
move=> hf; split.
  by exists (T (fun _ => 0)); exact: (imageP T (variation_admissible_zero hf)).
have [b hb] := vector_variation_bounded hT hf.
by exists b=> _ [w [hw hle] <-]; exact: hb.
Qed.

(** Source for [variation_integral_upper]: T(w) <= lambda(f) for
    admissible w, Federer 2.5.12(5), p. 103. *)
Lemma variation_integral_upper (f : X -> R) (w : X -> E) :
  Lp f -> Q w -> function_le (fun x => N (w x)) f -> T w <= lam f.
Proof.
move=> hf hw hle; have hmem : (Q `&` [set w | function_le (fun x => N (w x)) f]) w by split.
exact: (sup_upper_bound (variation_has_sup hf) (imageP T hmem)).
Qed.

(** Source for [variation_integral_least]: lambda(f) is the least upper
    bound of the values T(w) over admissible w, Federer 2.5.12(5),
    p. 103. *)
Lemma variation_integral_least (f : X -> R) (b : R) :
  Lp f -> (forall w, Q w -> function_le (fun x => N (w x)) f -> T w <= b) -> lam f <= b.
Proof.
move=> hf hb; rewrite /variation_integral; apply: ge_sup.
  by exists (T (fun _ => 0)); exact: (imageP T (variation_admissible_zero hf)).
by move=> _ [w [hw hle] <-]; exact: hb.
Qed.

(** Source for [variation_zero_map]: T vanishes on the zero map, by
    the linearity of T in Federer 2.5.12(5), p. 103. *)
Lemma variation_zero_map : T (fun _ : X => (0 : E)) = 0.
Proof.
have h := vector_variation_homogeneous hT 0 (vector_function_space_zero hQ).
rewrite mul0r in h.
have -> : (fun _ : X => (0 : E)) = (fun _ : X => 0 *: (0 : E)).
  by apply/funext=> x; rewrite scale0r.
exact: h.
Qed.

(** Source for [variation_integral_zero]: lambda vanishes on the zero
    function, since only the zero map is admissible, Federer 2.5.12,
    p. 104, "Clearly lambda is positively homogeneous". *)
Lemma variation_integral_zero : lam (fun _ : X => (0 : R)) = 0.
Proof.
rewrite /variation_integral.
have -> : [set T w | w in Q `&` [set w | function_le (fun x => N (w x)) (fun _ => 0)]] = [set 0].
  apply/seteqP; split=> [_ [w [hw hle] <-]|_ ->].
  - have hw0 : w = (fun _ => 0).
      apply/funext=> x; apply: hN.2; apply/eqP; rewrite eq_le (hle x).
      by rewrite (real_seminorm_nonnegative hN.1).
    by rewrite hw0 variation_zero_map.
  - exists (fun _ => 0); last exact: variation_zero_map.
    split; first exact: (vector_function_space_zero hQ).
    by move=> x; rewrite (real_seminorm_zero hN.1).
exact: sup1.
Qed.

(** Source for [variation_integral_monotone]: lambda is monotone,
    Federer 2.5.12, p. 104. *)
Lemma variation_integral_monotone (f g : X -> R) :
  Lp f -> Lp g -> function_le f g -> lam f <= lam g.
Proof.
move=> hf hg hfg; apply: variation_integral_least hf _ => w hw hle.
by apply: variation_integral_upper hg hw _ => x; exact: le_trans (hle x) (hfg x).
Qed.

(** Source for [variation_split_difference]: for w in Q and f in L+ with
    f <= nu o w, the map xi of hypothesis (4) satisfies
    nu o (w - xi) = nu o w - f, the inference drawn twice in the proof
    of Federer 2.5.12, pp. 103–104. *)
Lemma variation_split_difference (w : X -> E) (f : X -> R) :
  Q w -> Lp f -> function_le f (fun x => N (w x)) ->
  exists xi, Q xi /\ Q (fun x => w x - xi x) /\ (forall x, N (xi x) = f x) /\
    forall x, N (w x - xi x) = N (w x) - f x.
Proof.
move=> hw hf hle; have [xi [hxi [hn hs]]] := vector_lattice_module_split hM hw hf hle.
exists xi; split=> //; split.
  suff -> : (fun x => w x - xi x) = (fun x => w x + (-1) *: xi x).
    exact (vector_function_space_add hQ hw (vector_function_space_scale hQ (-1) hxi)).
  by apply/funext=> x; rewrite scaleN1r.
split=> // x.
have hf0 : 0 <= f x := hf.2 x.
have := real_seminorm_nonnegative hN.1 (w x); rewrite le_eqVlt=> /orP[/eqP h0|hpos].
- have hwx : w x = 0 := hN.2 _ (esym h0).
  have hfx0 : f x <= 0 by have := hle x; rewrite -h0.
  have hfx : f x = 0 by apply/eqP; rewrite eq_le hfx0 hf0.
  have hxix : xi x = 0 by apply: hN.2; rewrite hn hfx.
  by rewrite hwx hxix hfx !subr0 (real_seminorm_zero hN.1).
- have hne : N (w x) != 0 by rewrite gt_eqF.
  have hxi' : xi x = (f x / N (w x)) *: w x.
    by have := congr1 (fun v => (N (w x))^-1 *: v) (hs x); rewrite /= !scalerA mulVf // scale1r mulrC.
  rewrite hxi' -{1}(scale1r (w x)) -scalerBl (real_seminorm_scale hN.1) ger0_norm.
  + by rewrite mulrBl mul1r mulfVK.
  + by rewrite subr_ge0 ler_pdivrMr // mul1r; exact: hle.
Qed.

(** Source for [variation_integral_add]: additivity of lambda on L+,
    first paragraph of the proof of Federer 2.5.12, p. 103. *)
Lemma variation_integral_add (f g : X -> R) :
  Lp f -> Lp g -> lam (fun x => f x + g x) = lam f + lam g.
Proof.
move=> hf hg; have hfg : Lp (fun x => f x + g x) := function_lattice_add hLp hf hg.
apply/eqP; rewrite eq_le; apply/andP; split.
- apply: variation_integral_least hfg _ => w hw hle.
  pose h := fun x => Order.min (N (w x)) (f x).
  have hh : Lp h.
    split; first exact (function_lattice_minimum hL (vector_lattice_module_norm hM hw) hf.1).
    by move=> x; rewrite le_min (real_seminorm_nonnegative hN.1) hf.2.
  have hhw : function_le h (fun x => N (w x)) by move=> x; rewrite ge_min lexx.
  have [xi [hxi [hwxi [hnxi hnd]]]] := variation_split_difference hw hh hhw.
  have hsplit : T w = T xi + T (fun x => w x - xi x).
    rewrite -(vector_variation_additive hT hxi hwxi); congr T; apply/funext=> x.
    by rewrite addrC subrK.
  rewrite hsplit; apply: lerD.
  + by apply: variation_integral_upper hf hxi _ => x; rewrite hnxi /h ge_min lexx orbT.
  + apply: (variation_integral_upper hg hwxi _) => x; rewrite hnd /h.
    have h2 := hle x; have [h1|h1] := boolP (N (w x) <= f x).
    * by rewrite min_l // subrr; exact: hg.2.
    * rewrite -ltNge in h1; rewrite min_r ?(ltW h1) //; lra.
- have hbound : forall w1, Q w1 -> function_le (fun x => N (w1 x)) f ->
      T w1 <= lam (fun x => f x + g x) - lam g.
    move=> w1 hw1 hle1.
    have h2 : forall w2, Q w2 -> function_le (fun x => N (w2 x)) g ->
        T w2 <= lam (fun x => f x + g x) - T w1.
      move=> w2 hw2 hle2.
      have hadm : function_le (fun x => N (w1 x + w2 x)) (fun x => f x + g x).
        by move=> x; exact: le_trans (real_seminorm_triangle hN.1 _ _) (lerD (hle1 x) (hle2 x)).
      have := variation_integral_upper hfg (vector_function_space_add hQ hw1 hw2) hadm.
      rewrite (vector_variation_additive hT hw1 hw2); lra.
    have := variation_integral_least hg h2; lra.
  have := variation_integral_least hf hbound; lra.
Qed.

(** Source for [variation_integral_scale]: positive homogeneity of
    lambda on L+, Federer 2.5.12, p. 104. *)
Lemma variation_integral_scale (c : R) (f : X -> R) :
  0 <= c -> Lp f -> lam (fun x => c * f x) = c * lam f.
Proof.
move=> hc hf; have hcf : Lp (fun x => c * f x) := function_lattice_scale hLp hc hf.
move: hc; rewrite le_eqVlt=> /orP[/eqP hc0|hc].
- rewrite -hc0 mul0r.
  have -> : (fun x => 0 * f x) = (fun _ : X => (0 : R)) by apply/funext=> x; rewrite mul0r.
  exact: variation_integral_zero.
- have hne : c != 0 by rewrite gt_eqF.
  apply/eqP; rewrite eq_le; apply/andP; split.
  + apply: variation_integral_least hcf _ => w hw hle.
    have hw' : Q (fun x => c^-1 *: w x) := vector_function_space_scale hQ _ hw.
    have hle' : function_le (fun x => N (c^-1 *: w x)) f.
      move=> x; rewrite (real_seminorm_scale hN.1) gtr0_norm ?invr_gt0 //.
      by rewrite -(ler_pM2l (x := c) hc) mulrA mulfV // mul1r; exact: hle.
    have h1 := variation_integral_upper hf hw' hle'.
    rewrite (vector_variation_homogeneous hT _ hw) in h1.
    have h2 := ler_wpM2l (x := c) (ltW hc) h1.
    by rewrite mulrA mulfV // mul1r in h2.
  + have hc' : 0 < c^-1 by rewrite invr_gt0.
    rewrite -(ler_pM2l (x := c^-1) hc') mulrA mulVf // mul1r.
    apply: variation_integral_least hf _ => w hw hle.
    rewrite -(ler_pM2l (x := c) hc) mulrA mulfV // mul1r -(vector_variation_homogeneous hT c hw).
    apply: variation_integral_upper hcf (vector_function_space_scale hQ c hw) _ => x.
    by rewrite (real_seminorm_scale hN.1) gtr0_norm //; exact (ler_wpM2l (x := c) (ltW hc) (hle x)).
Qed.

(** Source for [variation_integral_increases]: lambda preserves
    increasing convergence on L+, second paragraph of the proof of
    Federer 2.5.12, p. 104. *)
Lemma variation_integral_increases (h : nat -> X -> R) (g : X -> R) :
  (forall n, Lp (h n)) -> Lp g -> real_functions_increase_to h g ->
  extended_increases_to (fun n => (lam (h n))%:E) (lam g)%:E.
Proof.
move=> hh hg hinc.
have hmono : forall n m, (n <= m)%N -> function_le (h n) (h m).
  by move=> n m hnm x; have := (hinc x).1 n m hnm; rewrite lee_fin.
have hle_g : forall n, function_le (h n) g.
  move=> n x; have [hm [_ hl]] := hinc x.
  rewrite leNgt; apply/negP=> hgt.
  have hgt' : ((g x)%:E < (h n x)%:E)%E by rewrite lte_fin.
  have [M hMM] := hl _ hgt'.
  have h1 := hMM (maxn n M) (leq_maxr n M).
  have h2 := hm n (maxn n M) (leq_maxl n M).
  by move: (lt_le_trans h1 h2); rewrite ltxx.
apply: extended_increasing_supremum_limit.
  by move=> n m hnm; rewrite lee_fin; exact: variation_integral_monotone (hh n) (hh m) (hmono n m hnm).
constructor.
  by move=> _ [n ->]; rewrite lee_fin; exact: variation_integral_monotone (hh n) hg (hle_g n).
move=> d hd; case: d hd=> [r| |] hd; [|exact: leey|].
  2: by have := hd _ (ex_intro _ 0%N erefl); rewrite leeNy_eq=> /eqP.
have hr : forall n, lam (h n) <= r by move=> n; rewrite -lee_fin; exact: hd _ (ex_intro _ n erefl).
rewrite lee_fin; apply: variation_integral_least hg _ => w hw hle.
pose fn n := fun x => Order.min (h n x) (N (w x)).
have hfn : forall n, Lp (fn n).
  move=> n; split; first exact (function_lattice_minimum hL (hh n).1 (vector_lattice_module_norm hM hw)).
  by move=> x; rewrite le_min (hh n).2 (real_seminorm_nonnegative hN.1).
have hfnw : forall n, function_le (fn n) (fun x => N (w x)).
  by move=> n x; rewrite ge_min lexx orbT.
have hfnh : forall n, function_le (fn n) (h n) by move=> n x; rewrite ge_min lexx.
have hxi : forall n, exists xi, Q xi /\ Q (fun x => w x - xi x) /\ (forall x, N (xi x) = fn n x) /\
    forall x, N (w x - xi x) = N (w x) - fn n x.
  by move=> n; exact: variation_split_difference hw (hfn n) (hfnw n).
pose xi n := sval (cid (hxi n)).
have hxiP : forall n, Q (xi n) /\ Q (fun x => w x - xi n x) /\ (forall x, N (xi n x) = fn n x) /\
    forall x, N (w x - xi n x) = N (w x) - fn n x.
  by move=> n; exact: svalP (cid (hxi n)).
have heta : forall n, Q (fun x => w x - xi n x) by move=> n; exact: (hxiP n).2.1.
have hdec : forall x, extended_decreases_to (fun n => (N (w x - xi n x))%:E) (0 : R)%:E.
  move=> x; split.
    move=> n m hnm; rewrite lee_fin (hxiP n).2.2.2 (hxiP m).2.2.2.
    apply: lerB (lexx _) _; rewrite /fn le_min !ge_min (hmono n m hnm x) lexx orbT.
    by [].
  split.
    move=> a ha; exists 0%N=> n _; apply: lt_le_trans ha _.
    by rewrite lee_fin (real_seminorm_nonnegative hN.1).
  move=> b; case: b=> [r'| |] hb; [|by exists 0%N=> n _; exact: ltry|by []].
  rewrite lte_fin in hb.
  have [_ [hlow _]] := hinc x.
  have hlt : ((N (w x) - r')%:E < (g x)%:E)%E.
    by rewrite lte_fin; have := hle x; lra.
  have [M hMM] := hlow _ hlt.
  exists M=> n hn; rewrite lte_fin (hxiP n).2.2.2 /fn.
  have := hMM n hn; rewrite lte_fin=> hMn.
  have [h1|h1] := boolP (N (w x) <= h n x).
    by rewrite min_r // subrr.
  by rewrite -ltNge in h1; rewrite min_l ?(ltW h1) //; lra.
have hlim := vector_variation_continuous hT heta hdec.
have hTw : forall n, T w = T (xi n) + T (fun x => w x - xi n x).
  move=> n; rewrite -(vector_variation_additive hT (hxiP n).1 (heta n)); congr T.
  by apply/funext=> x; rewrite addrC subrK.
have hTxi : forall n, T (xi n) <= r.
  move=> n; apply: le_trans (hr n).
  apply: variation_integral_upper (hh n) (hxiP n).1 _ => x.
  by rewrite (hxiP n).2.2.1; exact: hfnh.
have hlow : forall n, ((T w - r)%:E <= (T (fun x => w x - xi n x))%:E)%E.
  by move=> n; rewrite lee_fin; have := hTw n; have := hTxi n; lra.
have := extended_order_limit_lower_bound hlim hlow; rewrite lee_fin; lra.
Qed.

(** Source for [variation_integral_monotone_daniell]: lambda is a
    monotone Daniell integral on L+, the first conclusion of Federer
    2.5.12, p. 103. *)
Theorem variation_integral_monotone_daniell : is_monotone_daniell_integral Lp lam.
Proof.
constructor.
- exact: variation_integral_add.
- exact: variation_integral_scale.
- exact: variation_integral_monotone.
- exact: variation_integral_increases.
Qed.

(** Source for [variation_measure_exists]: the L+ regular measure phi
    associated with lambda, called the variation measure in Federer
    2.5.12, p. 103, exists and is unique by 2.5.3. *)
Theorem variation_measure_exists : (exists f, L f) ->
  exists phi, is_measure phi /\ is_real_integral_functional phi Lp lam /\
    is_function_lattice_regular Lp phi /\
    forall nu, is_measure nu -> is_real_integral_functional nu Lp lam ->
      is_function_lattice_regular Lp nu -> forall S, phi S = nu S.
Proof.
move=> [f hf].
apply: (monotone_daniell_regular_representation hLp variation_integral_monotone_daniell).
exists (fun _ => 0); split; first exact (function_lattice_zero hL hf).
by move=> x.
Qed.

End VariationIntegral.
