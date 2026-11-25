(** Federer (1969), 2.5.12, p. 104, third paragraph of the proof: for y in E
    the function mu_y(f) = T(f . y) on L+ satisfies nu o (f . y) = nu(y) . f
    and |mu_y(f)| <= nu(y) . lambda(f), hence is a Daniell integral on L+.
    Since X is countably phi measurable, 2.5.9 yields k_y in L_oo(phi) with
    mu_y(f) = int f k_y dphi for f in L+, phi_(oo)(k_y) <= nu(y), and k_y is
    phi almost unique. Federer applies these statements to y in a countable
    dense set D; they hold for every y in E. The countable phi measurability
    of X is derived from hypothesis (3) through the positive strict levels
    of the members of K, as in 2.5.3. For y <> 0 the density is obtained
    from 2.5.9 applied to mu_y' with y' = y / nu(y), whose bound is lambda
    itself. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality
  reals constructive_ereal topology.
From mathcomp Require Import ring lra.
From Federer Require Import RealNormUP NormMetric RealMetricBackground FunctionLatticeUP
  FunctionLatticeLaws DaniellIntegralUP MonotoneDaniellIntegralUP ExtendedRealOrderLimit
  RealErrorOrderLimit MeasureUP RealIntegralFunctionalUP FunctionLatticeRegularityUP
  FunctionLatticeLevelFamilies FunctionLatticeLevelMeasurability LatticeSeriesCoverUP
  LatticeSeriesCoverLaws ExtendedRealReciprocalBounds CountablyMeasurableUP
  SummableRealFunctionUP SummableRealArithmetic MeasureIntegralUP TotalScalarLpUP
  TotalScalarLpClosure TotalScalarLpNormLaws LatticeL1ApproximationLaws RealLatticeDensityUP
  RealLatticeDensityUniqueness DominatedLatticeRepresentation MeasureAlmostUP
  TotalEssentialNormBound VectorDaniellHypotheses VectorDaniellVariationIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [real_increase_to_function_le]: the members of a sequence
    increasing to g lie below g, used for h_n <= g in Federer 2.5.12,
    p. 104. *)
Lemma real_increase_to_function_le (R : realType) (X : Type) (h : nat -> X -> R) (g : X -> R) :
  real_functions_increase_to h g -> forall n, function_le (h n) g.
Proof.
move=> hinc n x; have [hm [_ hl]] := hinc x.
rewrite leNgt; apply/negP=> hgt.
have hgt' : ((g x)%:E < (h n x)%:E)%E by rewrite lte_fin.
have [M hMM] := hl _ hgt'.
have h1 := hMM (maxn n M) (leq_maxr n M).
have h2 := hm n (maxn n M) (leq_maxl n M).
by move: (lt_le_trans h1 h2); rewrite ltxx.
Qed.

Section Densities.
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

Variable phi : set X -> \bar R.
Hypothesis hphi : is_measure phi.
Hypothesis hrep : is_real_integral_functional phi Lp lam.
Hypothesis hreg : is_function_lattice_regular Lp phi.

(** Source for [component_integral]: the function
    mu_y(f) = T(f . y) for f in L+ and y in E, Federer 2.5.12, p. 104. *)
Definition component_integral (y : E) (f : X -> R) : R := T (fun x => f x *: y).

(** Source for [component_norm]: the identity nu o (f . y) = nu(y) . f
    for nonnegative f, Federer 2.5.12, p. 104. *)
Lemma component_norm (y : E) (f : X -> R) (x : X) : 0 <= f x -> N (f x *: y) = N y * f x.
Proof. by move=> hf; rewrite (real_seminorm_scale hN.1) ger0_norm // mulrC. Qed.

(** Source for [component_integral_bound]: the estimate
    |mu_y(f)| <= nu(y) . lambda(f) for f in L+, Federer 2.5.12, p. 104. *)
Lemma component_integral_bound (y : E) (f : X -> R) :
  Lp f -> `|component_integral y f| <= N y * lam f.
Proof.
move=> hf.
have hw : Q (fun x => f x *: y) := vector_lattice_module_product hM y hf.1.
have hNy : 0 <= N y := real_seminorm_nonnegative hN.1 y.
have hg : Lp (fun x => N y * f x) := function_lattice_scale hLp hNy hf.
have hlam : lam (fun x => N y * f x) = N y * lam f := variation_integral_scale hN hL hQ hT hNy hf.
have h1 : T (fun x => f x *: y) <= N y * lam f.
  rewrite -hlam; apply: (variation_integral_upper hN hQ hT hg hw) => x.
  have h0 := hf.2 x; by rewrite component_norm.
have hw' : Q (fun x => (-1) *: (f x *: y)) := vector_function_space_scale hQ (-1) hw.
have h2 : T (fun x => (-1) *: (f x *: y)) <= N y * lam f.
  rewrite -hlam; apply: (variation_integral_upper hN hQ hT hg hw') => x.
  have h0 := hf.2 x; by rewrite (real_seminorm_scale hN.1) normrN1 mul1r component_norm.
rewrite (vector_variation_homogeneous hT _ hw) in h2.
by rewrite /component_integral ler_norml; apply/andP; split; lra.
Qed.

(** Source for [component_integral_add]: additivity of mu_y on L+,
    Federer 2.5.12, p. 104. *)
Lemma component_integral_add (y : E) (f g : X -> R) :
  Lp f -> Lp g -> component_integral y (fun x => f x + g x) = component_integral y f + component_integral y g.
Proof.
move=> hf hg; rewrite /component_integral.
rewrite -(vector_variation_additive hT (vector_lattice_module_product hM y hf.1)
  (vector_lattice_module_product hM y hg.1)).
by congr T; apply/funext=> x; rewrite scalerDl.
Qed.

(** Source for [component_integral_scale]: homogeneity of mu_y on L+,
    Federer 2.5.12, p. 104. *)
Lemma component_integral_scale (y : E) (c : R) (f : X -> R) :
  Lp f -> component_integral y (fun x => c * f x) = c * component_integral y f.
Proof.
move=> hf; rewrite /component_integral.
rewrite -(vector_variation_homogeneous hT c (vector_lattice_module_product hM y hf.1)).
by congr T; apply/funext=> x; rewrite scalerA.
Qed.

(** Source for [component_integral_daniell]: mu_y is a Daniell integral
    on L+, Federer 2.5.12, p. 104. *)
Theorem component_integral_daniell (y : E) : is_daniell_integral Lp (component_integral y).
Proof.
have hNy : 0 <= N y := real_seminorm_nonnegative hN.1 y.
constructor.
- by move=> f g hf hg; exact: component_integral_add.
- by move=> c f _ hf; exact: component_integral_scale.
- move=> f hf; exists (N y * lam f) => k [hk [_ hkf]].
  apply: le_trans (ler_norm _) _; apply: le_trans (component_integral_bound y hk) _.
  exact: (ler_wpM2l hNy (variation_integral_monotone hN hQ hT hk hf hkf)).
- move=> h g hh hg hinc.
  have hle := real_increase_to_function_le hinc.
  have hd : forall n, Lp (fun x => g x - h n x).
    by move=> n; exact (function_lattice_ordered_difference hLp (hh n) hg (hle n)).
  have hsum : forall n, (fun x => h n x + (g x - h n x)) = g.
    by move=> n; apply/funext=> x; rewrite addrC subrK.
  have hlim := (variation_integral_increases hL hQ hM hT hh hg hinc).2.
  apply: real_error_extended_order_limit => e he.
  have hc : 0 < N y + 1 by rewrite ltr_pwDr.
  have hd0 : 0 < e / (N y + 1) by rewrite divr_gt0.
  have [M hMM] := extended_finite_order_limit_error hlim hd0.
  exists M => n hn.
  have hmu : component_integral y g = component_integral y (h n) + component_integral y (fun x => g x - h n x).
    by rewrite -(component_integral_add y (hh n) (hd n)) hsum.
  have hlam : lam g = lam (h n) + lam (fun x => g x - h n x).
    by rewrite -(variation_integral_add hL hQ hM hT (hh n) (hd n)) hsum.
  have hb := component_integral_bound y (hd n).
  have ht := hMM n hn.
  pose t := `|lam (h n) - lam g|.
  have ht0 : 0 <= t := normr_ge0 _.
  have hdiff : lam (fun x => g x - h n x) <= t.
    by rewrite /t distrC; apply: le_trans (ler_norm _); rewrite hlam addrC addKr.
  have h1 : N y * lam (fun x => g x - h n x) <= N y * t := ler_wpM2l hNy hdiff.
  have h2 : (N y + 1) * t < (N y + 1) * (e / (N y + 1)) by rewrite ltr_pM2l.
  rewrite [X in _ < X]mulrC divfK ?gt_eqF // mulrDl mul1r in h2.
  rewrite hmu distrC addrC addKr.
  by apply: le_lt_trans hb _; lra.
Qed.

(** Source for [variation_space_countably_measurable]: X is countably
    phi measurable, the fact invoked before the application of 2.5.9 in
    Federer 2.5.12, p. 104; it follows from hypothesis (3) through the
    positive strict levels of the members of K, as in 2.5.3, p. 94. *)
Theorem variation_space_countably_measurable :
  has_lattice_unit_series L -> measure_countably_measurable phi setT.
Proof.
move=> [K hK].
pose V (p : nat * nat) := [set x | ((p.2.+1)%:R)^-1 < K p.1 x].
have hV : forall p, function_lattice_strict_levels Lp (V p).
  move=> p; exists (K p.1), (((p.2.+1)%:R)^-1); split.
    by have hk := hK.1 p.1; split; [exact: hk | exact: hk.2].
  by split; [rewrite invr_gt0 ltr0n | by []].
exists (V @` setT); split.
  by apply: sub_countable (card_image_le _ _) _; exact: countableP.
split.
  apply/seteqP; split=> x _ //.
  have [n hn] := positive_lattice_series_cover_positive_term hK (I : setT x).
  have [k hk] := positive_reciprocal_nat_small hn.
  by exists (V (n, k)); [exists (n, k) | exact hk].
move=> B [p _ <-]; split.
- exact (represented_lattice_strict_level_measurable hphi hrep (hV p)).
- exact (represented_lattice_strict_level_finite hphi hrep (hV p)).
Qed.

(** Source for [component_integral_zero]: mu_0 vanishes, since T is
    linear, Federer 2.5.12, p. 104. *)
Lemma component_integral_zero (f : X -> R) : component_integral 0 f = 0.
Proof.
rewrite /component_integral.
have -> : (fun x => f x *: (0 : E)) = (fun _ => 0) by apply/funext=> x; rewrite scaler0.
exact (variation_zero_map hQ hT).
Qed.

(** Source for [component_density]: for y in E there is k_y in L_oo(phi)
    with mu_y(f) = int f k_y dphi for f in L+ and phi_(oo)(k_y) <= nu(y),
    by 2.5.9, Federer 2.5.12, p. 104. *)
Theorem component_density (y : E) : measure_countably_measurable phi setT ->
  exists k, is_real_lattice_density phi Lp (component_integral y) k /\
    total_scalar_lp phi +oo k /\ (total_scalar_lp_norm phi +oo k <= (N y)%:E)%E.
Proof.
move=> hX.
have h1 : (1 <= (+oo : \bar R))%E := leey _.
have [->|hy] := eqVneq y 0.
  have hz := total_scalar_lp_zero hphi h1.
  exists (fun _ => 0); split.
    split; first exact: hz.2.1.
    move=> f hf; rewrite component_integral_zero.
    have -> : (fun x => f x * (0 : R)) = (fun _ => 0) by apply/funext=> x; rewrite mulr0.
    exact: (real_total_zero_integral hphi).
  split; first exact: hz.
  have hs := total_scalar_lp_norm_scale hphi 0 h1 hz.2.1.
  have e0 : (fun x : X => (0 : R) * 0) = (fun _ => 0) by apply/funext=> x; rewrite mulr0.
  by rewrite e0 normr0 mul0e in hs; rewrite (real_seminorm_zero hN.1) hs.
have hNy : 0 < N y by rewrite (real_norm_positive hN.1 hN.2).
pose y' := (N y)^-1 *: y.
have hNy' : N y' = 1.
  by rewrite (real_seminorm_scale hN.1) gtr0_norm ?invr_gt0 // mulVf // gt_eqF.
have hb : forall f, Lp f -> `|component_integral y' f| <= lam (fun x => `|f x|).
  move=> f hf; have -> : (fun x => `|f x|) = f by apply/funext=> x; rewrite ger0_norm // (hf.2 x).
  by have := component_integral_bound y' hf; rewrite hNy' mul1r.
have [k [hk [hklp [hkn _]]]] := dominated_lattice_integral_representation hLp hphi
  (variation_integral_monotone_daniell hL hQ hM hT) hrep hreg hX (component_integral_daniell y') hb.
have hs := total_scalar_lp_scale hphi (N y) hklp.
exists (fun x => N y * k x); split.
  split; first exact: hs.2.1.
  move=> f hf; have hi := real_total_integral_scale hphi (N y) (hk.2 f hf).
  have -> : (fun x => f x * (N y * k x)) = (fun x => N y * (f x * k x)).
    by apply/funext=> x; rewrite mulrCA.
  have -> : component_integral y f = N y * component_integral y' f.
    rewrite /component_integral -(vector_variation_homogeneous hT (N y) (vector_lattice_module_product hM y' hf.1)).
    by congr T; apply/funext=> x; rewrite /y' !scalerA mulrAC mulfV ?gt_eqF // mul1r.
  exact: hi.
split; first exact: hs.
have hn := total_scalar_lp_norm_scale hphi (N y) h1 hklp.2.1.
rewrite hn gtr0_norm //.
have h0 : (0 <= (N y)%:E)%E by rewrite lee_fin; exact: ltW.
by have := lee_wpmul2l h0 hkn; rewrite mule1.
Qed.

(** Source for [component_density_unique]: the density k_y is phi
    almost unique, Federer 2.5.12, p. 104. *)
Theorem component_density_unique (y : E) (k l : X -> R) : measure_countably_measurable phi setT ->
  is_real_lattice_density phi Lp (component_integral y) k ->
  is_real_lattice_density phi Lp (component_integral y) l ->
  measure_almost_everywhere phi [set x | k x = l x].
Proof. by move=> hX hk hl; exact (real_lattice_density_almost_unique hLp hphi hrep hreg hX hk hl). Qed.

(** Source for [component_density_bound]: the estimate |k_y(x)| <= nu(y)
    for phi almost all x, from phi_(oo)(k_y) <= nu(y), Federer 2.5.12,
    p. 104. *)
Lemma component_density_bound (y : E) (k : X -> R) :
  total_scalar_lp phi +oo k -> (total_scalar_lp_norm phi +oo k <= (N y)%:E)%E ->
  measure_almost_everywhere phi [set x | `|k x| <= N y].
Proof. by move=> hk hn; exact (total_essential_norm_almost_bound hphi hk hn). Qed.

End Densities.
