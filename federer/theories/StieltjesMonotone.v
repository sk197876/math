(** Federer (1969), 2.5.17, p. 111: in case the function g is nondecreasing,
    the induced Daniell integral mu is monotone, hence psi^- = 0. Here mu is
    shown to be a monotone Daniell integral on K(R), the representation
    theorem 2.5.3 gives a single K(R) regular measure psi with mu(f) = int f
    dpsi, and the costs of the suiting sequences of an open interval give
    psi{x : a < x < b} <= g(b) - g(a), the value V_a^b g for nondecreasing
    g. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  constructive_ereal topology normedtype.
From mathcomp Require Import ring lra.
From Federer Require Import RealMetricBackground ExtendedRealBoundsUP ExtendedRealBounds
  ExtendedRealOrderLimit CurveVariationUP CurveArcLength FunctionLatticeUP
  FunctionLatticeRegularityUP LatticeAdditiveFunctional DaniellIntegralUP
  MonotoneDaniellIntegralUP MonotoneDaniellIntegralLaws RegularDaniellRepresentation
  RegularDaniellEnvelope DaniellCoverUP RealIntegralFunctionalUP MeasureUP
  CompactSupportFunctionUP CompactSupportFunctionLattice StieltjesSums StieltjesIntegral
  StieltjesDaniellIntegral IntervalBumpFunctions.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section MonotoneIntegrator.
Variable R : realType.
Variable g : R -> R.
Hypothesis hg : curve_locally_finite_variation (g : R -> real_line_metric R).
Hypothesis hmono : forall x y : R, x <= y -> g x <= g y.
Local Notation KR := (@compactly_supported_continuous_functions R R).
Local Notation mu := (induced_daniell g).

(** Source for [stieltjes_sum_constant]: the sum of a constant c over a
    sequence from a to b is c [g(b) - g(a)], Federer 2.5.17, p. 110. *)
Lemma stieltjes_sum_constant (c a b : R) (w : seq R) :
  is_tagged_partition a b w -> stieltjes_sum (fun _ => c) g w = c * (g b - g a).
Proof.
have [n] := ubnP (size w); elim: n w a=> // n ih [|t [|u [|t' rest]]] a hsize hw.
- by case: hw=> [_ [h _]].
- have [_ [_ [hh hl]]] := hw; move: hh hl=> /= -> <- /=.
  by rewrite subrr mulr0.
- by case: hw=> [_ [h _]].
- have [t'' [rest' [[<- <-] [hat [htu [hut' hw']]]]]] := tagged_partition_tail hw.
  have hsize' : (size (t' :: rest) < n)%N by move: hsize; rewrite /= ltnS; exact: ltnW.
  by rewrite stieltjes_sum_cons (ih _ _ hsize' hw') hat; ring.
Qed.

(** Source for [stieltjes_sum_lower_bound]: for nondecreasing g and
    f >= m on [a, b], the sums are at least m [g(b) - g(a)], Federer
    2.5.17, p. 111. *)
Lemma stieltjes_sum_lower_bound (f : R -> R) (m a b : R) (w : seq R) :
  is_tagged_partition a b w -> (forall x, a <= x <= b -> m <= f x) ->
  m * (g b - g a) <= stieltjes_sum f g w.
Proof.
move=> hw hm; rewrite -(stieltjes_sum_constant m hw).
have hbound : forall x, x \in w -> a <= x <= b.
  by move=> x hx; have := sorted_mem_bounds hw.1 hx; rewrite (tagged_partition_head0 hw) (tagged_partition_last0 hw).
have hs0 := hw.1; move: hbound hs0; clear hw.
have [n] := ubnP (size w); elim: n w=> // n ih [|t [|u [|t' rest]]] hsize hb hs //.
rewrite !stieltjes_sum_cons; apply: lerD.
- apply: ler_wpM2r; first by rewrite subr_ge0; apply: hmono; move: hs=> /= /and3P[h1 h2 _]; exact: le_trans h1 h2.
  by apply: hm; apply: hb; rewrite !inE eqxx orbT.
- apply: ih; first by move: hsize; rewrite /= ltnS; exact: ltnW.
  + by move=> x hx; apply: hb; rewrite 2!in_cons hx !orbT.
  + by move: hs=> /= /and3P[_ _].
Qed.

(** Source for [stieltjes_sum_upper_bound]: for nondecreasing g and
    f <= M on [a, b], the sums are at most M [g(b) - g(a)], Federer
    2.5.17, p. 111. *)
Lemma stieltjes_sum_upper_bound (f : R -> R) (M a b : R) (w : seq R) :
  is_tagged_partition a b w -> (forall x, a <= x <= b -> f x <= M) ->
  stieltjes_sum f g w <= M * (g b - g a).
Proof.
move=> hw hM; rewrite -(stieltjes_sum_constant M hw).
have hbound : forall x, x \in w -> a <= x <= b.
  by move=> x hx; have := sorted_mem_bounds hw.1 hx; rewrite (tagged_partition_head0 hw) (tagged_partition_last0 hw).
have hs0 := hw.1; move: hbound hs0; clear hw.
have [n] := ubnP (size w); elim: n w=> // n ih [|t [|u [|t' rest]]] hsize hb hs //.
rewrite !stieltjes_sum_cons; apply: lerD.
- apply: ler_wpM2r; first by rewrite subr_ge0; apply: hmono; move: hs=> /= /and3P[h1 h2 _]; exact: le_trans h1 h2.
  by apply: hM; apply: hb; rewrite !inE eqxx orbT.
- apply: ih; first by move: hsize; rewrite /= ltnS; exact: ltnW.
  + by move=> x hx; apply: hb; rewrite 2!in_cons hx !orbT.
  + by move: hs=> /= /and3P[_ _].
Qed.

(** Source for [stieltjes_integral_lower_bound]: m [g(b) - g(a)] <=
    int_a^b f dg when f >= m on [a, b] and g is nondecreasing, Federer
    2.5.17, p. 111. *)
Lemma stieltjes_integral_lower_bound (f : R -> R) (m a b : R) :
  continuous f -> a <= b -> (forall x, a <= x <= b -> m <= f x) ->
  m * (g b - g a) <= stieltjes_integral g f a b.
Proof.
move=> hf hab hm; apply/ler_addgt0Pr=> e he.
have [d [hd hlim]] := stieltjes_integral_limit hg hf hab he.
have [N hN] := uniform_mesh_small hab hd.
have hw := uniform_partition_is N hab.
have h1 := hlim _ hw (uniform_partition_mesh (hN N (leqnn N))).
have h2 := stieltjes_sum_lower_bound hw hm.
by move: h1; rewrite ltr_norml=> /andP[_ h1]; lra.
Qed.

(** Source for [stieltjes_integral_upper_bound]: int_a^b f dg <=
    M [g(b) - g(a)] when f <= M on [a, b] and g is nondecreasing,
    Federer 2.5.17, p. 111. *)
Lemma stieltjes_integral_upper_bound (f : R -> R) (M a b : R) :
  continuous f -> a <= b -> (forall x, a <= x <= b -> f x <= M) ->
  stieltjes_integral g f a b <= M * (g b - g a).
Proof.
move=> hf hab hM; apply/ler_addgt0Pr=> e he.
have [d [hd hlim]] := stieltjes_integral_limit hg hf hab he.
have [N hN] := uniform_mesh_small hab hd.
have hw := uniform_partition_is N hab.
have h1 := hlim _ hw (uniform_partition_mesh (hN N (leqnn N))).
have h2 := stieltjes_sum_upper_bound hw hM.
by move: h1; rewrite ltr_norml=> /andP[h1 _]; lra.
Qed.

(** Source for [induced_daniell_nonnegative]: mu(f) >= 0 for f in K(R)+
    when g is nondecreasing, the monotonicity of mu in Federer 2.5.17,
    p. 111. *)
Lemma induced_daniell_nonnegative (f : R -> R) :
  KR f -> function_nonnegative f -> 0 <= mu f.
Proof.
move=> hf hf0; have [N [hN0 hz]] := compact_support_bound hf.
have hN1 : 0 <= N + 1 by lra.
have hzs : forall x, f x <> 0 -> `|x| < N + 1 by move=> x hx; have := hz x hx; lra.
rewrite -(induced_daniell_eq hg (KR_continuous hf) (compact_support_bound hf) hN1 hzs).
have hab : - (N + 1) <= N + 1 by lra.
by have := stieltjes_integral_lower_bound (m := 0) (KR_continuous hf) hab (fun x _ => hf0 x); rewrite mul0r.
Qed.

(** Source for [induced_daniell_monotone_daniell]: mu is a monotone
    Daniell integral on K(R) when g is nondecreasing, Federer 2.5.17,
    p. 111. *)
Theorem induced_daniell_monotone_daniell : is_monotone_daniell_integral KR mu.
Proof.
have hL := @compactly_supported_continuous_functions_lattice R R.
have hD := induced_daniell_is_daniell hg.
have hadd : forall f1 f2, KR f1 -> KR f2 -> mu (fun x => f1 x + f2 x) = mu f1 + mu f2.
  by move=> f1 f2 hf1 hf2; exact: (induced_daniell_add hg).
have hpos : forall f, KR f -> function_nonnegative f -> 0 <= mu f.
  by move=> f hf hf0; exact: induced_daniell_nonnegative.
have hmon := positive_additive_lattice_functional_monotone hL hadd hpos.
constructor=> //.
- by move=> c f hc hf; exact: (induced_daniell_scale hg).
- move=> f h hf hh hinc; split.
  + move=> n m hnm; rewrite lee_fin; apply: hmon=> // x.
    by have := (hinc x).1 n m hnm; rewrite lee_fin.
  + exact (daniell_integral_increasing_continuity hD hf hh hinc).
Qed.

(** Source for [absolute_chain_monotone]: for nondecreasing g the
    absolute increment sum over a nondecreasing list telescopes to
    g(last) - g(first), Federer 2.5.17, p. 111. *)
Lemma absolute_chain_monotone (M : seq R) :
  sorted <=%O M -> absolute_chain g M = g (last 0 M) - g (head 0 M).
Proof.
elim: M=> [_|t M ih]; first by rewrite /= subrr.
case: M ih=> [_ _|t' M ih]; first by rewrite /= subrr.
move=> hs; have /andP[htt' hs'] : (t <= t') && sorted <=%O (t' :: M) := hs.
rewrite absolute_chain_cons2 (ih hs') /=.
by rewrite ger0_norm ?subr_ge0 ?hmono //; ring.
Qed.

(** Source for [monotone_curve_variation_eq]: V_a^b g = g(b) - g(a) for
    nondecreasing g, Federer 2.5.17, p. 111, as an extended real. *)
Lemma monotone_curve_variation_eq (a b : R) :
  a <= b -> curve_variation (g : R -> real_line_metric R) a b = (g b - g a)%:E.
Proof.
move=> hab; apply/le_anti/andP; split.
- apply: extended_real_sup_least=> _ [M [[hs [hn [hh hl]]] ->]]; rewrite lee_fin.
  rewrite -absolute_chain_chain_sum (absolute_chain_monotone hs).
  have hne : M <> [::] by move=> h; rewrite h in hn.
  rewrite (last_nonempty_default 0 a hne) hl.
  by case: M hne hh {hs hn hl}=> [//|m M] _ /= ->; rewrite lexx.
- have hpair := variation_partition_pair hab.
  apply: le_trans (extended_real_sup_upper (ex_intro _ [:: a; b] (conj hpair erefl))).
  by rewrite lee_fin /= real_line_metric_distanceE distrC ger0_norm ?subr_ge0 ?hmono // addr0.
Qed.

(** Source for [monotone_locally_finite_variation]: a nondecreasing
    function has finite variation on every segment, the standing
    hypothesis of Federer 2.5.17, p. 110, for nondecreasing g. *)
Lemma monotone_locally_finite_variation : curve_locally_finite_variation (g : R -> real_line_metric R).
Proof. by move=> a b hab; rewrite (monotone_curve_variation_eq hab) ltry. Qed.

(** Source for [monotone_total_variation]: V_a^b g = g(b) - g(a) for
    nondecreasing g, Federer 2.5.17, p. 111. *)
Lemma monotone_total_variation (a b : R) : a <= b -> total_variation g a b = g b - g a.
Proof. by move=> hab; rewrite /total_variation (monotone_curve_variation_eq hab). Qed.

(** Source for [stieltjes_monotone_representation]: for nondecreasing g
    the K(R) regular measure psi of 2.5.3 represents mu, with
    psi{x : a < x < b} <= g(b) - g(a); this is psi^+ with psi^- = 0 in
    Federer 2.5.17, p. 111. *)
Theorem stieltjes_monotone_representation :
  exists psi : set R -> \bar R, is_measure psi /\ is_function_lattice_regular KR psi /\
    is_real_integral_functional psi KR mu /\
    forall a b : R, a <= b -> (psi `]a, b[ <= (g b - g a)%:E)%E.
Proof.
have hL := @compactly_supported_continuous_functions_lattice R R.
have hne : exists f, KR f by exists (fun _ => 0); exact: compactly_supported_zero_function.
have [psi [hm [hi [hr _]]]] :=
  monotone_daniell_regular_representation hL induced_daniell_monotone_daniell hne.
exists psi; split=> //; split=> //; split=> // a b hab.
have henv := regular_representing_measure_envelope hL hm hi hr.
pose S := [set z : \bar R | exists n, z = (mu (interval_bump a b n))%:E].
have hc : is_daniell_sequence_cost mu (interval_bump a b) (extended_real_sup S).
  by split; [exact: extended_real_sup_upper | exact: extended_real_sup_least].
have hsuit : is_daniell_suiting_sequence KR `]a, b[ (interval_bump a b).
  split; last split.
  - by move=> n; split; [exact: interval_bump_member | move=> x; exact: interval_bump_ge0].
  - by move=> n m hnm x; exact: interval_bump_monotone.
  - by move=> x hx r hr1; rewrite /= in_itv /= in hx; exact (interval_bump_limit hx hr1).
have hmuV := daniell_cover_lower henv hsuit hc.
apply: le_trans hmuV _; apply: extended_real_sup_least=> _ [n ->]; rewrite lee_fin.
rewrite (induced_daniell_value hg (interval_bump_member a b n) hab
  (fun x => @interval_bump_support R a b n x)).
have := stieltjes_integral_upper_bound (M := 1) (KR_continuous (interval_bump_member a b n)) hab
  (fun x _ => interval_bump_le1 a b n x).
by rewrite mul1r.
Qed.

End MonotoneIntegrator.
