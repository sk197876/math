(** Federer (1969), 2.5.4, pp. 95–96: two examples depending on 2.5.17. (1)
    p : R^2 -> R, p(x) = x_1, L_1 is the set of all functions u o p
    corresponding to continuous u : R -> R, and lambda_1(u o p) = int_0^1 u
    dL^1; the L_1 regular measure phi_1 associated with lambda_1 satisfies
    phi_1(A) = L^1[p(A) cap {t : 0 <= t <= 1}] whenever A subset R^2. (2)
    L_2 is the set of all continuous real valued functions on R^2 and
    lambda_2(f) = int_0^1 f(t, 0) dL^1 t; the L_2 regular measure phi_2
    associated with lambda_2 satisfies phi_2(A) = L^1[xi^{-1}(A) cap {t : 0
    <= t <= 1}] whenever A subset R^2, where xi(t) = (t, 0). The set {x :
    x_2 >= 0} is not phi_1 measurable; L_1 subset L_2 and lambda_1 =
    lambda_2|L_1, hence the conclusion of 2.5.2 holds with L_1, lambda_1 and
    either of phi_1, phi_2; and phi_2 is not L_1 regular. The plane is the
    product R * R with the product topology of mathcomp-analysis. Both
    functionals are the single function [plane_section_integral], F |->
    int_0^1 F(t, 0) dt, given by the Riemann integral of 2.5.17; L^1 is any
    measure with the properties recorded in [lebesgue_line_measure_exists].
    The values of phi_1 and phi_2 are computed from the envelope formula of
    2.5.2 by comparing suiting sequences of the plane lattices with suiting
    sequences of K(R). The statement that all Borel sets of R^2 are phi_2
    measurable is proved in PlaneBorelMeasurability.v, and
    PlaneMeasureComparison.v combines it with the Borel set {x : x_2 >= 0},
    which is not phi_1 measurable. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  constructive_ereal topology normedtype.
From mathcomp Require Import ring lra.
From Federer Require Import RealMetricBackground ExtendedRealBoundsUP ExtendedRealBounds
  ExtendedRealOrderLimit CurveVariationUP CurveArcLength FunctionLatticeUP FunctionLatticeLaws
  ContinuousFunctionLattice MonotoneDaniellIntegralUP MonotoneDaniellIntegralLaws
  RegularDaniellRepresentation RegularDaniellEnvelope DaniellCoverUP RealIntegralFunctionalUP
  FunctionLatticeRegularityUP MeasureUP MeasureBasic CompactSupportFunctionUP
  CompactSupportFunctionLattice StieltjesSums StieltjesIntegral StieltjesDaniellIntegral
  StieltjesMonotone IntervalBumpFunctions LebesgueLineMeasure ArchimedeanReciprocal.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section PlaneExamples.
Variable R : realType.
Local Notation plane := (R * R)%type.
Local Notation KR := (@compactly_supported_continuous_functions R R).
Local Notation CR := [set f : R -> R | continuous (f : R -> real_line_metric R)].
Local Notation id_fun := (fun x : R => x).
Let hmono : forall x y : R, x <= y -> id_fun x <= id_fun y := fun x y h => h.
Let hg : curve_locally_finite_variation (id_fun : R -> real_line_metric R) :=
  monotone_locally_finite_variation hmono.
Let hCR : is_function_lattice CR := @continuous_functions_lattice R R.
Let hKR : is_function_lattice KR := @compactly_supported_continuous_functions_lattice R R.
Local Notation mu := (induced_daniell id_fun).

(** Source for [first_coordinate_continuous]: supporting continuity of u o p
    for continuous u : R -> R, Federer 2.5.4(1), p. 95 *)
Lemma first_coordinate_continuous (u : R -> R) :
  continuous u -> continuous (fun x : plane => u x.1).
Proof.
move=> hu p; apply: (@continuous_comp _ _ _ fst u p); last exact: hu.
exact: cvg_fst.
Qed.

(** Source for [second_coordinate_continuous]: supporting continuity of a
    function of the second coordinate, Federer 2.5.4(2), p. 96. *)
Lemma second_coordinate_continuous (u : R -> R) :
  continuous u -> continuous (fun x : plane => u x.2).
Proof.
move=> hu p; apply: (@continuous_comp _ _ _ snd u p); last exact: hu.
exact: cvg_snd.
Qed.

(** Source for [section_map_continuous]: the map xi(t) = (t, 0) of Federer
    2.5.4(2), p. 96, is continuous. *)
Lemma section_map_continuous : continuous (fun t : R => ((t, 0) : plane)).
Proof.
move=> t A [[B C] /= [hB hC] hBC].
have hB' : nbhs t B := hB.
apply: filterS hB'=> s hs; apply: hBC; split=> //=.
exact: nbhs_singleton hC.
Qed.

(** Source for [section_continuous]: f o xi is continuous for continuous f
    on R^2, Federer 2.5.4(2), p. 96. *)
Lemma section_continuous (F : plane -> R) :
  continuous F -> continuous (fun t : R => F (t, 0)).
Proof.
move=> hF t; apply: (@continuous_comp _ _ _ (fun t : R => ((t, 0) : plane)) F t); last exact: hF.
exact: section_map_continuous.
Qed.

(** Source for [absolute_value_continuous]: supporting continuity of the
    absolute value, used for the auxiliary functions of Federer 2.5.4(2), p.
    96. *)
Lemma absolute_value_continuous : continuous (fun s : R => `|s|).
Proof.
apply: (lipschitz_continuous (L := 1) ler01)=> x y; rewrite mul1r.
exact: ler_dist_dist.
Qed.

(** Source for [plane_section_integral]: the common formula lambda(f) =
    int_0^1 f(t, 0) dL^1 t of both functionals in Federer 2.5.4, pp. 95–96,
    with the Riemann integral of 2.5.17 For f = u o p this is int_0^1 u
    dL^1. *)
Definition plane_section_integral (F : plane -> R) : R :=
  stieltjes_integral id_fun (fun t => F (t, 0)) 0 1.

(** Source for [first_coordinate_lattice]: the lattice L_1 of all functions
    u o p with u : R -> R continuous, Federer 2.5.4(1), p. 95 *)
Definition first_coordinate_lattice : set (plane -> R) :=
  [set F | exists u : R -> R, continuous u /\ F = fun x => u x.1].

(** Source for [plane_continuous_lattice]: the lattice L_2 of all continuous
    real valued functions on R^2, Federer 2.5.4(2), p. 96. *)
Definition plane_continuous_lattice : set (plane -> R) :=
  [set F | continuous (F : plane -> real_line_metric R)].

(** Source for [first_coordinate_lattice_is_lattice]: L_1 is a lattice of
    functions on R^2 in the sense of 2.5.1, Federer 2.5.4(1), p. 95 *)
Lemma first_coordinate_lattice_is_lattice : is_function_lattice first_coordinate_lattice.
Proof.
constructor.
- move=> F G [u [hu ->]] [v [hv ->]]; exists (fun t => u t + v t); split=> //.
  exact (function_lattice_add hCR hu hv).
- move=> c F hc [u [hu ->]]; exists (fun t => c * u t); split=> //.
  exact (function_lattice_scale hCR hc hu).
- move=> F G [u [hu ->]] [v [hv ->]]; exists (fun t => Order.min (u t) (v t)); split=> //.
  exact (function_lattice_minimum hCR hu hv).
- move=> c F hc [u [hu ->]]; exists (fun t => Order.min (u t) c); split=> //.
  exact (function_lattice_truncation hCR hc hu).
- move=> F G [u [hu ->]] [v [hv ->]] hle; exists (fun t => v t - u t); split=> //.
  apply: (function_lattice_ordered_difference hCR hu hv)=> t; exact: (hle (t, 0)).
Qed.

(** Source for [first_coordinate_lattice_section]: for u o p in L_1 the
    function t |-> (u o p)(t, 0) = u(t) is continuous, Federer 2.5.4(1), p.
    95 *)
Lemma first_coordinate_lattice_section (F : plane -> R) :
  first_coordinate_lattice F -> continuous (fun t => F (t, 0)).
Proof. by move=> [u [hu ->]]. Qed.

(** Source for [first_coordinate_lattice_subset]: L_1 subset L_2, Federer
    2.5.4, p. 96, last paragraph. *)
Lemma first_coordinate_lattice_subset : first_coordinate_lattice `<=` plane_continuous_lattice.
Proof. by move=> F [u [hu ->]]; exact: first_coordinate_continuous. Qed.

(** Source for [plane_continuous_lattice_is_lattice]: L_2 is a lattice of
    functions on R^2, Federer 2.5.4(2), p. 96, by the continuous function
    example of 2.5.1. *)
Lemma plane_continuous_lattice_is_lattice : is_function_lattice plane_continuous_lattice.
Proof. exact: (@continuous_functions_lattice R plane). Qed.

(** Source for [plane_continuous_lattice_section]: f o xi is continuous for
    f in L_2, Federer 2.5.4(2), p. 96. *)
Lemma plane_continuous_lattice_section (F : plane -> R) :
  plane_continuous_lattice F -> continuous (fun t => F (t, 0)).
Proof. by move=> hF; exact: section_continuous. Qed.

(** Source for [real_increase_to_le]: supporting fact that a sequence
    increasing to g is bounded by g, Federer 2.5.1, p. 92, for the Daniell
    condition in 2.5.4, pp. 95–96. *)
Lemma real_increase_to_le (X : Type) (F : nat -> X -> R) (G : X -> R) :
  real_functions_increase_to F G -> forall n x, F n x <= G x.
Proof.
move=> hinc n x; apply/ler_addgt0Pr=> e he.
have hlt : ((G x)%:E < (G x + e)%:E)%E by rewrite lte_fin; lra.
have [N hN] := (hinc x).2.2 _ hlt.
have h1 := hN (maxn N n) (leq_maxl N n).
have h2 := (hinc x).1 n (maxn N n) (leq_maxr N n).
by move: h1 h2; rewrite lte_fin lee_fin; lra.
Qed.

(** Source for [plane_section_monotone_daniell]: lambda_1 and lambda_2 are
    monotone Daniell integrals, the premise of the phrase "the L regular
    measure associated with lambda" in Federer 2.5.4, pp. 95–96 The
    hypothesis is that every member of the lattice has a continuous
    restriction to the line {x : x_2 = 0}; the limit condition follows from
    the Dini type estimate of 2.5.17 on the segment [0, 1]. *)
Theorem plane_section_monotone_daniell (L : set (plane -> R)) (hL : is_function_lattice L)
    (hsec : forall F, L F -> continuous (fun t => F (t, 0))) :
  is_monotone_daniell_integral L plane_section_integral.
Proof.
have hadd : forall F G, L F -> L G ->
    plane_section_integral (fun x => F x + G x) = plane_section_integral F + plane_section_integral G.
  move=> F G hF hG.
  exact (stieltjes_integral_add hg (hsec _ hF) (hsec _ hG) (hsec _ (function_lattice_add hL hF hG)) ler01).
have hpos : forall F, L F -> function_nonnegative F -> 0 <= plane_section_integral F.
  move=> F hF hF0.
  have := stieltjes_integral_lower_bound hg hmono (m := 0) (hsec _ hF) ler01 (fun t _ => hF0 (t, 0)).
  by rewrite mul0r.
have hmon := positive_additive_lattice_functional_monotone hL hadd hpos.
constructor=> //.
- move=> c F hc hF.
  exact (stieltjes_integral_scale hg (hsec _ hF) (hsec _ (function_lattice_scale hL hc hF)) ler01).
move=> F G hF hG hinc.
have hle : forall n, function_le (F n) G := fun n x => real_increase_to_le hinc n x.
have hmonF : forall n m, (n <= m)%N -> function_le (F n) (F m).
  by move=> n m hnm x; have := (hinc x).1 n m hnm; rewrite lee_fin.
split; first by move=> n m hnm; rewrite lee_fin; apply: hmon=> //; exact: hmonF.
split; last first.
  move=> b hb; exists 0%N=> n _; apply: le_lt_trans hb; rewrite lee_fin.
  by apply: hmon=> //; exact: hle.
move=> a; case: a=> [a ha|ha|_]; last by exists 0%N=> n _; exact: ltNyr.
- rewrite lte_fin in ha.
  pose e := (plane_section_integral G - a) / 2.
  have he : 0 < e by rewrite /e; lra.
  pose h := fun n t => F n (t, 0) - G (t, 0).
  have hc : forall n, continuous (h n).
    move=> n t.
    exact: (@continuousB R R^o R (fun t => F n (t, 0)) (fun t => G (t, 0)) t (hsec _ (hF n) t) (hsec _ hG t)).
  have hhmon : forall n m, (n <= m)%N -> forall t, h n t <= h m t.
    by move=> n m hnm t; rewrite /h; have := hmonF n m hnm (t, 0); lra.
  have hhlim : forall t, `[0, 1] t -> forall r, r < 0 -> exists n, r < h n t.
    move=> t _ r hr.
    have hlt : ((G (t, 0) + r)%:E < (G (t, 0))%:E)%E by rewrite lte_fin; lra.
    have [N hN] := (hinc (t, 0)).2.1 _ hlt.
    by exists N; have := hN N (leqnn N); rewrite lte_fin /h; lra.
  have [N hN] := compact_increasing_eventually_above (@segment_compact R 0 1) hc hhmon hhlim he.
  exists N=> n hn; rewrite lte_fin.
  have hdiff : L (fun x => G x - F n x) := function_lattice_ordered_difference hL (hF n) hG (hle n).
  have heq : (fun x => F n x + (G x - F n x)) = G by apply/funext=> x; ring.
  have hsplit := hadd _ _ (hF n) hdiff; rewrite heq in hsplit.
  have hsmall : forall t, 0 <= t <= 1 -> G (t, 0) - F n (t, 0) <= e.
    move=> t ht; have hK : `[0, 1] t by rewrite /= in_itv /= ht.
    by have := hN n hn t hK; rewrite /h; lra.
  have hbound : plane_section_integral (fun x => G x - F n x) <= e.
    have := stieltjes_integral_upper_bound hg hmono (M := e) (hsec _ hdiff) ler01 hsmall.
    by rewrite /= subr0 mulr1.
  by rewrite /e in hbound; lra.
- by move: ha; rewrite ltNge leey.
Qed.

(** Source for [first_coordinate_monotone_daniell]: lambda_1 is a monotone
    Daniell integral on L_1, Federer 2.5.4(1), p. 95 *)
Theorem first_coordinate_monotone_daniell :
  is_monotone_daniell_integral first_coordinate_lattice plane_section_integral.
Proof.
exact (plane_section_monotone_daniell first_coordinate_lattice_is_lattice
  first_coordinate_lattice_section).
Qed.

(** Source for [plane_continuous_monotone_daniell]: lambda_2 is a monotone
    Daniell integral on L_2, Federer 2.5.4(2), p. 96. *)
Theorem plane_continuous_monotone_daniell :
  is_monotone_daniell_integral plane_continuous_lattice plane_section_integral.
Proof.
exact (plane_section_monotone_daniell plane_continuous_lattice_is_lattice
  plane_continuous_lattice_section).
Qed.

(** Source for [first_coordinate_regular_measure_exists]: the L_1 regular
    measure phi_1 associated with lambda_1 by 2.5.2, Federer 2.5.4(1), p. 95 *)
Theorem first_coordinate_regular_measure_exists :
  exists phi : set plane -> \bar R, is_measure phi /\
    is_real_integral_functional phi first_coordinate_lattice plane_section_integral /\
    is_function_lattice_regular first_coordinate_lattice phi.
Proof.
have hne : exists F, first_coordinate_lattice F.
  exists (fun _ : plane => 0), (fun _ : R => 0); split=> // t; exact: cvg_cst.
have [phi [hm [hA [hr _]]]] := monotone_daniell_regular_representation
  first_coordinate_lattice_is_lattice first_coordinate_monotone_daniell hne.
by exists phi.
Qed.

(** Source for [plane_continuous_regular_measure_exists]: the L_2 regular
    measure phi_2 associated with lambda_2 by 2.5.2, Federer 2.5.4(2), p.
    96. *)
Theorem plane_continuous_regular_measure_exists :
  exists phi : set plane -> \bar R, is_measure phi /\
    is_real_integral_functional phi plane_continuous_lattice plane_section_integral /\
    is_function_lattice_regular plane_continuous_lattice phi.
Proof.
have hne : exists F, plane_continuous_lattice F.
  by exists (fun _ : plane => 0)=> x; exact: cvg_cst.
have [phi [hm [hA [hr _]]]] := monotone_daniell_regular_representation
  plane_continuous_lattice_is_lattice plane_continuous_monotone_daniell hne.
by exists phi.
Qed.

(** Source for [riemann_integral_monotone]: the Riemann integral of 2.5.17
    preserves order between continuous functions, supporting the comparison
    of suiting sequences in Federer 2.5.4, pp. 95–96. *)
Lemma riemann_integral_monotone (f h : R -> R) (a b : R) :
  continuous f -> continuous h -> a <= b -> (forall x, a <= x <= b -> f x <= h x) ->
  stieltjes_integral id_fun f a b <= stieltjes_integral id_fun h a b.
Proof.
move=> hf hh hab hle.
have hd : continuous (fun x => h x - f x).
  by move=> x; exact: (@continuousB R R^o R h f x (hh x) (hf x)).
have hs : continuous (fun x => f x + (h x - f x)).
  by move=> x; exact: (@continuousD R R^o R f (fun x => h x - f x) x (hf x) (hd x)).
have heq : (fun x => f x + (h x - f x)) = h by apply/funext=> x; ring.
have := stieltjes_integral_add hg hf hd hs hab; rewrite heq=> ->.
have hpos : forall x, a <= x <= b -> 0 <= h x - f x by move=> x hx; have := hle x hx; lra.
by have := stieltjes_integral_lower_bound hg hmono (m := 0) hd hab hpos; rewrite mul0r; lra.
Qed.

(** Source for [riemann_segment_le_daniell]: for k in K(R)+ the Riemann
    integral over a segment is at most the Riemann integral mu(k) over R of
    2.5.17, supporting the estimate phi_1 <= L^1 o p in Federer 2.5.4(1), p.
    95. *)
Lemma riemann_segment_le_daniell (k : R -> R) (a b : R) :
  KR k -> function_nonnegative k -> a <= b -> stieltjes_integral id_fun k a b <= mu k.
Proof.
move=> hk hk0 hab; have hcont := KR_continuous hk.
have [N0 [hN00 hz0]] := compact_support_bound hk.
have /andP[ha1 ha2] : - `|a| <= a <= `|a| by rewrite -ler_norml.
have /andP[hb1 hb2] : - `|b| <= b <= `|b| by rewrite -ler_norml.
have hna := normr_ge0 a; have hnb := normr_ge0 b.
pose N := N0 + `|a| + `|b| + 1.
have hN0 : 0 <= N by rewrite /N; lra.
have hzN : forall x, k x <> 0 -> `|x| < N by move=> x hx; have := hz0 x hx; rewrite /N; lra.
rewrite -(induced_daniell_eq hg hcont (compact_support_bound hk) hN0 hzN).
have hNa : - N <= a by rewrite /N; lra.
have hbN : b <= N by rewrite /N; lra.
rewrite -(stieltjes_integral_cat hg hcont hNa (le_trans hab hbN)) -(stieltjes_integral_cat hg hcont hab hbN).
have h1 := stieltjes_integral_lower_bound hg hmono (m := 0) hcont hNa (fun x _ => hk0 x).
have h3 := stieltjes_integral_lower_bound hg hmono (m := 0) hcont hbN (fun x _ => hk0 x).
by move: h1 h3; rewrite !mul0r=> h1 h3; lra.
Qed.

(** Source for [interval_bump_one]: the bumps of 2.5.17 equal one on the
    inner segment [a + 1/(n+1), b - 1/(n+1)], supporting Federer 2.5.4, pp.
    95–96. *)
Lemma interval_bump_one (a b t : R) (n : nat) :
  a + n.+1%:R^-1 <= t -> t <= b - n.+1%:R^-1 -> interval_bump a b n t = 1.
Proof.
move=> h1 h2; rewrite /interval_bump.
have hn : (0:R) < n.+1%:R by rewrite ltr0n.
have hmin : n.+1%:R^-1 <= Order.min (t - a) (b - t).
  by move: h1 h2; set d := n.+1%:R^-1=> h1 h2; rewrite le_min; apply/andP; split; lra.
have h : 1 <= n.+1%:R * Order.min (t - a) (b - t).
  by have := ler_wpM2l (ltW hn) hmin; rewrite mulfV ?gt_eqF.
by rewrite (min_l h) max_r // ler01.
Qed.

(** Source for [outside_bump]: the continuous function 1 - (bump of (0, 1)),
    equal to one off (0, 1) and with small integral over [0, 1], which
    covers the part of a set lying over R ~ [0, 1] in the computation of
    Federer 2.5.4, pp. 95–96. *)
Definition outside_bump (n : nat) (t : R) : R := 1 - interval_bump 0 1 n t.

(** Source for [outside_bump_ge0]: nonnegativity of [outside_bump], Federer
    2.5.4, pp. 95–96. *)
Lemma outside_bump_ge0 (n : nat) (t : R) : 0 <= outside_bump n t.
Proof. by rewrite /outside_bump subr_ge0; exact: interval_bump_le1. Qed.

(** Source for [outside_bump_le1]: [outside_bump] is at most one, Federer
    2.5.4, pp. 95–96. *)
Lemma outside_bump_le1 (n : nat) (t : R) : outside_bump n t <= 1.
Proof. by have := interval_bump_ge0 0 1 n t; rewrite /outside_bump; lra. Qed.

(** Source for [outside_bump_one]: [outside_bump] equals one off (0, 1),
    Federer 2.5.4, pp. 95–96. *)
Lemma outside_bump_one (n : nat) (t : R) : ~~ (0 < t < 1) -> outside_bump n t = 1.
Proof. by move=> h; rewrite /outside_bump interval_bump_zero // subr0. Qed.

(** Source for [outside_bump_middle]: [outside_bump] vanishes on the inner
    segment, Federer 2.5.4, pp. 95–96. *)
Lemma outside_bump_middle (n : nat) (t : R) :
  n.+1%:R^-1 <= t -> t <= 1 - n.+1%:R^-1 -> outside_bump n t <= 0.
Proof.
move=> h1 h2; have h1' : 0 + n.+1%:R^-1 <= t by rewrite add0r.
by rewrite /outside_bump (interval_bump_one h1' h2) subrr.
Qed.

(** Source for [outside_bump_continuous]: continuity of [outside_bump],
    Federer 2.5.4, pp. 95–96. *)
Lemma outside_bump_continuous (n : nat) : continuous (outside_bump n).
Proof.
have hb : continuous (interval_bump (0 : R) 1 n) := KR_continuous (interval_bump_member 0 1 n).
have h1 : continuous (fun _ : R => (1 : R)) by move=> t; exact: cvg_cst.
exact (function_lattice_ordered_difference hCR hb h1 (fun t => interval_bump_le1 0 1 n t)).
Qed.

(** Source for [outside_bump_integral]: int_0^1 [outside_bump n] is at most
    2/(n+1), Federer 2.5.4, pp. 95–96. *)
Lemma outside_bump_integral (n : nat) :
  stieltjes_integral id_fun (outside_bump n) 0 1 <= 2 * n.+1%:R^-1.
Proof.
have hcont := @outside_bump_continuous n.
have hd : (0 : R) < n.+1%:R^-1 by rewrite invr_gt0 ltr0n.
have hle1 := outside_bump_le1 n.
have hmid := @outside_bump_middle n.
move: hd hle1 hmid; set d := n.+1%:R^-1=> hd hle1 hmid.
case: (lerP (2 * d) 1)=> h2d.
- have h01 : 0 <= d by exact: ltW.
  have hdd : d <= 1 - d by lra.
  have hd1 : 1 - d <= 1 by lra.
  rewrite -(stieltjes_integral_cat hg hcont h01 (le_trans hdd hd1))
    -(stieltjes_integral_cat hg hcont hdd hd1).
  have h1 := stieltjes_integral_upper_bound hg hmono (M := 1) hcont h01 (fun x _ => hle1 x).
  have h3 := stieltjes_integral_upper_bound hg hmono (M := 1) hcont hd1 (fun x _ => hle1 x).
  have h2 := stieltjes_integral_upper_bound hg hmono (M := 0) hcont hdd
    (fun x hx => hmid x (proj1 (andP hx)) (proj2 (andP hx))).
  by move: h1 h2 h3; rewrite !mul1r mul0r /= => h1 h2 h3; lra.
- have h := stieltjes_integral_upper_bound hg hmono (M := 1) hcont ler01 (fun x _ => hle1 x).
  by move: h; rewrite mul1r /= => h; lra.
Qed.

(** Source for [inside_bump]: the bump of 2.5.17 for the interval (-2/(n+1),
    1 + 2/(n+1)), equal to one on [0, 1], which truncates a function of the
    plane lattices to a member of K(R) in Federer 2.5.4, pp. 95–96. *)
Definition inside_bump (n : nat) : R -> R :=
  interval_bump (- (2 * n.+1%:R^-1)) (1 + 2 * n.+1%:R^-1) n.

(** Source for [inside_bump_one]: [inside_bump] equals one on [0, 1],
    Federer 2.5.4, pp. 95–96. *)
Lemma inside_bump_one (n : nat) (t : R) : 0 <= t <= 1 -> inside_bump n t = 1.
Proof.
move=> /andP[h1 h2]; have hd : (0 : R) < n.+1%:R^-1 by rewrite invr_gt0 ltr0n.
rewrite /inside_bump; move: hd h1 h2; set d := n.+1%:R^-1=> hd h1 h2.
by apply: interval_bump_one; rewrite -/d; lra.
Qed.

(** Source for [truncated_section_support]: the truncation of a nonnegative
    function by [inside_bump] vanishes off (-2/(n+1), 1 + 2/(n+1)), Federer
    2.5.4, pp. 95–96. *)
Lemma truncated_section_support (F : plane -> R) (n : nat) (t : R) :
  function_nonnegative F -> Order.min (F (t, 0)) (inside_bump n t) <> 0 ->
  - (2 * n.+1%:R^-1) < t < 1 + 2 * n.+1%:R^-1.
Proof.
move=> hF0 hne; apply: (interval_bump_support (n := n) (x := t))=> h0; apply: hne.
by rewrite /inside_bump h0 (min_r (hF0 (t, 0))).
Qed.

(** Source for [truncated_section_member]: the truncation of a nonnegative
    function with continuous restriction to the line {x : x_2 = 0} by
    [inside_bump] belongs to K(R), Federer 2.5.4, pp. 95–96. *)
Lemma truncated_section_member (F : plane -> R) (n : nat) :
  continuous (fun t => F (t, 0)) -> function_nonnegative F ->
  KR (fun t => Order.min (F (t, 0)) (inside_bump n t)).
Proof.
move=> hF hF0; split.
  exact (function_lattice_minimum hCR hF
    (KR_continuous (interval_bump_member (- (2 * n.+1%:R^-1)) (1 + 2 * n.+1%:R^-1) n))).
rewrite /real_function_support.
apply: (subclosed_compact (@closed_closure _ [set x | Order.min (F (x, 0)) (inside_bump n x) <> 0])
  (@segment_compact R (- (2 * n.+1%:R^-1)) (1 + 2 * n.+1%:R^-1))).
rewrite [X in _ `<=` X]((closure_id _).1 (@segment_closed_real R _ _)).
apply: closureS=> x hx; have /andP[h1 h2] := truncated_section_support hF0 hx.
by rewrite /= in_itv /= (ltW h1) (ltW h2).
Qed.

(** Source for [vanishing_bump]: the functions s |-> min{(m+1)|s|, 1},
    increasing to one off s = 0 and vanishing at s = 0, which cover the part
    of a set off the line {x : x_2 = 0} in the computation of phi_2 in
    Federer 2.5.4(2), p. 96. *)
Definition vanishing_bump (m : nat) (s : R) : R := Order.min (m.+1%:R * `|s|) 1.

(** Source for [vanishing_bump_ge0]: nonnegativity of [vanishing_bump],
    Federer 2.5.4(2), p. 96. *)
Lemma vanishing_bump_ge0 (m : nat) (s : R) : 0 <= vanishing_bump m s.
Proof. by rewrite /vanishing_bump le_min ler01 andbT mulr_ge0 ?ler0n ?normr_ge0. Qed.

(** Source for [vanishing_bump_zero]: [vanishing_bump] vanishes at zero,
    Federer 2.5.4(2), p. 96. *)
Lemma vanishing_bump_zero (m : nat) : vanishing_bump m 0 = 0.
Proof. by rewrite /vanishing_bump normr0 mulr0 min_l // ler01. Qed.

(** Source for [vanishing_bump_monotone]: [vanishing_bump] increases with m,
    Federer 2.5.4(2), p. 96. *)
Lemma vanishing_bump_monotone (m m' : nat) (s : R) :
  (m <= m')%N -> vanishing_bump m s <= vanishing_bump m' s.
Proof.
move=> h; rewrite /vanishing_bump le_min; apply/andP; split; last by rewrite ge_min lexx orbT.
rewrite ge_min; apply/orP; left; apply: (ler_wpM2r (normr_ge0 s)).
by rewrite ler_nat.
Qed.

(** Source for [vanishing_bump_continuous]: continuity of [vanishing_bump],
    Federer 2.5.4(2), p. 96. *)
Lemma vanishing_bump_continuous (m : nat) : continuous (vanishing_bump m).
Proof.
exact (function_lattice_truncation hCR ler01
  (continuous_scale (c := m.+1%:R) absolute_value_continuous)).
Qed.

(** Source for [vanishing_bump_limit]: off zero some [vanishing_bump] equals
    one, by the Archimedean property, Federer 2.5.4(2), p. 96. *)
Lemma vanishing_bump_limit (s : R) : s != 0 -> exists m, vanishing_bump m s = 1.
Proof.
move=> hs; have hpos : 0 < `|s| by rewrite normr_gt0.
have [m hm] := real_reciprocal_below hpos.
have hn : (0:R) < m.+1%:R by rewrite ltr0n.
exists m; rewrite /vanishing_bump min_r //.
by rewrite -(ltr_pM2l hn) mulfV ?gt_eqF // in hm; exact: ltW.
Qed.

(** Source for [sequence_cost_compare]: if the values of one functional
    along a sequence are bounded by the values of another along a second
    sequence plus e, then the cost of the first sequence, in the sense of
    2.5.2, is at most the cost of the second plus e, Federer 2.5.4, pp.
    95–96. *)
Lemma sequence_cost_compare (X Y : Type) (A : (X -> R) -> R) (A' : (Y -> R) -> R)
    (f : nat -> X -> R) (k : nat -> Y -> R) (c : \bar R) (e : R) :
  is_daniell_sequence_cost A' k c -> (forall m, A (f m) <= A' (k m) + e) ->
  exists c' : \bar R, is_daniell_sequence_cost A f c' /\ (c' <= c + e%:E)%E.
Proof.
move=> hc hle.
exists (extended_real_sup [set z | exists m, z = (A (f m))%:E]); split.
  by split; [exact: extended_real_sup_upper | exact: extended_real_sup_least].
apply: extended_real_sup_least=> _ [m ->].
have h1 : ((A' (k m))%:E <= c)%E := extended_real_supremum_upper hc (ex_intro _ m erefl).
apply: le_trans _ (leeD h1 (lexx e%:E)); rewrite -EFinD lee_fin; exact: hle.
Qed.

(** Source for [plane_section_measure_upper]: phi(S) <= L^1(B) for the
    regular measure phi of a plane lattice whenever every suiting sequence
    of K(R) for B yields suiting sequences of the lattice for S bounded by
    it plus [outside_bump], Federer 2.5.4, pp. 95–96, by the envelope
    formula of 2.5.2. *)
Lemma plane_section_measure_upper (L : set (plane -> R)) (hL : is_function_lattice L)
    (hsec : forall F, L F -> continuous (fun t => F (t, 0)))
    (phi : set plane -> \bar R) (hm : is_measure phi)
    (hA : is_real_integral_functional phi L plane_section_integral)
    (hr : is_function_lattice_regular L phi)
    (L1 : set R -> \bar R) (hm1 : is_measure L1) (hr1 : is_function_lattice_regular KR L1)
    (hA1 : is_real_integral_functional L1 KR mu) (S : set plane) (B : set R) :
  (forall k, is_daniell_suiting_sequence KR B k -> forall n, exists f,
     is_daniell_suiting_sequence L S f /\ forall m t, f m (t, 0) <= k m t + outside_bump n t) ->
  (phi S <= L1 B)%E.
Proof.
move=> hconstr.
have henv := regular_representing_measure_envelope hL hm hA hr.
have henv1 := regular_representing_measure_envelope hKR hm1 hA1 hr1.
apply: (daniell_cover_greatest henv1)=> k c hk hc.
apply/lee_addgt0Pr=> e he.
have he2 : 0 < e / 2 by lra.
have [n hn] := real_reciprocal_below he2.
pose d : R := n.+1%:R^-1; rewrite -/d in hn.
have [f [hf hfk]] := hconstr k hk n.
have [hkpos _] := hk.
have [hfpos _] := hf.
have hcost : forall m, plane_section_integral (f m) <= mu (k m) + 2 * d.
  move=> m.
  have hkc := KR_continuous (hkpos m).1.
  have hwc := @outside_bump_continuous n.
  have hsum : continuous (fun t => k m t + outside_bump n t).
    by move=> t; exact: (@continuousD R R^o R (k m) (outside_bump n) t (hkc t) (hwc t)).
  have e1 : plane_section_integral (f m)
      <= stieltjes_integral id_fun (fun t => k m t + outside_bump n t) 0 1.
    exact (riemann_integral_monotone (hsec _ (hfpos m).1) hsum ler01 (fun t _ => hfk m t)).
  have e2 := stieltjes_integral_add hg hkc hwc hsum ler01.
  have e3 := riemann_segment_le_daniell (hkpos m).1 (hkpos m).2 ler01.
  have e4 := outside_bump_integral n.
  by rewrite -/d in e4; lra.
have [c' [hc' hc'le]] :=
  sequence_cost_compare (A := plane_section_integral) (A' := mu) hc hcost.
apply: le_trans (daniell_cover_lower henv hf hc') _.
by apply: le_trans hc'le _; apply: (leeD (lexx _)); rewrite lee_fin; lra.
Qed.

(** Source for [plane_section_measure_lower]: L^1(B) <= phi(S) for the
    regular measure phi of a plane lattice whenever B subset [0, 1] and
    every suiting sequence of the lattice for S, restricted to the line {x :
    x_2 = 0}, reaches one on B, Federer 2.5.4, pp. 95–96, by the envelope
    formula of 2.5.2 and truncation by [inside_bump]. *)
Lemma plane_section_measure_lower (L : set (plane -> R)) (hL : is_function_lattice L)
    (hsec : forall F, L F -> continuous (fun t => F (t, 0)))
    (phi : set plane -> \bar R) (hm : is_measure phi)
    (hA : is_real_integral_functional phi L plane_section_integral)
    (hr : is_function_lattice_regular L phi)
    (L1 : set R -> \bar R) (hm1 : is_measure L1) (hr1 : is_function_lattice_regular KR L1)
    (hA1 : is_real_integral_functional L1 KR mu) (S : set plane) (B : set R) :
  B `<=` `[0, 1] ->
  (forall f, is_daniell_suiting_sequence L S f ->
     forall t, B t -> forall r, r < 1 -> exists m, r < f m (t, 0)) ->
  (L1 B <= phi S)%E.
Proof.
move=> hB01 hBS.
have henv := regular_representing_measure_envelope hL hm hA hr.
have henv1 := regular_representing_measure_envelope hKR hm1 hA1 hr1.
apply: (daniell_cover_greatest henv)=> f c hf hc.
apply/lee_addgt0Pr=> e he.
have he4 : 0 < e / 4 by lra.
have [n hn] := real_reciprocal_below he4.
pose d : R := n.+1%:R^-1; rewrite -/d in hn.
have hd : 0 < d by rewrite /d invr_gt0 ltr0n.
have [hfpos [hfmon hflim]] := hf.
pose k := fun m t => Order.min (f m (t, 0)) (inside_bump n t).
have hk : is_daniell_suiting_sequence KR B k.
  split; last split.
  - move=> m; split; first exact (truncated_section_member n (hsec _ (hfpos m).1) (hfpos m).2).
    move=> t; rewrite /k le_min (hfpos m).2 andTb; exact: interval_bump_ge0.
  - move=> m m' hmm' t; rewrite /k le_min; apply/andP; split.
      by rewrite ge_min (hfmon m m' hmm' (t, 0)).
    by rewrite ge_min lexx orbT.
  - move=> t ht r hlt1.
    have [m hmm] := hBS f hf t ht r hlt1.
    exists m; rewrite /k lt_min hmm andTb inside_bump_one //.
    by move: (hB01 t ht); rewrite /= in_itv /=.
have hcost : forall m, mu (k m) <= plane_section_integral (f m) + 4 * d.
  move=> m.
  have hFc : continuous (fun t => f m (t, 0)) := hsec _ (hfpos m).1.
  have hF0 : function_nonnegative (f m) := (hfpos m).2.
  have hkm : KR (k m) := truncated_section_member n hFc hF0.
  have hkc := KR_continuous hkm.
  have hz : forall t, k m t <> 0 -> - (2 * d) < t < 1 + 2 * d.
    by move=> t ht; exact: (truncated_section_support hF0 ht).
  have hab : - (2 * d) <= 1 + 2 * d by lra.
  rewrite (induced_daniell_value hg hkm hab hz).
  have h0 : - (2 * d) <= 0 by lra.
  have h1 : (1 : R) <= 1 + 2 * d by lra.
  rewrite -(stieltjes_integral_cat hg hkc h0 (le_trans ler01 h1))
    -(stieltjes_integral_cat hg hkc ler01 h1).
  have hk1 : forall t, k m t <= 1.
    by move=> t; rewrite /k ge_min; apply/orP; right; exact: interval_bump_le1.
  have e1 := stieltjes_integral_upper_bound hg hmono (M := 1) hkc h0 (fun t _ => hk1 t).
  have e3 := stieltjes_integral_upper_bound hg hmono (M := 1) hkc h1 (fun t _ => hk1 t).
  have e2 : stieltjes_integral id_fun (k m) 0 1 <= plane_section_integral (f m).
    apply: (riemann_integral_monotone hkc hFc ler01)=> t _.
    by rewrite /k ge_min lexx.
  by move: e1 e2 e3; rewrite !mul1r /= => e1 e2 e3; lra.
have [c' [hc' hc'le]] :=
  sequence_cost_compare (A := mu) (A' := plane_section_integral) hc hcost.
apply: le_trans (daniell_cover_lower henv1 hk hc') _.
by apply: le_trans hc'le _; apply: (leeD (lexx _)); rewrite lee_fin; lra.
Qed.

(** Source for [first_coordinate_cover]: from a sequence of K(R)+ suiting
    p(S) cap [0, 1], the functions max{k_m o p, w o p} with w =
    [outside_bump] form a sequence of L_1+ suiting S, Federer 2.5.4(1), p.
    95 *)
Lemma first_coordinate_cover (S : set plane) (k : nat -> R -> R) (n : nat) :
  is_daniell_suiting_sequence KR ((fst @` S) `&` `[0, 1]) k ->
  exists f, is_daniell_suiting_sequence first_coordinate_lattice S f /\
    forall m t, f m (t, 0) <= k m t + outside_bump n t.
Proof.
move=> [hkpos [hkmon hklim]].
exists (fun m x => Order.max (k m x.1) (outside_bump n x.1)); split; last first.
  move=> m t; rewrite /= ge_max; apply/andP; split.
    by rewrite lerDl; exact: outside_bump_ge0.
  by rewrite lerDr; exact: (hkpos m).2.
split; last split.
- move=> m; split.
    exists (fun t => Order.max (k m t) (outside_bump n t)); split=> //.
    exact (function_lattice_maximum hCR (KR_continuous (hkpos m).1) (@outside_bump_continuous n)).
  by move=> x; rewrite le_max (hkpos m).2.
- move=> m m' hmm' x; rewrite ge_max; apply/andP; split.
    by rewrite le_max (hkmon m m' hmm' x.1).
  by rewrite le_max lexx orbT.
- move=> x hx r hr; case: (boolP (0 <= x.1 <= 1))=> [h01|hout].
    have hB : ((fst @` S) `&` `[0, 1]) x.1 by split; [exists x | rewrite /= in_itv /=].
    have [m hm] := hklim x.1 hB r hr.
    by exists m; rewrite lt_max hm.
  exists 0%N; rewrite lt_max; apply/orP; right.
  rewrite outside_bump_one //; apply: contra hout=> /andP[h1 h2].
  by apply/andP; split; exact: ltW.
Qed.

(** Source for [first_coordinate_section_limit]: a sequence of L_1+ suiting
    S reaches one, along the line {x : x_2 = 0}, on p(S) cap [0, 1], Federer
    2.5.4(1), p. 95 *)
Lemma first_coordinate_section_limit (S : set plane) (f : nat -> plane -> R) :
  is_daniell_suiting_sequence first_coordinate_lattice S f ->
  forall t, ((fst @` S) `&` `[0, 1]) t -> forall r, r < 1 -> exists m, r < f m (t, 0).
Proof.
move=> [hfpos [_ hflim]] t [[x hx <-] _] r hr.
have [m hm] := hflim x hx r hr; exists m.
have [u [_ hu]] := (hfpos m).1.
by move: hm; rewrite hu.
Qed.

(** Source for [plane_continuous_cover]: from a sequence of K(R)+ suiting
    xi^{-1}(S) cap [0, 1], the functions max{k_m(x_1), w(x_1), v_m(x_2)}
    with w = [outside_bump] and v_m = [vanishing_bump] form a sequence of
    L_2+ suiting S, Federer 2.5.4(2), p. 96. *)
Lemma plane_continuous_cover (S : set plane) (k : nat -> R -> R) (n : nat) :
  is_daniell_suiting_sequence KR ([set t | S (t, 0)] `&` `[0, 1]) k ->
  exists f, is_daniell_suiting_sequence plane_continuous_lattice S f /\
    forall m t, f m (t, 0) <= k m t + outside_bump n t.
Proof.
move=> [hkpos [hkmon hklim]].
have hL2 := plane_continuous_lattice_is_lattice.
exists (fun m x => Order.max (Order.max (k m x.1) (outside_bump n x.1)) (vanishing_bump m x.2)).
split; last first.
  move=> m t; rewrite /= vanishing_bump_zero ge_max; apply/andP; split; last first.
    by rewrite addr_ge0 ?(hkpos m).2 ?outside_bump_ge0.
  rewrite ge_max; apply/andP; split.
    by rewrite lerDl; exact: outside_bump_ge0.
  by rewrite lerDr; exact: (hkpos m).2.
split; last split.
- move=> m; split.
    apply: (function_lattice_maximum hL2); last first.
      exact (second_coordinate_continuous (@vanishing_bump_continuous m)).
    apply: (function_lattice_maximum hL2).
      exact (first_coordinate_continuous (KR_continuous (hkpos m).1)).
    exact (first_coordinate_continuous (@outside_bump_continuous n)).
  by move=> x; rewrite !le_max (hkpos m).2.
- move=> m m' hmm' x; rewrite ge_max; apply/andP; split.
    rewrite le_max; apply/orP; left; rewrite ge_max; apply/andP; split.
      by rewrite le_max (hkmon m m' hmm' x.1).
    by rewrite le_max lexx orbT.
  by rewrite le_max (vanishing_bump_monotone x.2 hmm') orbT.
- move=> x hx r hr; case: (eqVneq x.2 0)=> [hx2|hx2].
    have hx' : S (x.1, 0) by move: hx; rewrite {1}(surjective_pairing x) hx2.
    case: (boolP (0 <= x.1 <= 1))=> [h01|hout].
      have hB : ([set t | S (t, 0)] `&` `[0, 1]) x.1 by split; [exact: hx' | rewrite /= in_itv /=].
      have [m hm] := hklim x.1 hB r hr.
      by exists m; rewrite !lt_max hm.
    exists 0%N; rewrite lt_max; apply/orP; left; rewrite lt_max; apply/orP; right.
    rewrite outside_bump_one //; apply: contra hout=> /andP[h1 h2].
    by apply/andP; split; exact: ltW.
  have [m hm] := vanishing_bump_limit hx2.
  by exists m; rewrite lt_max hm hr orbT.
Qed.

(** Source for [plane_continuous_section_limit]: a sequence of L_2+ suiting
    S reaches one, along the line {x : x_2 = 0}, on xi^{-1}(S) cap [0, 1],
    Federer 2.5.4(2), p. 96. *)
Lemma plane_continuous_section_limit (S : set plane) (f : nat -> plane -> R) :
  is_daniell_suiting_sequence plane_continuous_lattice S f ->
  forall t, ([set t | S (t, 0)] `&` `[0, 1]) t -> forall r, r < 1 -> exists m, r < f m (t, 0).
Proof. by move=> [_ [_ hflim]] t [hS _] r hr; exact: hflim. Qed.

(** Source for [first_coordinate_regular_measure_value]: the displayed
    equation phi_1(A) = L^1[p(A) cap {t : 0 <= t <= 1}] whenever A subset
    R^2, Federer 2.5.4(1), p. 95 Here phi_1 is any L_1 regular measure
    representing lambda_1 and L^1 any K(R) regular measure representing the
    Riemann integral. *)
Theorem first_coordinate_regular_measure_value (phi : set plane -> \bar R) (L1 : set R -> \bar R) :
  is_measure phi -> is_real_integral_functional phi first_coordinate_lattice plane_section_integral ->
  is_function_lattice_regular first_coordinate_lattice phi ->
  is_measure L1 -> is_function_lattice_regular KR L1 -> is_real_integral_functional L1 KR mu ->
  forall S : set plane, phi S = L1 ((fst @` S) `&` `[0, 1]).
Proof.
move=> hm hA hr hm1 hr1 hA1 S; apply/le_anti/andP; split.
- apply: (plane_section_measure_upper first_coordinate_lattice_is_lattice
    first_coordinate_lattice_section hm hA hr hm1 hr1 hA1).
  by move=> k hk n; exact: (first_coordinate_cover n hk).
- apply: (plane_section_measure_lower first_coordinate_lattice_is_lattice
    first_coordinate_lattice_section hm hA hr hm1 hr1 hA1).
    by move=> t [_ ht].
  by move=> f hf; exact: (first_coordinate_section_limit hf).
Qed.

(** Source for [plane_continuous_regular_measure_value]: the displayed
    equation phi_2(A) = L^1[xi^{-1}(A) cap {t : 0 <= t <= 1}] whenever A
    subset R^2, Federer 2.5.4(2), p. 96. Here phi_2 is any L_2 regular
    measure representing lambda_2 and L^1 any K(R) regular measure
    representing the Riemann integral. *)
Theorem plane_continuous_regular_measure_value (phi : set plane -> \bar R) (L1 : set R -> \bar R) :
  is_measure phi -> is_real_integral_functional phi plane_continuous_lattice plane_section_integral ->
  is_function_lattice_regular plane_continuous_lattice phi ->
  is_measure L1 -> is_function_lattice_regular KR L1 -> is_real_integral_functional L1 KR mu ->
  forall S : set plane, phi S = L1 ([set t | S (t, 0)] `&` `[0, 1]).
Proof.
move=> hm hA hr hm1 hr1 hA1 S; apply/le_anti/andP; split.
- apply: (plane_section_measure_upper plane_continuous_lattice_is_lattice
    plane_continuous_lattice_section hm hA hr hm1 hr1 hA1).
  by move=> k hk n; exact: (plane_continuous_cover n hk).
- apply: (plane_section_measure_lower plane_continuous_lattice_is_lattice
    plane_continuous_lattice_section hm hA hr hm1 hr1 hA1).
    by move=> t [_ ht].
  by move=> f hf; exact: (plane_continuous_section_limit hf).
Qed.

(** Source for [plane_continuous_measure_represents_first]: since L_1 subset
    L_2 and lambda_1 = lambda_2|L_1, the conclusion of 2.5.2 holds with L_1,
    lambda_1 and phi_2, Federer 2.5.4, p. 96, last paragraph. *)
Theorem plane_continuous_measure_represents_first (phi : set plane -> \bar R) :
  is_real_integral_functional phi plane_continuous_lattice plane_section_integral ->
  is_real_integral_functional phi first_coordinate_lattice plane_section_integral.
Proof. by move=> hA F hF; exact: (hA F (first_coordinate_lattice_subset hF)). Qed.

(** Source for [upper_half_plane_not_measurable]: the Borel set {x : x_2 >=
    0} is not phi_1 measurable, Federer 2.5.4, p. 96, last paragraph, tested
    with the two segments [0, 1] x {1} and [0, 1] x {-1}. *)
Theorem upper_half_plane_not_measurable (phi : set plane -> \bar R) (L1 : set R -> \bar R) :
  is_measure phi -> is_real_integral_functional phi first_coordinate_lattice plane_section_integral ->
  is_function_lattice_regular first_coordinate_lattice phi ->
  is_measure L1 -> is_function_lattice_regular KR L1 -> is_real_integral_functional L1 KR mu ->
  (forall a b : R, a <= b -> L1 `[a, b] = (b - a)%:E) ->
  ~ measure_measurable phi [set x : plane | 0 <= x.2].
Proof.
move=> hm hA hr hm1 hr1 hA1 hseg hmeas.
pose T := [set x : plane | 0 <= x.1 <= 1 /\ (x.2 = 1 \/ x.2 = -1)].
have hv := first_coordinate_regular_measure_value hm hA hr hm1 hr1 hA1.
have hT : (fst @` T) `&` `[0, 1] = `[0, 1].
  apply/seteqP; split=> t; first by move=> [_ ht].
  move=> ht; split=> //; exists (t, 1); last by [].
  by split; [move: ht; rewrite /= in_itv /= | left].
have hTH : (fst @` (T `&` [set x : plane | 0 <= x.2])) `&` `[0, 1] = `[0, 1].
  apply/seteqP; split=> t; first by move=> [_ ht].
  move=> ht; split=> //; exists (t, 1); last by [].
  split; last by rewrite /=; exact: ler01.
  by split; [move: ht; rewrite /= in_itv /= | left].
have hTD : (fst @` (T `\` [set x : plane | 0 <= x.2])) `&` `[0, 1] = `[0, 1].
  apply/seteqP; split=> t; first by move=> [_ ht].
  move=> ht; split=> //; exists (t, -1); last by [].
  split; last by move=> h; have h' : (0 : R) <= -1 := h; move: h'; rewrite oppr_ge0 ler10.
  by split; [move: ht; rewrite /= in_itv /= | right].
have h := hmeas T; rewrite !hv hT hTH hTD (hseg 0 1 ler01) -EFinD in h.
have h' := EFin_inj h; move: h'; rewrite !subr0=> /esym/eqP.
by rewrite -subr_eq0 addrK oner_eq0.
Qed.

(** Source for [plane_continuous_measure_not_first_regular]: phi_2 is not
    L_1 regular, Federer 2.5.4, p. 96, last paragraph: an L_1 regular
    measure representing lambda_1 gives the segment [0, 1] x {1} the value
    one, whereas phi_2 gives it the value zero. *)
Theorem plane_continuous_measure_not_first_regular (phi : set plane -> \bar R)
    (L1 : set R -> \bar R) :
  is_measure phi -> is_real_integral_functional phi plane_continuous_lattice plane_section_integral ->
  is_function_lattice_regular plane_continuous_lattice phi ->
  is_measure L1 -> is_function_lattice_regular KR L1 -> is_real_integral_functional L1 KR mu ->
  (forall a b : R, a <= b -> L1 `[a, b] = (b - a)%:E) ->
  ~ is_function_lattice_regular first_coordinate_lattice phi.
Proof.
move=> hm hA2 hr2 hm1 hr1 hA1 hseg hr.
have hA1' := plane_continuous_measure_represents_first hA2.
pose S := [set x : plane | 0 <= x.1 <= 1 /\ x.2 = 1].
have h1 := first_coordinate_regular_measure_value hm hA1' hr hm1 hr1 hA1 S.
have h2 := plane_continuous_regular_measure_value hm hA2 hr2 hm1 hr1 hA1 S.
have hS1 : (fst @` S) `&` `[0, 1] = `[0, 1].
  apply/seteqP; split=> t; first by move=> [_ ht].
  move=> ht; split=> //; exists (t, 1); last by [].
  by split=> //; move: ht; rewrite /= in_itv /=.
have hS2 : [set t | S (t, 0)] `&` `[0, 1] = set0.
  apply/seteqP; split=> t; last by [].
  by move=> [[_ h] _]; have /eqP := (h : (0 : R) = 1); rewrite eq_sym oner_eq0.
move: h1; rewrite h2 hS1 hS2 (hseg 0 1 ler01) (measure_empty hm1) subr0=> h.
have h' := EFin_inj h; move/eqP: h'.
by rewrite eq_sym oner_eq0.
Qed.

(** Source for [first_coordinate_example]: the first example of Federer
    2.5.4, p. 95, assembled: an L_1 regular measure phi_1 representing
    lambda_1 and a Lebesgue measure L^1 with phi_1(A) = L^1[p(A) cap {t : 0
    <= t <= 1}] for all A subset R^2, and {x : x_2 >= 0} not phi_1
    measurable *)
Theorem first_coordinate_example :
  exists (phi : set plane -> \bar R) (L1 : set R -> \bar R),
    is_measure phi /\ is_real_integral_functional phi first_coordinate_lattice plane_section_integral /\
    is_function_lattice_regular first_coordinate_lattice phi /\
    is_measure L1 /\ (forall a b : R, a <= b -> L1 `[a, b] = (b - a)%:E) /\
    (forall S : set plane, phi S = L1 ((fst @` S) `&` `[0, 1])) /\
    ~ measure_measurable phi [set x : plane | 0 <= x.2].
Proof.
have [phi [hm [hA hr]]] := first_coordinate_regular_measure_exists.
have [L1 [hm1 [hr1 [hA1 [_ hseg]]]]] := @lebesgue_line_measure_exists R.
exists phi, L1; split=> //; split=> //; split=> //; split=> //; split=> //; split.
  exact (first_coordinate_regular_measure_value hm hA hr hm1 hr1 hA1).
exact (upper_half_plane_not_measurable hm hA hr hm1 hr1 hA1 hseg).
Qed.

(** Source for [plane_continuous_example]: the second example of Federer
    2.5.4, p. 96, assembled: an L_2 regular measure phi_2 representing
    lambda_2 and a Lebesgue measure L^1 with phi_2(A) = L^1[xi^{-1}(A) cap
    {t : 0 <= t <= 1}] for all A subset R^2, phi_2 representing lambda_1 on
    L_1, and phi_2 not L_1 regular. *)
Theorem plane_continuous_example :
  exists (phi : set plane -> \bar R) (L1 : set R -> \bar R),
    is_measure phi /\ is_real_integral_functional phi plane_continuous_lattice plane_section_integral /\
    is_function_lattice_regular plane_continuous_lattice phi /\
    is_measure L1 /\ (forall a b : R, a <= b -> L1 `[a, b] = (b - a)%:E) /\
    (forall S : set plane, phi S = L1 ([set t | S (t, 0)] `&` `[0, 1])) /\
    is_real_integral_functional phi first_coordinate_lattice plane_section_integral /\
    ~ is_function_lattice_regular first_coordinate_lattice phi.
Proof.
have [phi [hm [hA hr]]] := plane_continuous_regular_measure_exists.
have [L1 [hm1 [hr1 [hA1 [_ hseg]]]]] := @lebesgue_line_measure_exists R.
exists phi, L1; split=> //; split=> //; split=> //; split=> //; split=> //; split.
  exact (plane_continuous_regular_measure_value hm hA hr hm1 hr1 hA1).
split; first exact (plane_continuous_measure_represents_first hA).
exact (plane_continuous_measure_not_first_regular hm hA hr hm1 hr1 hA1 hseg).
Qed.

End PlaneExamples.
