(** Federer (1969), 2.7.14, printed pp. 131–133, proof of "Every left
    (right) chi covariant measure over G is a Radon measure": "Suppose alpha
    is the K(G) regular measure associated with a monotone left chi
    covariant integral lambda. In view of 2.5.3, 2.5.14 we need to show
    that, if U is any nonempty open subset of G with compact closure, then U
    is alpha measurable." This module proves that assertion. It follows
    Federer's choice of objects: the class Phi = K(G)+ cap {f: f <= u}, u
    the characteristic function of U; a countable subset Psi of Phi with sup
    lambda(Phi) = sup lambda(Psi), written as a sequence f_0, f_1, ... with
    lambda(w) <= lambda(f_n) + 1/(n+1) whenever w in Phi; the closed
    subgroup S = G cap {s: f(t s) = f(t) whenever f in Psi, t in G}, which
    is compact; the pseudometrics rho_f(g,h) = sup{|f(t g) - f(t h)|: t in
    G}; a countable subset Omega of Phi with U subset Union_{omega in Omega}
    {g: omega(g) > 0} . S; the alpha measurable set P = Intersection_{f in
    Psi} {g: f(g) = 0}; and the decomposition U = (G ~ P) cup (P cap U). The
    proof departs from the printed route in three places, recorded in
    DOC.md. First, the quotient X = G/S and its metric sum_{f in Psi}
    epsilon(f) sigma_f are not formed: the finitely many pseudometrics
    rho_{f_0}, ..., rho_{f_{n-1}} are used directly on G, the finite
    intersection argument of p. 132 shows that every open set W with W . S =
    W contains a ball for them about each of its points, and the compactness
    of Clos U gives finitely many balls of each radius covering it; this
    replaces "the topology of A^x(U) has a countable base". Second, the
    computation of integral p . [mu^x(omega) o A^x] d alpha through a Haar
    measure beta of S and Fubini's theorem is replaced by measure estimates:
    for omega in Phi and s in S the set P cap {g: omega(g s) > 0} is alpha
    null, because the function sup{omega(. s), f_n} - f_n of K(G)+ exceeds
    omega(g s) on P and has integral at most 1/(n+1), by the right
    invariance lambda_g u(g s) = lambda(u) for s in S (the remark "Delta_G
    and chi map the compact subgroup S onto {1}",
    CovariantCompactRightInvariance.v) and Chebyshev's inequality for the
    levels of lambda (2.5.3); a finite cover of the compact set {omega >= t}
    . S by the open sets {g: omega(g s^{-1}) > 0}, s in S, then shows that P
    cap ({omega > 0} . S) is alpha null. Third, Federer's display "U = (X ~
    P) cup (P cap U)" is read with G in place of X, since P is a subset of
    G. The right invariance is a hypothesis of this module, so that only the
    monotonicity of lambda, its representation by alpha and that invariance
    are used; alpha need not be K(G) regular here. The local erratum has no
    entry for pp. 131–133. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets cardinality
  functions reals constructive_ereal topology normedtype.
From mathcomp Require Import lra.
From Federer Require Import RealMetricBackground CountableOrderIntervals FunctionLatticeUP
  MonotoneDaniellIntegralUP MonotoneDaniellIntegralLaws CompactSupportFunctionUP
  CompactSupportFunctionLattice CompactCutoffUP CompactCutoff LocalizedCompactCutoffUP
  LocalizedCompactCutoff CompactFiniteCover FunctionLatticeLevelFamilies
  FunctionLatticeLevelMeasurability RealIntegralFunctionalUP MeasureUP MeasureBasic
  MeasureAlmostBasic MeasureFiniteClosure MeasureCountableClosure ExtendedRealReciprocalBounds
  TopologicalGroupUP TopologicalGroupLaws HaarIntegralUP GroupMultiplicationHomogeneous
  CovariantIntegralLaws UniformActionUP GroupUniformity UniformityCompactSupport.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [real_strict_upper_level_open]: the sets {x: t < f(x)}
    of a continuous real function are open, used for the open sets
    {g: omega(g) > 0} in the proof of Federer 2.7.14, p. 132.
    Supporting lemma. *)
Lemma real_strict_upper_level_open (R : realType) (T : topologicalType) (f : T -> R) (t : R) :
  continuous (f : T -> real_line_metric R) -> open [set x | t < f x].
Proof.
move=> hf.
exact ((@continuousP T (real_line_metric R) f).1 hf _
  (@order_strict_upper_ray_open _ [the orderTopologicalType _ of R^o] t)).
Qed.

(** Source for [real_strict_lower_level_open]: the sets {x: f(x) < t}
    of a continuous real function are open, supporting the pseudometric
    balls in the proof of Federer 2.7.14, p. 131. Supporting lemma. *)
Lemma real_strict_lower_level_open (R : realType) (T : topologicalType) (f : T -> R) (t : R) :
  continuous (f : T -> real_line_metric R) -> open [set x | f x < t].
Proof.
move=> hf.
exact ((@continuousP T (real_line_metric R) f).1 hf _
  (@order_strict_lower_ray_open _ [the orderTopologicalType _ of R^o] t)).
Qed.

(** Source for [real_closed_upper_level_closed]: the sets {x: t <= f(x)}
    of a continuous real function are closed, supporting the compact sets
    of the proof of Federer 2.7.14, p. 131. Supporting lemma. *)
Lemma real_closed_upper_level_closed (R : realType) (T : topologicalType) (f : T -> R) (t : R) :
  continuous (f : T -> real_line_metric R) -> closed [set x | t <= f x].
Proof.
move=> hf.
exact ((@continuous_closedP T (real_line_metric R) f).1 hf _
  (@order_closed_upper_ray_closed _ [the orderTopologicalType _ of R^o] t)).
Qed.

(** Source for [real_closed_lower_level_closed]: the sets {x: f(x) <= t}
    of a continuous real function are closed, supporting the compact sets
    of the proof of Federer 2.7.14, p. 131. Supporting lemma. *)
Lemma real_closed_lower_level_closed (R : realType) (T : topologicalType) (f : T -> R) (t : R) :
  continuous (f : T -> real_line_metric R) -> closed [set x | f x <= t].
Proof.
move=> hf.
exact ((@continuous_closedP T (real_line_metric R) f).1 hf _
  (@order_closed_lower_ray_closed _ [the orderTopologicalType _ of R^o] t)).
Qed.

(** Source for [real_lt_dist_split]: c < |a - b| if and only if
    b < a - c or a + c < b, supporting the open sets
    {h: rho_f(g,h) > r} in the proof of Federer 2.7.14, p. 132.
    Supporting lemma. *)
Lemma real_lt_dist_split (R : realType) (a b c : R) :
  c < `|a - b| <-> b < a - c \/ a + c < b.
Proof.
rewrite ltr_normr opprB !ltrBrDr (addrC c b) (addrC c a).
by split=> /orP.
Qed.

(** Source for [nat_reciprocal_positive]: 1/(n+1) > 0, supporting the
    radii and error terms of the proof of Federer 2.7.14, pp. 131–132.
    Supporting lemma. *)
Lemma nat_reciprocal_positive (R : realType) n : 0 < (n.+1%:R : R)^-1.
Proof. by rewrite invr_gt0 ltr0n. Qed.

(** Source for [extended_null_of_small_bounds]: if d a <= 1/(n+1) for
    every n, with d > 0 and a >= 0 in the extended reals, then a = 0;
    supporting "therefore integral p omega d alpha = 0", Federer 2.7.14,
    p. 132. Supporting lemma. *)
Lemma extended_null_of_small_bounds (R : realType) (d : R) (a : \bar R) :
  0 < d -> (0 <= a)%E -> (forall n, (d%:E * a <= ((n.+1%:R)^-1)%:E)%E) -> a = 0%E.
Proof.
move=> hd ha hb; case: a ha hb=> [r| |] ha hb.
- have hr : 0 <= r by rewrite -lee_fin.
  have [->|hne] := eqVneq r 0; first by [].
  have hpos : 0 < d * r by apply: mulr_gt0=> //; rewrite lt_def hne hr.
  have [n hn] := positive_reciprocal_nat_small hpos.
  have := hb n; rewrite -EFinM lee_fin=> h.
  by have := lt_le_trans hn h; rewrite ltxx.
- by have := hb 0%N; rewrite mulry gtr0_sg // mul1e leye_eq.
- by [].
Qed.

Section CovariantMeasureOpenMeasurability.
Variable R : realType.
Variable G : topologicalType.
Variables (mul : G -> G -> G) (inv : G -> G) (e : G).
Hypothesis hGc : is_locally_compact_hausdorff_group mul inv e.
Local Notation K := (@compactly_supported_continuous_functions R G).
Variable lambda : (G -> R) -> R.
Hypothesis hl : is_monotone_daniell_integral K lambda.
Hypothesis hinv : forall S : set G, is_subgroup mul inv e S -> compact S ->
  forall s u, S s -> K u -> lambda (fun g => u (mul g s)) = lambda u.
Variable alpha : set G -> \bar R.
Hypothesis ha : is_measure alpha.
Hypothesis hrep : is_real_integral_functional alpha K lambda.

(** Source for [hT]: G is a topological group, Federer 2.7.1, p. 121,
    used in this section. *)
Let hT := lch_group_topological hGc.
(** Source for [hgl]: the group laws of G, Federer 2.7.1, p. 121, used
    in this section. *)
Let hgl := topological_group_laws hT.
(** Source for [hL]: K(G) is a lattice of functions, Federer 2.5.13,
    p. 106, used in this section. *)
Let hL := @compactly_supported_continuous_functions_lattice R G.
(** Source for [hGH]: G is Hausdorff, Federer 2.7.1, p. 121, used in
    this section. *)
Let hGH := lch_group_hausdorff hGc.
(** Source for [hGl]: G is locally compact, Federer 2.7.1, p. 121, used
    in this section. *)
Let hGl := lch_group_locally_compact hGc.

(** Source for [open_test_functions]: "Phi = K(G)+ cap {f: f <= u}",
    with u the characteristic function of U, Federer 2.7.14, p. 131.
    Definition: f in K(G), f >= 0, f <= 1 and f = 0 outside U, which is
    f in K(G)+ with f <= u. *)
Definition open_test_functions (U : set G) : set (G -> R) :=
  [set w | [/\ K w, function_nonnegative w, forall x, w x <= 1 & forall x, ~ U x -> w x = 0]].

(** Source for [sequence_subgroup]: "the closed subgroup
    S = G cap {s: f(t s) = f(t) whenever f in Psi, t in G}", Federer
    2.7.14, p. 131, for Psi = {f_n: n in N}. Definition. *)
Definition sequence_subgroup (f : nat -> G -> R) : set G :=
  [set s | forall n t, f n (mul t s) = f n t].

(** Source for [sequence_null_locus]: "the alpha measurable set
    P = Intersection_{f in Psi} {g: f(g) = 0}", Federer 2.7.14, p. 132,
    for Psi = {f_n: n in N}. Definition. *)
Definition sequence_null_locus (f : nat -> G -> R) : set G := [set x | forall n, f n x = 0].

(** Source for [subgroup_saturation]: the set {g: omega(g) > 0} . S of
    Federer 2.7.14, p. 132, in "U subset Union_{omega in Omega}
    {g: [mu^x(omega) o A^x](g) > 0}" (by 2.7.10, mu^x(omega)(A^x g) > 0
    if and only if omega(g s) > 0 for some s in S). Definition: the
    points g s with omega(g) > 0 and s in S. *)
Definition subgroup_saturation (S : set G) (w : G -> R) : set G :=
  [set x | exists2 s, S s & 0 < w (mul x (inv s))].

(** Source for [sequence_ball]: the condition
    rho_{f_k}(g,h) <= r for k < n, where
    "rho_f(g,h) = sup{|f(t g) - f(t h)|: t in G}", Federer 2.7.14,
    p. 131. Definition, without forming the supremum. *)
Definition sequence_ball (f : nat -> G -> R) (n : nat) (g : G) (r : R) (h : G) : Prop :=
  forall k, (k < n)%N -> forall t, `|f k (mul t g) - f k (mul t h)| <= r.

(** Source for [positive_compact_max]: sup{omega, f} in K(G)+ for
    omega, f in K(G)+, used in "p omega + f <= sup{omega, f} in Phi",
    Federer 2.7.14, p. 132; sup{a, b} = a + b - inf{a, b} (2.5.1,
    p. 91). Supporting lemma. *)
Lemma positive_compact_max (a b : G -> R) : K a -> K b -> function_nonnegative a ->
  function_nonnegative b -> K (fun x => Order.max (a x) (b x)).
Proof.
move=> hka hkb ha0 hb0.
have hmin := function_lattice_minimum hL hka hkb.
have hsum := function_lattice_add hL hka hkb.
have hle : function_le (fun x => Order.min (a x) (b x)) (fun x => a x + b x).
  move=> x; have hm : Order.min (a x) (b x) <= a x by rewrite ge_min lexx.
  apply: le_trans hm _; exact: ler_wpDr (hb0 x) (lexx _).
have hd := function_lattice_ordered_difference hL hmin hsum hle.
have -> : (fun x => Order.max (a x) (b x)) = (fun x => a x + b x - Order.min (a x) (b x)).
  by apply: funext=> x; case: (leP (a x) (b x))=> _; lra.
exact: hd.
Qed.

(** Source for [compact_right_translate]: g |-> u(g s) belongs to K(G)
    for u in K(G), used for omega(g s) in the proof of Federer 2.7.14,
    p. 132; it is u o A_{s^{-1}} for the action 2.7.2(2), p. 122.
    Supporting lemma. *)
Lemma compact_right_translate (u : G -> R) s : K u -> K (fun g => u (mul g s)).
Proof.
move=> hu.
have h := compactly_supported_translate hgl (right_multiplication_homogeneous hT) (inv s) hu.
have -> : (fun g => u (mul g s)) = u \o right_multiplication_action mul inv (inv s).
  by apply: funext=> g; rewrite /= /right_multiplication_action (group_invK hgl).
exact: h.
Qed.

(** Source for [compact_left_translate_continuous]: h |-> f(t h) is
    continuous for continuous f, supporting the pseudometrics rho_f of
    Federer 2.7.14, p. 131. Supporting lemma. *)
Lemma compact_left_translate_continuous (u : G -> R) t :
  continuous (u : G -> real_line_metric R) -> continuous ((fun h => u (mul t h)) : G -> real_line_metric R).
Proof.
move=> hu x; apply: (@continuous_comp G G (real_line_metric R) (mul t) u x).
- exact: left_translation_continuous hT t x.
- exact: hu.
Qed.

(** Source for [compact_right_translate_continuous]: h |-> f(h s) is
    continuous for continuous f, supporting the open sets
    {g: omega(g s) > 0} in the proof of Federer 2.7.14, p. 132.
    Supporting lemma. *)
Lemma compact_right_translate_continuous (u : G -> R) s :
  continuous (u : G -> real_line_metric R) -> continuous ((fun h => u (mul h s)) : G -> real_line_metric R).
Proof.
move=> hu x; apply: (@continuous_comp G G (real_line_metric R) (fun h => mul h s) u x).
- exact: right_translation_continuous hT s x.
- exact: hu.
Qed.

(** Source for [left_uniform_continuity]: "The uniform continuity of f
    on G implies continuity of rho_f", Federer 2.7.14, p. 131, for the
    uniformity of 2.7.5, p. 125, with the basis {(y,z): y^{-1} z in V}:
    there is a neighbourhood V of e with |u(y) - u(z)| <= eps whenever
    y^{-1} z in V. Supporting lemma. *)
Lemma left_uniform_continuity (u : G -> R) (eps : R) : K u -> 0 < eps ->
  exists2 V : set G, nbhs e V & forall y z, V (mul (inv y) z) -> `|u y - u z| <= eps.
Proof.
move=> hu heps.
have [hE hnb _ _] := left_division_entourage_basis hT.
have [D hD hDu] := compactly_supported_uniformly_continuous hE hnb hu heps.
have [V hV hVD] := hD.
by exists V=> // y z hyz; apply: hDu; apply: hVD.
Qed.

(** Source for [open_test_max]: "sup{omega, f} in Phi" for omega, f in
    Phi, Federer 2.7.14, p. 132. Supporting lemma. *)
Lemma open_test_max (U : set G) (a b : G -> R) : open_test_functions U a -> open_test_functions U b ->
  open_test_functions U (fun x => Order.max (a x) (b x)).
Proof.
move=> [hka ha0 ha1 haU] [hkb hb0 hb1 hbU]; split.
- exact: positive_compact_max.
- by move=> x; apply: le_trans (ha0 x) _; rewrite le_max lexx.
- by move=> x; rewrite ge_max ha1 hb1.
- by move=> x hx; rewrite (haU x hx) (hbU x hx) maxxx.
Qed.

(** Source for [open_test_zero]: the zero function belongs to
    Phi = K(G)+ cap {f: f <= u}, Federer 2.7.14, p. 131. Supporting
    lemma. *)
Lemma open_test_zero (U : set G) : open_test_functions U (fun _ => 0).
Proof.
split; [exact: (@compactly_supported_zero_function R G)|by move=> x|by move=> x; exact: ler01|by []].
Qed.

(** Source for [open_test_cutoff]: for g in an open set U there is
    omega in Phi with omega(g) = 1, a cutoff function of 2.5.13–2.5.14,
    pp. 106–108, with support in U; used for "Phi has a countable subset
    Omega such that A^x(U) = Union_{omega in Omega} A^x{g: omega(g) > 0}",
    Federer 2.7.14, p. 132. Supporting lemma. *)
Lemma open_test_cutoff (U : set G) g : open U -> U g ->
  exists2 w, open_test_functions U w & w g = 1.
Proof.
move=> hUo hUg.
have hg : [set g] `<=` U by move=> x ->.
have [[hc hr h1] hspt] := @localized_compact_cutoff_specification R G [set g] U hGH hGl (@compact_set1 G g) hUo hg.
exists (@localized_compact_cutoff R G [set g] U hGH hGl (@compact_set1 G g) hUo hg); last exact: h1.
split=> //.
- by move=> x; have /andP[] := hr x.
- by move=> x; have /andP[] := hr x.
- by move=> x hx; apply: real_function_zero_off_support=> hs; apply: hx; exact: hspt x hs.
Qed.

Section FixedOpenSet.
Variable U : set G.
Hypothesis hUo : open U.
Hypothesis hUc : compact (closure U).
Variable f : nat -> G -> R.
Variable g0 : G.
Hypothesis hfP : forall n, open_test_functions U (f n).
Hypothesis hfg0 : 0 < f 0%N g0.
Hypothesis hfsup : forall w n, open_test_functions U w -> lambda w <= lambda (f n) + (n.+1%:R)^-1.

Local Notation S := (sequence_subgroup f).
Local Notation P := (sequence_null_locus f).

(** Source for [sequence_subgroup_subgroup]: "the closed subgroup S",
    Federer 2.7.14, p. 131: S is a subgroup of G. Supporting lemma. *)
Lemma sequence_subgroup_subgroup : is_subgroup mul inv e S.
Proof.
constructor.
- by move=> n t; rewrite (group_mulg1 hgl).
- by move=> a b ha' hb' n t; rewrite (group_mulA hgl) hb' ha'.
- move=> a ha' n t; have h := ha' n (mul t (inv a)).
  by rewrite (group_mulgKV hgl) in h; rewrite h.
Qed.

(** Source for [sequence_subgroup_closed]: "the closed subgroup S",
    Federer 2.7.14, p. 131: S is closed, as an intersection of the sets
    {s: f(t s) = f(t)}, each closed by the continuity of s |-> f(t s).
    Supporting lemma. *)
Lemma sequence_subgroup_closed : closed S.
Proof.
have -> : S = \bigcap_(p in [set: nat * G])
    ([set s | f p.1 (mul p.2 s) <= f p.1 p.2] `&` [set s | f p.1 p.2 <= f p.1 (mul p.2 s)]).
  apply/seteqP; split=> s hs.
  - by move=> [n t] _ /=; rewrite hs; split.
  - move=> n t; have [h1 h2] := hs (n, t) I; apply/eqP; rewrite eq_le; apply/andP; split; [exact: h1|exact: h2].
apply: closed_bigI=> [[n t]] _ /=.
have [[hfc _] _ _ _] := hfP n.
have hc := @compact_left_translate_continuous (f n) t hfc.
apply: closedI.
- exact: real_closed_lower_level_closed hc.
- exact: real_closed_upper_level_closed hc.
Qed.

(** Source for [sequence_subgroup_compact]: "S = Intersection_{f in Psi}
    {h: rho_f(e,h) = 0} is compact", Federer 2.7.14, p. 132. Direct
    formalisation: f_0(g_0 s) = f_0(g_0) > 0 for s in S, so S is a closed
    subset of the compact set g_0^{-1} . spt f_0. *)
Lemma sequence_subgroup_compact : compact S.
Proof.
have [[_ hspt] _ _ _] := hfP 0%N.
have himg : compact (mul (inv g0) @` real_function_support (f 0%N)).
  apply: continuous_compact hspt; apply: continuous_subspaceT.
  exact: left_translation_continuous hT (inv g0).
apply: (subclosed_compact sequence_subgroup_closed himg)=> s hs.
exists (mul g0 s); last by rewrite (group_mulKg hgl).
apply: subset_closure; rewrite /= (hs 0%N g0); exact: (elimN eqP (lt0r_neq0 hfg0)).
Qed.

(** Source for [sequence_right_invariant]: lambda_g u(g s) = lambda(u)
    for u in K(G) and s in S, from "Delta_G and chi map the compact
    subgroup S onto {1}", Federer 2.7.14, p. 133. Supporting lemma. *)
Lemma sequence_right_invariant s u : S s -> K u -> lambda (fun g => u (mul g s)) = lambda u.
Proof.
move=> hs hu; exact: (hinv sequence_subgroup_subgroup sequence_subgroup_compact hs hu).
Qed.

(** Source for [null_locus_right_translate_null]: for omega in Phi and
    s in S, the set P cap {g: omega(g s) > 0} is alpha null. This
    replaces "integral p omega d alpha = 0" of Federer 2.7.14, p. 132,
    and its use in the computation of integral p . [mu^x(omega) o A^x]
    d alpha: with k_n = sup{omega(. s), f_n} - f_n in K(G)+, the
    inequality "p omega + f <= sup{omega, f} in Phi" gives k_n > t on
    P cap {g: omega(g s) > t}, and lambda(k_n) <= 1/(n+1) because
    sup{omega(. s), f_n} = sup{omega, f_n}(. s). Different proof route. *)
Lemma null_locus_right_translate_null (w : G -> R) s : open_test_functions U w -> S s ->
  alpha (P `&` [set x | 0 < w (mul x s)]) = 0%E.
Proof.
move=> hw hs.
have [hkw hw0 _ _] := hw.
have hlev m : alpha (P `&` [set x | (m.+1%:R)^-1 < w (mul x s)]) = 0%E.
  pose d : R := (m.+1%:R)^-1.
  have hd : 0 < d by rewrite /d invr_gt0 ltr0n.
  apply: (extended_null_of_small_bounds hd (measure_nonnegative ha _))=> n.
  have [hkf hf0 _ _] := hfP n.
  have hkws : K (fun x => w (mul x s)) := @compact_right_translate w s hkw.
  have hws0 : function_nonnegative (fun x => w (mul x s)) by move=> x; exact: hw0.
  pose M := fun x => Order.max (w (mul x s)) (f n x).
  have hM : K M := positive_compact_max hkws hkf hws0 hf0.
  have hfM : function_le (f n) M by move=> x; rewrite /M le_max lexx orbT.
  pose k := fun x => M x - f n x.
  have hk : K k := function_lattice_ordered_difference hL hkf hM hfM.
  have hk0 : function_nonnegative k by move=> x; rewrite /k subr_ge0; exact: hfM.
  have hMk : lambda M = lambda (f n) + lambda k.
    have -> : M = (fun x => f n x + k x) by apply: funext=> x; rewrite /k addrC subrK.
    exact: (monotone_daniell_integral_add hl hkf hk).
  have hMs : M = (fun x => Order.max (w (mul x s)) (f n (mul x s))).
    by apply: funext=> x; rewrite /M (hs n x).
  have hM' : lambda M = lambda (fun x => Order.max (w x) (f n x)).
    have [hKF _ _ _] := open_test_max hw (hfP n).
    rewrite hMs; exact: (sequence_right_invariant hs hKF).
  have hMle : lambda M <= lambda (f n) + (n.+1%:R)^-1.
    rewrite hM'; exact: hfsup (open_test_max hw (hfP n)).
  have hkle : lambda k <= (n.+1%:R)^-1 by move: hMle; rewrite hMk lerD2l.
  have hsub : P `&` [set x | d < w (mul x s)] `<=` [set x | d < k x].
    move=> x [hxP hx]; rewrite /= /k (hxP n) subr0 /M (hxP n).
    by apply: lt_le_trans hx _; rewrite le_max lexx.
  have hb := represented_lattice_strict_level_bound ha hrep (conj hk hk0) hd.
  have h1 : (d%:E * alpha (P `&` [set x | (d < w (mul x s))%R]) <=
      d%:E * alpha [set x | (d < k x)%R])%E.
    apply: lee_pmul; [rewrite lee_fin; exact: ltW hd|exact: measure_nonnegative ha _|exact: lexx|].
    apply: (measure_mono ha); exact: hsub.
  apply: le_trans h1 _; apply: le_trans hb _; by rewrite lee_fin.
have hcov : P `&` [set x | 0 < w (mul x s)] `<=`
    \bigcup_(m in [set: nat]) (P `&` [set x | (m.+1%:R)^-1 < w (mul x s)]).
  move=> x [hxP hx]; have [m hm] := positive_reciprocal_nat_small hx.
  by exists m=> //; split.
apply: (measure_null_subset ha hcov).
apply: (@measure_null_countable_union R G nat alpha ha setT _ (countableP _))=> m _.
exact: hlev m.
Qed.

(** Source for [null_locus_saturation_null]: for omega in Phi the set
    P cap ({g: omega(g) > 0} . S) is alpha null; this is the conclusion
    "integral p . [mu^x(omega) o A^x] d alpha = 0" of Federer 2.7.14,
    p. 132, in terms of sets. The compact sets {omega >= 1/(m+1)} . S are
    covered by finitely many of the open sets {g: omega(g s^{-1}) > 0},
    s in S, whose intersections with P are alpha null by
    null_locus_right_translate_null. Different proof route. *)
Lemma null_locus_saturation_null (w : G -> R) : open_test_functions U w ->
  alpha (P `&` subgroup_saturation S w) = 0%E.
Proof.
move=> hw; have [[hwc hws] hw0 _ _] := hw.
pose C m := (fun p : G * G => mul p.1 p.2) @`
  ([set c | (m.+1%:R)^-1 <= w c] `*` S).
have hlevc m : compact [set c | (m.+1%:R)^-1 <= w c].
  apply: (subclosed_compact (real_closed_upper_level_closed hwc) hws)=> c hc.
  apply: subset_closure=> /= hc0; move: hc; rewrite /= hc0 leNgt invr_gt0 ltr0n //.
have hC m : compact (C m).
  apply: continuous_compact; last exact: compact_setX (hlevc m) sequence_subgroup_compact.
  apply: continuous_subspaceT; exact: topological_group_mul_continuous hT.
have hCm m : alpha (P `&` C m) = 0%E.
  have hcov : C m `<=` \bigcup_(s in S) [set x | 0 < w (mul x (inv s))].
    move=> _ [[c s] [hc hs] <-] /=; exists s=> //=.
    rewrite (group_mulgK hgl); apply: lt_le_trans hc; rewrite invr_gt0 ltr0n //.
  have hop s : S s -> open [set x | 0 < w (mul x (inv s))].
    move=> _; exact: real_strict_upper_level_open (@compact_right_translate_continuous w (inv s) hwc).
  have [D' hD' hDcov] := compact_open_finite_cover (hC m) hop hcov.
  have hsub : P `&` C m `<=` \bigcup_(s in [set` D']) (P `&` [set x | 0 < w (mul x (inv s))]).
    move=> x [hxP hxC]; have [s hs hx] := hDcov x hxC; by exists s=> //; split.
  apply: (measure_null_subset ha hsub).
  apply: (measure_null_countable_union ha (finite_set_countable (finite_fset D')))=> s hs.
  exact: (null_locus_right_translate_null hw (subgroup_inv sequence_subgroup_subgroup (set_mem (hD' s hs)))).
have hsub : P `&` subgroup_saturation S w `<=` \bigcup_(m in [set: nat]) (P `&` C m).
  move=> x [hxP [s hs hx]]; have [m hm] := positive_reciprocal_nat_small hx.
  exists m=> //; split=> //; exists (mul x (inv s), s); first by split=> //; exact: ltW hm.
  by rewrite /= (group_mulgKV hgl).
apply: (measure_null_subset ha hsub).
apply: (@measure_null_countable_union R G nat alpha ha setT _ (countableP _))=> m _.
exact: hCm.
Qed.

(** Source for [sequence_ball_triangle]: the triangle inequality of the
    pseudometrics rho_f, Federer 2.7.14, p. 131: rho(g,h) <= r and
    rho(h,k) <= r' imply rho(g,k) <= r + r'. Supporting lemma. *)
Lemma sequence_ball_triangle n g h k r r' :
  sequence_ball f n g r h -> sequence_ball f n h r' k -> sequence_ball f n g (r + r') k.
Proof.
move=> h1 h2 i hi t; apply: le_trans (ler_distD (f i (mul t h)) _ _) _.
exact: lerD (h1 i hi t) (h2 i hi t).
Qed.

(** Source for [sequence_ball_sym]: the symmetry rho_f(g,h) = rho_f(h,g),
    Federer 2.7.14, p. 131. Supporting lemma. *)
Lemma sequence_ball_sym n g h r : sequence_ball f n g r h -> sequence_ball f n h r g.
Proof. by move=> hb i hi t; rewrite distrC; exact: hb i hi t. Qed.

(** Source for [sequence_ball_nbhs]: "The uniform continuity of f on G
    implies continuity of rho_f on G x G", Federer 2.7.14, p. 131, in the
    form used: for r > 0 the set {h: rho_{f_k}(d,h) <= r for k < n} is a
    neighbourhood of d. Supporting lemma, by induction on n, with the
    uniformity of 2.7.5, p. 125: (t d)^{-1} (t h) = d^{-1} h. *)
Lemma sequence_ball_nbhs n d r : 0 < r -> nbhs d (sequence_ball f n d r).
Proof.
move=> hr; elim: n=> [|n ih].
  have -> : sequence_ball f 0 d r = setT by apply/seteqP; split=> // h _ k; rewrite ltn0.
  exact: filterT.
have [hkf _ _ _] := hfP n.
have [V hV hVu] := @left_uniform_continuity (f n) r hkf hr.
have hW : nbhs d [set h | V (mul (inv d) h)].
  have hc := left_translation_continuous hT (inv d) d.
  by apply: hc; rewrite /= (group_mulVg hgl).
apply: (filterS _ (filterI ih hW))=> h [hb hV'] k hk t.
rewrite ltnS leq_eqVlt in hk; have [/eqP ->|hlt] := orP hk; last exact: hb k hlt t.
apply: hVu; by rewrite (group_invM hgl) -(group_mulA hgl) (group_mulKg hgl).
Qed.

(** Source for [saturated_open_contains_ball]: "It suffices to show
    that, if g in G and W is an open neighborhood of g in G with
    W . S = W, then the family of compact sets {h: rho_f(g,h) <= r and
    h notin W} which correspond to f in Psi and 0 < r <= sup im f, does
    not have the finite intersection property", Federer 2.7.14, p. 132.
    Direct formalisation of the consequence: some finite set of
    conditions rho_{f_k}(g,h) <= r, k < n, forces h in W. The compact set
    {h: rho_{f_0}(g,h) <= f_0(g_0)/2} lies in t_0^{-1} . spt f_0 with
    t_0 g = g_0, as in "because there exists t in G with f(t g) > r,
    hence rho_f(g,h) <= r implies f(t h) > 0, h in t^{-1} . spt f"; a
    point h outside W with rho_f(g,h) = 0 for every f in Psi would
    satisfy g^{-1} h in S and h in g S subset W. The finite intersection
    property is used in its open cover form. *)
Lemma saturated_open_contains_ball (W : set G) g : open W ->
  (forall x s, W x -> S s -> W (mul x s)) -> W g ->
  exists n r, 0 < r /\ forall h, sequence_ball f n g r h -> W h.
Proof.
move=> hWo hWs hWg.
have [[hf0c hf0s] _ _ _] := hfP 0%N.
pose r0 := f 0%N g0 / 2.
have hr0 : 0 < r0 by rewrite /r0 divr_gt0.
pose t0 := mul g0 (inv g).
pose K0 := [set h | forall t, `|f 0%N (mul t g) - f 0%N (mul t h)| <= r0].
have hK0c : closed K0.
  have -> : K0 = \bigcap_(t in [set: G])
      ([set h | f 0%N (mul t g) - r0 <= f 0%N (mul t h)] `&` [set h | f 0%N (mul t h) <= f 0%N (mul t g) + r0]).
    apply/seteqP; split=> h hh.
    - move=> t _; have := hh t; rewrite ler_distlC=> /andP[h1 h2]; split; [exact: h1|exact: h2].
    - move=> t; have [h1 h2] := hh t I; rewrite ler_distlC; apply/andP; split; [exact: h1|exact: h2].
  apply: closed_bigI=> t _; have hc := @compact_left_translate_continuous (f 0%N) t hf0c.
  apply: closedI; [exact: real_closed_upper_level_closed hc|exact: real_closed_lower_level_closed hc].
have hK0s : K0 `<=` mul (inv t0) @` real_function_support (f 0%N).
  move=> h hh; exists (mul t0 h); last by rewrite (group_mulKg hgl).
  apply: subset_closure=> /= hz.
  have h1 : mul t0 g = g0 by rewrite /t0 (group_mulgKV hgl).
  have := hh t0; rewrite h1 hz subr0 ger0_norm; last exact: ltW hfg0.
  rewrite /r0=> hle; have hlt : f 0%N g0 / 2 < f 0%N g0.
    by rewrite ltr_pdivrMr ?ltr0n // ltr_pMr // ltr1n.
  by have := le_lt_trans hle hlt; rewrite ltxx.
have hK0 : compact K0.
  apply: (subclosed_compact hK0c _ hK0s); apply: continuous_compact hf0s.
  apply: continuous_subspaceT; exact: left_translation_continuous hT (inv t0).
pose F (i : option (nat * nat)) : set G :=
  if i is Some (k, j) then
    [set h | exists t, (j.+1%:R)^-1 < `|f k (mul t g) - f k (mul t h)|]
  else W.
have hFo i : [set: option (nat * nat)] i -> open (F i).
  case: i=> [[k j]|] _ /=; last exact: hWo.
  have [[hfkc _] _ _ _] := hfP k.
  have -> : [set h | exists t, (j.+1%:R)^-1 < `|f k (mul t g) - f k (mul t h)|] =
      \bigcup_(t in [set: G]) ([set h | f k (mul t h) < f k (mul t g) - (j.+1%:R)^-1] `|`
        [set h | f k (mul t g) + (j.+1%:R)^-1 < f k (mul t h)]).
    apply/seteqP; split=> h.
    - by move=> [t ht]; exists t=> //; apply/real_lt_dist_split.
    - by move=> [t _ ht]; exists t; apply/real_lt_dist_split.
  apply: bigcup_open=> t _; have hc := @compact_left_translate_continuous (f k) t hfkc.
  apply: openU; [exact: real_strict_lower_level_open hc|exact: real_strict_upper_level_open hc].
have hcov : K0 `<=` \bigcup_(i in [set: option (nat * nat)]) F i.
  move=> h hh; case: (pselect (W h))=> hWh; first by exists None.
  have hex : exists k t, f k (mul t g) <> f k (mul t h).
    apply: contrapT=> hn; apply: hWh.
    have hS : S (mul (inv g) h).
      move=> k t.
      have heq : f k (mul (mul t (inv g)) g) = f k (mul (mul t (inv g)) h).
        by apply: contrapT=> hne; apply: hn; exists k, (mul t (inv g)).
      by rewrite (group_mulgKV hgl) in heq; rewrite (group_mulA hgl) -heq.
    by have := hWs g _ hWg hS; rewrite (group_mulKVg hgl).
  have [k [t ht]] := hex.
  have hpos : 0 < `|f k (mul t g) - f k (mul t h)| by rewrite normr_gt0 subr_eq0; apply/eqP.
  have [j hj] := positive_reciprocal_nat_small hpos.
  by exists (Some (k, j))=> //; exists t.
have [D' _ hDcov] := compact_open_finite_cover hK0 hFo hcov.
pose kof (i : option (nat * nat)) := if i is Some (k, _) then k else 0%N.
pose jof (i : option (nat * nat)) := if i is Some (_, j) then j else 0%N.
pose N := (\max_(i <- D') kof i).+1.
pose J := \max_(i <- D') jof i.
pose r := Order.min r0 (J.+1%:R)^-1.
exists N, r; split; first by rewrite lt_min hr0 invr_gt0 ltr0n.
move=> h hb.
have hhK : K0 h.
  move=> t; apply: le_trans (hb 0%N _ t) _; first by rewrite /N ltnS leq0n.
  by rewrite ge_min lexx.
have [i hi hFi] := hDcov h hhK.
case: i hi hFi=> [[k j]|] hi /= hFi; last exact: hFi.
exfalso; have [t ht] := hFi.
have hk : (k < N)%N by rewrite /N ltnS (@leq_bigmax_seq _ _ _ kof (Some (k, j))).
have hj : (j <= J)%N by exact: (@leq_bigmax_seq _ _ _ jof (Some (k, j))).
have hle := hb k hk t.
have hrj : r <= (j.+1%:R)^-1.
  apply: le_trans (_ : r <= (J.+1%:R)^-1) _; first by rewrite ge_min lexx orbT.
  by rewrite lef_pV2 ?posrE ?ltr0n // ler_nat ltnS.
by have := lt_le_trans ht (le_trans hle hrj); rewrite ltxx.
Qed.

(** Source for [sequence_ball_le]: rho(g,h) <= r and r <= r' give
    rho(g,h) <= r', Federer 2.7.14, p. 131. Supporting lemma. *)
Lemma sequence_ball_le n g h r r' : r <= r' -> sequence_ball f n g r h -> sequence_ball f n g r' h.
Proof. by move=> hr hb k hk t; exact: le_trans (hb k hk t) hr. Qed.

(** Source for [subgroup_saturation_open]: {g: omega(g) > 0} . S is
    open, as a union of the open sets {g: omega(g s^{-1}) > 0}, Federer
    2.7.14, p. 132. Supporting lemma. *)
Lemma subgroup_saturation_open w : K w -> open (subgroup_saturation S w).
Proof.
move=> [hwc _].
have -> : subgroup_saturation S w = \bigcup_(s in S) [set x | 0 < w (mul x (inv s))].
  by apply/seteqP; split=> x [s hs hx]; exists s.
apply: bigcup_open=> s _.
exact: real_strict_upper_level_open (@compact_right_translate_continuous w (inv s) hwc).
Qed.

(** Source for [subgroup_saturation_saturated]: W . S = W for
    W = {g: omega(g) > 0} . S, Federer 2.7.14, p. 132, "W . S = W".
    Supporting lemma. *)
Lemma subgroup_saturation_saturated w x s :
  subgroup_saturation S w x -> S s -> subgroup_saturation S w (mul x s).
Proof.
move=> [s' hs' hx] hs; exists (mul s' s); first exact: (subgroup_mul sequence_subgroup_subgroup hs' hs).
by rewrite (group_invM hgl) -(group_mulA hgl) (group_mulKVg hgl).
Qed.

(** Source for [countable_saturation_cover]: "Since X is metrizable and
    Clos A^x(U) is compact, the topology of A^x(U) has a countable base.
    Consequently Phi has a countable subset Omega such that
    A^x(U) = Union_{omega in Omega} A^x{g: omega(g) > 0} ... hence
    U subset Union_{omega in Omega} {g: [mu^x(omega) o A^x](g) > 0}",
    Federer 2.7.14, p. 132. Direct formalisation of the conclusion, with
    Omega indexed by n, j in N and the finitely many centres d of a
    cover of Clos U by balls {h: rho_{f_k}(d,h) <= 1/(j+1), k < n}.
    Different proof route: the quotient X and its metric are not formed;
    the pseudometrics act on G, and saturated_open_contains_ball replaces
    the comparison of the metric topology with the quotient topology. *)
Lemma countable_saturation_cover : exists (D : nat -> nat -> {fset G}) (Om : nat -> nat -> G -> G -> R),
  (forall n j d, open_test_functions U (Om n j d)) /\
  U `<=` \bigcup_(n in [set: nat]) \bigcup_(j in [set: nat]) \bigcup_(d in [set` D n j])
    subgroup_saturation S (Om n j d).
Proof.
have hO n j d : exists O : set G, [/\ open O, O d & O `<=` sequence_ball f n d (j.+1%:R)^-1].
  have hb := @sequence_ball_nbhs n d (j.+1%:R)^-1 (nat_reciprocal_positive R j).
  rewrite nbhsE in hb; have [B [hBo hBd] hBs] := hb; by exists B.
pose O n j d := projT1 (cid (hO n j d)).
have hOs n j d : [/\ open (O n j d), O n j d d & O n j d `<=` sequence_ball f n d (j.+1%:R)^-1].
  exact: projT2 (cid (hO n j d)).
have hfin n j : exists2 D' : {fset G}, {subset D' <= closure U} &
    closure U `<=` cover [set` D'] (O n j).
  apply: (compact_open_finite_cover hUc)=> [d _|d hd]; first by have [] := hOs n j d.
  by exists d=> //; have [] := hOs n j d.
pose D n j := s2val (cid2 (hfin n j)).
have hD n j : closure U `<=` cover [set` D n j] (O n j) := s2valP' (cid2 (hfin n j)).
pose cond n j d w := open_test_functions U w /\
  forall h, sequence_ball f n d (j.+1%:R)^-1 h -> subgroup_saturation S w h.
pose Om n j d := if pselect (exists w, cond n j d w) is left H then projT1 (cid H) else (fun _ => 0).
have hOm n j d : open_test_functions U (Om n j d).
  rewrite /Om; case: pselect=> [H|_]; last exact: open_test_zero.
  by have [] := projT2 (cid H).
exists D, Om; split=> // g hg.
have [w hw hwg] := open_test_cutoff hUo hg.
have [hwK _ _ _] := hw.
have hWo := subgroup_saturation_open hwK.
have hWg : subgroup_saturation S w g.
  exists e; first exact: subgroup_unit sequence_subgroup_subgroup.
  by rewrite (group_inv1 hgl) (group_mulg1 hgl) hwg ltr01.
have [n [r [hr hball]]] := saturated_open_contains_ball hWo (@subgroup_saturation_saturated w) hWg.
have hr2 : 0 < r / 2 by rewrite divr_gt0.
have [j hj] := positive_reciprocal_nat_small hr2.
have [d hd hOd] := hD n j g (subset_closure hg).
have [_ _ hOb] := hOs n j d.
have hgd := hOb g hOd.
have hcond : cond n j d w.
  split=> // h hh; apply: hball; apply: (sequence_ball_le _ (sequence_ball_triangle (sequence_ball_sym hgd) hh)).
  by rewrite [r]splitr; apply: lerD; exact: ltW hj.
exists n=> //; exists j=> //; exists d=> //.
have hcd : exists w, cond n j d w by exists w.
rewrite /Om; case: pselect=> [H|hn]; last by exfalso; exact: hn hcd.
by have [_ h2] := projT2 (cid H); exact: h2 g hgd.
Qed.

(** Source for [null_locus_open_null]: "We infer that alpha(P cap U) =
    0", Federer 2.7.14, p. 133. Direct formalisation: P cap U is covered
    by the countably many alpha null sets P cap ({omega > 0} . S),
    omega in Omega. *)
Lemma null_locus_open_null : alpha (P `&` U) = 0%E.
Proof.
have [D [Om [hOm hcov]]] := countable_saturation_cover.
have hsub : P `&` U `<=` \bigcup_(n in [set: nat]) \bigcup_(j in [set: nat])
    \bigcup_(d in [set` D n j]) (P `&` subgroup_saturation S (Om n j d)).
  move=> x [hxP hxU]; have [n _ [j _ [d hd hx]]] := hcov x hxU.
  by exists n=> //; exists j=> //; exists d=> //; split.
apply: (measure_null_subset ha hsub).
apply: (@measure_null_countable_union R G nat alpha ha setT _ (countableP _))=> n _.
apply: (@measure_null_countable_union R G nat alpha ha setT _ (countableP _))=> j _.
apply: (measure_null_countable_union ha (finite_set_countable (finite_fset (D n j))))=> d _.
exact: null_locus_saturation_null (hOm n j d).
Qed.

(** Source for [fixed_open_set_measurable]: "and conclude
    U = (X ~ P) cup (P cap U) is alpha measurable", Federer 2.7.14,
    p. 133, with G in place of X: G ~ P is the union of the alpha
    measurable sets {g: f_n(g) > 0}, which lie in U, and P cap U is
    alpha null. Direct formalisation, with the reading G ~ P. *)
Lemma fixed_open_set_measurable : measure_measurable alpha U.
Proof.
have hU : U = (\bigcup_(n in [set: nat]) [set x | 0 < f n x]) `|` (P `&` U).
  apply/seteqP; split=> x.
  - move=> hx; case: (pselect (P x))=> hP; first by right.
    left; have [n hn] : exists n, f n x <> 0.
      by apply: contrapT=> hn; apply: hP=> n; apply: contrapT=> hne; apply: hn; exists n.
    exists n=> //=; have [_ hf0 _ _] := hfP n; rewrite lt_def (hf0 x) andbT; exact/eqP.
  - case=> [[n _ hn]|[_ hx]] //; apply: contrapT=> hx.
    have [_ _ _ hz] := hfP n; by move: hn; rewrite /= (hz x hx) ltxx.
have hlev n m : measure_measurable alpha [set x | (m.+1%:R)^-1 < f n x].
  have [hkf hf0 _ _] := hfP n.
  apply: (represented_lattice_strict_level_measurable ha hrep).
  exists (f n), (m.+1%:R)^-1; split; first by split.
  by split=> //; rewrite invr_gt0 ltr0n.
have hpos n : measure_measurable alpha [set x | 0 < f n x].
  have -> : [set x | 0 < f n x] = \bigcup_(m in [set: nat]) [set x | (m.+1%:R)^-1 < f n x].
    apply/seteqP; split=> x hx; last first.
      by have [m _ hm] := hx; apply: lt_trans hm; rewrite invr_gt0 ltr0n.
    by have [m hm] := positive_reciprocal_nat_small hx; exists m.
  exact: (measure_measurable_countable_union ha (countableP _) (fun m _ => hlev n m)).
have h1 : measure_measurable alpha (\bigcup_(n in [set: nat]) [set x | 0 < f n x]).
  exact: (measure_measurable_countable_union ha (countableP _) (fun n _ => hpos n)).
have h2 : measure_measurable alpha (P `&` U) := measure_null_measurable ha null_locus_open_null.
rewrite hU; exact: (measure_measurable_union ha h1 h2).
Qed.

End FixedOpenSet.

(** Source for [open_test_sequence_exists]: "and choose a countable
    subset Psi of Phi such that sup lambda(Phi) = sup lambda(Psi)",
    Federer 2.7.14, p. 131. Direct formalisation: Psi is a sequence f_n
    with lambda(w) <= lambda(f_n) + 1/(n+1) whenever w in Phi; the sup is
    finite because lambda(w) <= lambda(h) for a cutoff h equal to 1 on
    Clos U. Each f_n is replaced by sup{omega_0, f_n} for an omega_0 in
    Phi with omega_0(g_0) = 1, so that f_0(g_0) > 0; this does not change
    sup lambda(Psi) and supplies the nonzero member of Psi used for the
    compactness of S. *)
Lemma open_test_sequence_exists (U : set G) g0 : open U -> compact (closure U) -> U g0 ->
  exists f : nat -> G -> R, [/\ forall n, open_test_functions U (f n), 0 < f 0%N g0 &
    forall w n, open_test_functions U w -> lambda w <= lambda (f n) + (n.+1%:R)^-1].
Proof.
move=> hUo hUc hg0.
have [w0 hw0 hw0g] := open_test_cutoff hUo hg0.
have [hhc hhr hh1] := @compact_cutoff_specification R G (closure U) hGH hGl hUc.
pose h := @compact_cutoff R G (closure U) hGH hGl hUc.
have hbound w : open_test_functions U w -> lambda w <= lambda h.
  move=> [hwK hw0' hw1 hwU]; apply: (monotone_daniell_integral_monotone hl hwK hhc)=> x.
  case: (pselect (U x))=> hx; last by rewrite (hwU x hx); have /andP[] := hhr x.
  by rewrite hh1; [exact: hw1|exact: subset_closure].
pose E := [set y | exists2 w, open_test_functions U w & y = lambda w].
have hE : has_sup E.
  split; first by exists (lambda w0), w0.
  by exists (lambda h)=> _ [w hw ->]; exact: hbound.
have hex n : exists w, open_test_functions U w /\ sup E - (n.+1%:R)^-1 < lambda w.
  have [_ [w hw ->] hlt] := sup_adherent (nat_reciprocal_positive R n) hE.
  by exists w.
pose v n := projT1 (cid (hex n)).
have hv n : open_test_functions U (v n) /\ sup E - (n.+1%:R)^-1 < lambda (v n) := projT2 (cid (hex n)).
exists (fun n x => Order.max (w0 x) (v n x)); split.
- by move=> n; exact: open_test_max hw0 (hv n).1.
- by apply: lt_le_trans (_ : 0 < w0 g0) _; [rewrite hw0g ltr01|rewrite le_max lexx].
- move=> w n hw.
  have [hvn hlt] := hv n.
  have [hvK _ _ _] := hvn; have [hmK _ _ _] := open_test_max hw0 hvn.
  have hle : lambda (v n) <= lambda (fun x => Order.max (w0 x) (v n x)).
    by apply: (monotone_daniell_integral_monotone hl hvK hmK)=> x; rewrite le_max lexx orbT.
  have hwE : lambda w <= sup E by apply: (sup_upper_bound hE); exists w.
  move: hlt; rewrite ltrBlDr=> hlt.
  apply: le_trans hwE (le_trans (ltW hlt) _); exact: lerD hle (lexx _).
Qed.

(** Source for [covariant_open_compact_closure_measurable]: "we need to
    show that, if U is any nonempty open subset of G with compact
    closure, then U is alpha measurable", Federer 2.7.14, p. 131, and
    "U = (X ~ P) cup (P cap U) is alpha measurable", p. 133. Direct
    formalisation, under the right invariance of lambda for compact
    subgroups; the empty set is included. *)
Theorem covariant_open_compact_closure_measurable (U : set G) :
  open U -> compact (closure U) -> measure_measurable alpha U.
Proof.
move=> hUo hUc; case: (pselect (exists g0, U g0))=> [[g0 hg0]|hn].
- have [f [hfP hfg0 hfsup]] := open_test_sequence_exists hUo hUc hg0.
  exact: (fixed_open_set_measurable hUo hUc hfP hfg0 hfsup).
- have hU0 : alpha U = 0%E.
    apply: (measure_null_subset ha (B := set0)); last exact: measure_empty ha.
    by move=> x hx; apply: hn; exists x.
  exact: (measure_null_measurable ha hU0).
Qed.

End CovariantMeasureOpenMeasurability.
