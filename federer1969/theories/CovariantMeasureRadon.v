(** Federer (1969), 2.7.14, printed pp. 131–133: "Theorem. Every left
    (right) chi covariant measure over G is a Radon measure. Proof. Suppose
    alpha is the K(G) regular measure associated with a monotone left chi
    covariant integral lambda. In view of 2.5.3, 2.5.14 we need to show
    that, if U is any nonempty open subset of G with compact closure, then U
    is alpha measurable. ... and conclude U = (X ~ P) cup (P cap U) is alpha
    measurable." The measurability of the open sets with compact closure is
    covariant_open_compact_closure_measurable
    (CovariantMeasureOpenMeasurability.v), with the right invariance of
    lambda on compact subgroups from CovariantCompactRightInvariance.v. The
    reduction "In view of 2.5.3, 2.5.14" gives the measurability of all open
    sets, the finiteness on compact sets, the outer regularity, and the
    inner regularity of open sets of finite measure. The inner regularity of
    open sets of infinite measure, which the definition of a Radon measure
    (2.2.5, p. 62) also requires, needs a further argument and a further
    hypothesis. If lambda vanishes on K(G) and G is not contained in a
    countable union of compact sets, then alpha(G) = oo while alpha(K) = 0
    for every compact K, so alpha is not a Radon measure; the zero integral
    is a monotone left chi covariant integral for every chi (2.7.1, p. 122).
    The theorem is therefore proved under the alternative hypothesis that
    lambda does not vanish on K(G) or that G is a countable union of compact
    sets; for a measure given by is_left_covariant_measure, "lambda does not
    vanish" is expressed as "alpha(K) <> 0 for some compact K". In the first
    case positivity of lambda (CovariantCompactRightInvariance.v) and the
    cosets of an open subgroup which is a countable union of compact sets
    (OpenSigmaCompactSubgroup.v) give the inner regularity; in the second
    case the countable union does. The right version follows from the left
    version for the opposite group (G, (g,h) |-> h g), whose left
    multiplication by g is right multiplication by (g^{-1})^{-1} = g in G,
    so that a right chi covariant integral of G is a left chi o inv
    covariant integral of the opposite group. The nonzero hypothesis is
    Federer's erratum p. 3, book p. 131 line 10. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets functions reals
  constructive_ereal topology normedtype.
From Federer Require Import RealMetricBackground FunctionLatticeUP MonotoneDaniellIntegralUP
  CompactSupportFunctionUP CompactCutoffUP CompactCutoff LocalizedCompactCutoffUP
  LocalizedCompactCutoff FunctionLatticeLevelMeasurability FunctionLatticeRegularityUP
  RealIntegralFunctionalUP MeasureUP MeasureBasic MeasureAlmostBasic RadonMeasureUP
  CompactOpenContentUP CompactOpenContentMeasureBound CompactDaniellIterationCommutation
  TopologicalGroupUP TopologicalGroupLaws CovariantIntegralUP HaarIntegralUP
  GroupMultiplicationHomogeneous CovariantCompactRightInvariance CovariantMeasureOpenMeasurability
  RegularMeasureRadonCriteria OpenSigmaCompactSubgroup.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [is_sigma_compact_space]: "G is a countable union of
    compact sets", the alternative hypothesis under which the theorem of
    Federer 2.7.14, p. 131, holds for the zero integral. Definition. *)
Definition is_sigma_compact_space (X : topologicalType) : Prop :=
  exists C : nat -> set X, (forall n, compact (C n)) /\ [set: X] `<=` \bigcup_n C n.

Section LeftCovariantMeasureRadon.
Variable R : realType.
Variable G : topologicalType.
Variables (mul : G -> G -> G) (inv : G -> G) (e : G).
Hypothesis hGc : is_locally_compact_hausdorff_group mul inv e.
Local Notation K := (@compactly_supported_continuous_functions R G).

(** Source for [hT]: G is a topological group, Federer 2.7.1, p. 121,
    used in this section. *)
Let hT := lch_group_topological hGc.
(** Source for [hgl]: the group laws of G, Federer 2.7.1, p. 121, used
    in this section. *)
Let hgl := topological_group_laws hT.
(** Source for [hGH]: G is Hausdorff, Federer 2.7.1, p. 121, used in
    this section. *)
Let hGH := lch_group_hausdorff hGc.
(** Source for [hGl]: G is locally compact, Federer 2.7.1, p. 121, used
    in this section. *)
Let hGl := lch_group_locally_compact hGc.

(** Source for [left_covariant_open_positive]: alpha(V) > 0 for every
    nonempty open V when lambda does not vanish on K(G), supporting the
    inner regularity in "alpha is a Radon measure", Federer 2.7.14,
    p. 131: lambda(w) > 0 for a cutoff w with w(x) = 1 and spt w subset V
    (CovariantCompactRightInvariance.v), and lambda(w) <= alpha(V)
    (2.5.14, p. 107). Supporting lemma. *)
Lemma left_covariant_open_positive (chi : G -> R) (lambda : (G -> R) -> R) (alpha : set G -> \bar R) :
  is_monotone_daniell_integral K lambda -> is_covariant_on K (left_multiplication_action mul) chi lambda ->
  is_measure alpha -> is_real_integral_functional alpha K lambda ->
  (exists u, K u /\ lambda u <> 0) -> forall V, open V -> (exists x, V x) -> (0 < alpha V)%E.
Proof.
move=> hl hc ha hrep hnz V hV [x hx].
have hxV : [set x] `<=` V by move=> y ->.
pose w := @localized_compact_cutoff R G [set x] V hGH hGl (@compact_set1 G x) hV hxV.
have [[hwK hwr hw1] hws] := @localized_compact_cutoff_specification R G [set x] V hGH hGl
  (@compact_set1 G x) hV hxV.
have hpos : 0 < lambda w.
  apply: (left_covariant_integral_positive hGc hl hc hnz hwK).
  - by move=> y; have /andP[] := hwr y.
  - by exists x; rewrite hw1 //; exact: (elimN eqP (oner_neq0 R)).
have hle := @compact_open_test_representing_measure_bound R G alpha lambda ha hrep V w (conj hwK (conj hwr hws)).
by apply: lt_le_trans hle; rewrite lte_fin.
Qed.

(** Source for [left_covariant_integral_radon]: "Every left ... chi
    covariant measure over G is a Radon measure", Federer 2.7.14, p. 131,
    for the K(G) regular measure alpha associated with a monotone left
    chi covariant integral lambda. Direct formalisation with the added
    alternative hypothesis that lambda does not vanish on K(G) or that G
    is a countable union of compact sets; the hypothesis is necessary
    (see the header of this file). *)
Theorem left_covariant_integral_radon (chi : G -> R) (lambda : (G -> R) -> R) (alpha : set G -> \bar R) :
  is_monotone_daniell_integral K lambda -> is_covariant_on K (left_multiplication_action mul) chi lambda ->
  is_measure alpha -> is_real_integral_functional alpha K lambda -> is_function_lattice_regular K alpha ->
  (exists u, K u /\ lambda u <> 0) \/ is_sigma_compact_space G -> is_radon_measure alpha.
Proof.
move=> hl hc ha hrep hreg halt.
have hinv S : is_subgroup mul inv e S -> compact S ->
    forall s u, S s -> K u -> lambda (fun g => u (mul g s)) = lambda u.
  by move=> hS hSc s u hs hu; exact: (left_covariant_compact_right_invariant hGc hl hc hS hSc hs hu).
have hrc V : open V -> compact (closure V) -> measure_measurable alpha V.
  by move=> hV hVc; exact: (covariant_open_compact_closure_measurable hGc hl hinv ha hrep hV hVc).
case: halt=> [hnz|[C [hC hGC]]]; last exact: (regular_radon_sigma_compact hGH hGl ha hrep hreg hrc hC hGC).
have [H [hH hHo [C [hC hHC]]]] := open_sigma_compact_subgroup hGc.
have hAl := left_multiplication_homogeneous hT.
apply: (regular_radon_partition hGH hGl ha hrep hreg
  (cell := subgroup_orbit (left_multiplication_action mul) H)).
- by move=> y; exact: (subgroup_orbit_open hAl hHo y).
- by move=> y; exact: (subgroup_orbit_self hGc hAl hH y).
- by move=> y z hyz; exact: (subgroup_orbit_eq hGc hAl hH hyz).
- by move=> y; exact: (subgroup_orbit_sigma_compact hAl hC hHC y).
- exact: (left_covariant_open_positive hl hc ha hrep hnz).
- exact: hrc.
Qed.

(** Source for [left_covariant_measure_radon]: "Every left ... chi
    covariant measure over G is a Radon measure", Federer 2.7.14, p. 131.
    Direct formalisation for is_left_covariant_measure, with the added
    alternative hypothesis that alpha(K) <> 0 for some compact K (which
    holds exactly when the associated integral does not vanish) or that
    G is a countable union of compact sets. *)
Theorem left_covariant_measure_radon (chi : G -> R) (alpha : set G -> \bar R) :
  is_left_covariant_measure mul chi alpha ->
  (exists C, compact C /\ alpha C <> 0%E) \/ is_sigma_compact_space G -> is_radon_measure alpha.
Proof.
move=> [lambda [hl hc ha hrep hreg]] halt.
apply: (left_covariant_integral_radon hl hc ha hrep hreg).
case: halt=> [[C [hC hCz]]|hs]; last by right.
left; apply: contrapT=> hn; apply: hCz.
apply: (regular_vanishing_compact_null hGH hGl ha hrep _ hC)=> u hu.
by apply: contrapT=> hu0; apply: hn; exists u.
Qed.

End LeftCovariantMeasureRadon.

(** Source for [opposite_multiplication]: the multiplication
    (g,h) |-> h g of the opposite group, used to deduce the right version
    "(right) chi covariant measure" of Federer 2.7.14, p. 131, from the
    left version. Definition. *)
Definition opposite_multiplication (G : Type) (mul : G -> G -> G) : G -> G -> G :=
  fun g h => mul h g.

Section RightCovariantMeasureRadon.
Variable R : realType.
Variable G : topologicalType.
Variables (mul : G -> G -> G) (inv : G -> G) (e : G).
Hypothesis hGc : is_locally_compact_hausdorff_group mul inv e.
Local Notation K := (@compactly_supported_continuous_functions R G).

(** Source for [hT]: G is a topological group, Federer 2.7.1, p. 121,
    used in this section. *)
Let hT := lch_group_topological hGc.
(** Source for [hgl]: the group laws of G, Federer 2.7.1, p. 121, used
    in this section. *)
Let hgl := topological_group_laws hT.

(** Source for [opposite_group_lch]: the opposite group of a locally
    compact Hausdorff topological group is one, supporting the right
    version of Federer 2.7.14, p. 131. Supporting lemma. *)
Lemma opposite_group_lch : is_locally_compact_hausdorff_group (opposite_multiplication mul) inv e.
Proof.
constructor; last exact: lch_group_locally_compact hGc; last exact: lch_group_hausdorff hGc.
constructor.
- constructor.
  + by move=> g h k; rewrite /opposite_multiplication (group_mulA hgl).
  + by move=> g; rewrite /opposite_multiplication (group_mulg1 hgl).
  + by move=> g; rewrite /opposite_multiplication (group_mulgV hgl).
- have hsw := @topological_swap_continuous G G.
  have hm := topological_group_mul_continuous hT.
  have -> : (fun p : G * G => opposite_multiplication mul p.1 p.2) =
      (fun p : G * G => mul p.1 p.2) \o (fun p : G * G => (p.2, p.1)) by [].
  by move=> p; exact: (continuous_comp (hsw p) (hm _)).
- exact: topological_group_inv_continuous hT.
Qed.

(** Source for [right_covariant_opposite_left]: a right chi covariant
    integral of G (2.7.2(2), p. 122: A(g,x) = x g^{-1}) is a left
    chi o inv covariant integral of the opposite group, supporting the
    right version of Federer 2.7.14, p. 131. Supporting lemma. *)
Lemma right_covariant_opposite_left (chi : G -> R) (lambda : (G -> R) -> R) :
  is_covariant_on K (right_multiplication_action mul inv) chi lambda ->
  is_covariant_on K (left_multiplication_action (opposite_multiplication mul)) (fun g => chi (inv g)) lambda.
Proof.
move=> hc u g hu; rewrite -hc //; congr lambda; apply: funext=> x.
by rewrite /= /left_multiplication_action /right_multiplication_action /opposite_multiplication
  (group_invK hgl).
Qed.

(** Source for [right_covariant_integral_radon]: "Every ... (right)
    chi covariant measure over G is a Radon measure", Federer 2.7.14,
    p. 131, for the K(G) regular measure associated with a monotone
    right chi covariant integral lambda. Direct formalisation, with the
    alternative hypothesis of left_covariant_integral_radon, deduced
    from the left version for the opposite group. *)
Theorem right_covariant_integral_radon (chi : G -> R) (lambda : (G -> R) -> R) (alpha : set G -> \bar R) :
  is_monotone_daniell_integral K lambda -> is_covariant_on K (right_multiplication_action mul inv) chi lambda ->
  is_measure alpha -> is_real_integral_functional alpha K lambda -> is_function_lattice_regular K alpha ->
  (exists u, K u /\ lambda u <> 0) \/ is_sigma_compact_space G -> is_radon_measure alpha.
Proof.
move=> hl hc ha hrep hreg halt.
exact: (left_covariant_integral_radon opposite_group_lch hl (right_covariant_opposite_left hc)
  ha hrep hreg halt).
Qed.

(** Source for [right_covariant_measure_radon]: "Every ... (right) chi
    covariant measure over G is a Radon measure", Federer 2.7.14, p. 131.
    Direct formalisation for is_right_covariant_measure, with the
    alternative hypothesis of left_covariant_measure_radon. *)
Theorem right_covariant_measure_radon (chi : G -> R) (alpha : set G -> \bar R) :
  is_right_covariant_measure mul inv chi alpha ->
  (exists C, compact C /\ alpha C <> 0%E) \/ is_sigma_compact_space G -> is_radon_measure alpha.
Proof.
move=> [lambda [hl hc ha hrep hreg]] halt.
apply: (left_covariant_measure_radon opposite_group_lch (chi := fun g => chi (inv g))) halt.
by exists lambda; split=> //; exact: right_covariant_opposite_left.
Qed.

End RightCovariantMeasureRadon.
