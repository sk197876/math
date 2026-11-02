(** Federer (1969), 2.7.4, printed pp. 124-125: two facts of general
    topology used in the proof of the theorem. First, "use the uniform
    continuity of r_1, r_2 to obtain beta in B with |r_j(x) - r_j(y)| <=
    epsilon whenever (x,y) in beta": every member of K(X) is uniformly
    continuous with respect to a uniformity which induces the topology of X.
    The usual argument covers the compact support of r by finitely many open
    sets on which r varies by less than epsilon/2, and takes a symmetric
    entourage D with D o D inside the corresponding entourages. Second, the
    closed sets S(beta) = Closure {p_v: (spt v) x (spt v) subset beta} are
    nonempty because for every entourage beta and every point a there is a
    nonzero v in K(X)+ with (spt v) x (spt v) subset beta, namely a cutoff
    equal to 1 at a with support in a neighbourhood U of a such that U x U
    subset beta (2.5.13-2.5.14, pp. 106-108). The uniformities are those of
    UniformActionUP.v (2.7.3, p. 123). *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets reals
  topology.
From mathcomp.analysis.normedtype_theory Require Import num_normedtype.
From mathcomp Require Import ring lra.
From Federer Require Import RealMetricBackground FunctionLatticeUP CompactSupportFunctionUP
  CompactCutoffUP LocalizedCompactCutoffUP LocalizedCompactCutoff CompactFiniteCover
  UniformActionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope relation_scope.

Section UniformitySupport.
Variable R : realType.
Variable X : topologicalType.
Variable E : set_system (X * X).
Hypothesis hE : is_uniformity E.
Hypothesis hnb : uniformity_induces_topology E.
Local Notation K := (@compactly_supported_continuous_functions R X).

(** Source for [uniformity_entourage_section]: the sections
    {y: (x,y) in D} of entourages are neighbourhoods of x when the
    uniformity induces the topology, Federer 2.7.3, p. 123. Supporting
    lemma for 2.7.4, pp. 124-125. *)
Lemma uniformity_entourage_section x D : E D -> nbhs x (xsection D x).
Proof. by move=> hD; rewrite hnb; exists D. Qed.

(** Source for [uniformity_nbhs_entourage]: every neighbourhood of x
    contains a section {y: (x,y) in D} of an entourage, Federer 2.7.3,
    p. 123. Supporting lemma for 2.7.4, pp. 124-125. *)
Lemma uniformity_nbhs_entourage x N : nbhs x N -> exists2 D, E D & xsection D x `<=` N.
Proof. by rewrite hnb; case=> D hD hDN; exists D. Qed.

(** Source for [compactly_supported_uniformly_continuous]: "use the
    uniform continuity of r_1, r_2 to obtain beta in B with
    |r_j(x) - r_j(y)| <= epsilon whenever (x,y) in beta", Federer 2.7.4,
    p. 124: every member of K(X) is uniformly continuous with respect
    to a uniformity inducing the topology of X. Supporting theorem. *)
Theorem compactly_supported_uniformly_continuous (r : X -> R) (eps : R) : K r -> 0 < eps ->
  exists2 D, E D & forall x y, D (x, y) -> `|r x - r y| <= eps.
Proof.
move=> [hrc hrK] he.
have hF := uniformity_filter hE.
have he2 : 0 < eps / 2 by rewrite divr_gt0.
have hloc x : exists D, E D /\ forall y, D (x, y) -> `|r x - r y| < eps / 2.
  have hb := nbhsx_ballx (r x : real_line_metric R) (eps / 2) he2.
  have hN := hrc x _ hb; rewrite real_line_ball_distance in hN.
  have [D hD hDN] := uniformity_nbhs_entourage hN.
  by exists D; split=> // y hy; apply: hDN; apply/xsectionP.
have /choice [D hD] := hloc.
have hsplit x : exists D', E D' /\ D' \; D' `<=` D x.
  by have [D' hD' hD'D] := uniformity_split hE (hD x).1; exists D'.
have /choice [D' hD'] := hsplit.
pose O x := (xsection (D' x) x)°.
have hO x : open (O x) := @open_interior X _.
have hxO x : O x x := uniformity_entourage_section x (hD' x).1.
have [F hFsub hFcov] := @compact_open_finite_cover X X (real_function_support r) O _ hrK
  (fun x _ => hO x) (fun x hx => ex_intro2 _ (fun j => O j x) x hx (hxO x)).
pose Dc := \bigcap_(x in [set` F]) D' x.
have hDc : E Dc := @filter_bigI _ X F D' E hF (fun x _ => (hD' x).1).
have hDci : E Dc^-1 := uniformity_inverse hE hDc.
exists (Dc `&` Dc^-1); first exact: filterI hDc hDci.
have key x y : real_function_support r x -> Dc (x, y) -> `|r x - r y| < eps.
  move=> hx hxy; have [z hz hOz] := hFcov x hx.
  have hzx : D' z (z, x) by apply/xsectionP; exact: interior_subset hOz.
  have hxy' : D' z (x, y) := hxy z hz.
  have hzy : D z (z, y) by apply: (hD' z).2; exists x.
  have hxx : D' z (x, x) by apply: (uniformity_diagonal hE (hD' z).1).
  have hzx2 : D z (z, x) by apply: (hD' z).2; exists x.
  have h1 := (hD z).2 y hzy; have h2 := (hD z).2 x hzx2.
  have -> : r x - r y = (r z - r y) - (r z - r x) by ring.
  by apply: le_lt_trans (ler_normB _ _) _; lra.
move=> x y [hxy hyx].
case: (pselect (real_function_support r x))=> hx; first exact: ltW (key x y hx hxy).
case: (pselect (real_function_support r y))=> hy.
  by rewrite distrC; exact: ltW (key y x hy hyx).
by rewrite (real_function_zero_off_support hx) (real_function_zero_off_support hy) subr0 normr0 ltW.
Qed.

(** Source for [entourage_small_support_function]: the sets
    {p_v: (spt v) x (spt v) subset beta} of Federer 2.7.4, p. 124, are
    nonempty: for every entourage beta and every point a there is
    v in K(X)+ with v(a) = 1 and (spt v) x (spt v) subset beta. Choose
    an entourage D with D o D subset beta and a cutoff equal to 1 at a
    with support in the interior of {y: (a,y) in D cap D^{-1}}
    (2.5.14, pp. 107-108). Supporting theorem. *)
Theorem entourage_small_support_function (beta : set (X * X)) (a : X) :
  hausdorff_space X -> locally_compact [set: X] -> E beta ->
  exists v : X -> R, [/\ positive_function_lattice K v, v a = 1 &
    real_function_support v `*` real_function_support v `<=` beta].
Proof.
move=> hh hl hbeta.
have hF := uniformity_filter hE.
have [D hD hDD] := uniformity_split hE hbeta.
have hD2 : E (D `&` D^-1) := @filterI _ E hF _ _ hD (uniformity_inverse hE hD).
pose U := (xsection (D `&` D^-1) a)°.
have hU : open U := @open_interior X _.
have haU : U a := uniformity_entourage_section a hD2.
have hK : compact [set a] := @compact_set1 X a.
have hKU : [set a] `<=` U by move=> x ->.
have [[hvK hv01 hv1] hvU] := localized_compact_cutoff_specification R hh hl hK hU hKU.
exists (localized_compact_cutoff R hh hl hK hU hKU); split.
- by split=> // x; have /andP [] := hv01 x.
- exact: hv1.
- move=> [y z] [hy hz] /=.
  have /interior_subset /xsectionP [_ hya] := hvU y hy.
  have /interior_subset /xsectionP [haz _] := hvU z hz.
  by apply: hDD; exists a.
Qed.

End UniformitySupport.
