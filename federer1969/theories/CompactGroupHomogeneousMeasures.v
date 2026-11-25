(** Federer (1969), 2.7.16, printed p. 139, example (6): "For every
    transitive action A of O(n) on a homogeneous space X, and each x in X,
    the measure (A^x)_# theta_n over X is invariant with [(A^x)_# theta_n] X
    = 1." Federer gives no proof. The assertion holds for every compact
    group G with its normalised Haar measure theta
    (CompactGroupHaarNormalisation.v), and this module proves it in that
    generality. (A^x)_# theta is the image measure of 2.1.2, p. 54
    (measure_pushforward). "Invariant" is the notion of 2.7.1, p. 122: the
    K(X) regular measure associated with a monotone invariant integral. The
    proof supplied here runs as follows. A^x is continuous and proper, so
    (A^x)_# theta represents the invariant integral (A^x)_#(lambda) on K(X)
    (2.5.19, p. 113; 2.7.12, p. 129), and it is a Radon measure (2.2.17, p.
    72), since theta is one (2.7.14, p. 131). The K(X) regular measure
    associated with (A^x)_#(lambda) is a Radon measure as well (2.7.15, p.
    133), and two Radon measures representing the same integral on K(X)
    coincide (radon_representations_coincide). The module also proves facts
    used with Federer's examples but not stated by him: a continuous
    transitive action of a compact group on a Hausdorff space makes it a
    homogeneous space in the sense of 2.7.1, p. 121 (the orbit maps are
    open), and any two invariant measures over X with total measure 1
    coincide, so that (A^x)_# theta does not depend on x; this justifies the
    definite article in "the O(n) invariant measures theta_{n,m},
    theta*_{n,m}, gamma_{n,m}". The local erratum has no entry for p. 139. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  constructive_ereal topology.
From Federer Require Import RealMetricBackground FunctionLatticeUP FunctionLatticeLevelFamilies
  FunctionLatticeLevelIntegral MonotoneDaniellIntegralUP DaniellIntegralNegation
  CompactSupportFunctionUP CompactSupportFunctionLattice CompactCutoffUP LocalizedCompactCutoffUP
  LocalizedCompactCutoff FunctionLatticeRegularityUP FunctionLatticeRegularUniqueness
  RegularDaniellRepresentation RealIntegralFunctionalUP MeasureUP MeasureBasic MeasurePushforward
  RadonMeasureUP ProperMapUP RadonProperPushforward DaniellSpacePushforward DaniellSpaceCompactSpace
  SubtypeCompactHausdorff TopologicalProductMaps TopologicalGroupUP TopologicalGroupLaws HomeomorphismUP
  HomogeneousSpaceUP HomogeneousSpaceLaws CovariantIntegralUP CovariantIntegralLaws HaarIntegralUP HaarIntegralLaws
  CovariantMeasureRadon HomogeneousCovariantMeasureRadon WeilCondition
  CompactGroupHaarNormalisation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section RadonUniqueness.
Variable R : realType.
Variable X : topologicalType.
Local Notation K := (@compactly_supported_continuous_functions R X).

(** Source for [radon_open_representation_le]: phi(V) <= psi(V) for
    open V when phi and psi are Radon measures representing the same
    integral on K(X), supporting "(A^x)_# theta_n over X is invariant",
    Federer 2.7.16, p. 139, through 2.2.5, p. 62, and 2.5.13, p. 106.
    Supporting lemma: each compact C contained in V lies in a set
    {x : f(x) > 1/2} with f in K(X)+ and spt f contained in V, and phi,
    psi agree on such sets (2.5.3, p. 94). *)
Lemma radon_open_representation_le (lambda : (X -> R) -> R) (phi psi : set X -> \bar R) :
  is_measure phi -> is_measure psi -> is_radon_measure phi ->
  is_real_integral_functional phi K lambda -> is_real_integral_functional psi K lambda ->
  forall V, open V -> (phi V <= psi V)%E.
Proof.
move=> hm hn hr hphi hpsi V hV.
apply: (radon_inner_least hr hV)=> C hC hCV.
have hh := radon_hausdorff hr; have hl := radon_locally_compact hr.
have hs := @localized_compact_cutoff_specification R X C V hh hl hC hV hCV.
set w := localized_compact_cutoff _ _ _ _ _ _ in hs.
have [[hwK hwr hw1] hws] := hs.
pose S := [set x | (2 : R)^-1 < w x].
have hS : function_lattice_strict_levels K S.
  exists w, (2 : R)^-1; split; last by split=> //; rewrite invr_gt0 ltr0n.
  by split=> // x; have /andP[] := hwr x.
have hCS : C `<=` S.
  by move=> x hx; rewrite /S /= (hw1 x hx) invf_lt1 ?ltr0n // ltr1n.
have hSV : S `<=` V.
  move=> x hx; apply: hws; apply: subset_closure=> /= hx0.
  by move: hx; rewrite /S /= hx0 ltNge invr_ge0 ler0n.
have he := represented_lattice_strict_level_unique
  (@compactly_supported_continuous_functions_lattice R X) hm hn hphi hpsi hS.
apply: le_trans (measure_mono hm hCS) _; rewrite he.
exact: (@measure_mono _ _ psi hn S V hSV).
Qed.

(** Source for [radon_representations_coincide]: two Radon measures
    over X representing the same integral on K(X) are equal, supporting
    "the measure (A^x)_# theta_n over X is invariant", Federer 2.7.16,
    p. 139, with 2.2.5, p. 62, and 2.5.14, p. 107. Supporting lemma:
    open sets are compared by radon_open_representation_le, arbitrary
    sets by outer regularity. *)
Theorem radon_representations_coincide (lambda : (X -> R) -> R) (phi psi : set X -> \bar R) :
  is_measure phi -> is_measure psi -> is_radon_measure phi -> is_radon_measure psi ->
  is_real_integral_functional phi K lambda -> is_real_integral_functional psi K lambda ->
  phi = psi.
Proof.
move=> hm hn hr hs hphi hpsi.
have hle (a b : set X -> \bar R) : is_measure a -> is_measure b -> is_radon_measure a ->
    is_radon_measure b -> is_real_integral_functional a K lambda ->
    is_real_integral_functional b K lambda -> forall S, (a S <= b S)%E.
  move=> ha hb hra hrb hia hib S; apply: (radon_outer_greatest hrb)=> V hV hSV.
  apply: le_trans (measure_mono ha hSV) _.
  exact: (radon_open_representation_le ha hb hra hia hib hV).
apply: funext=> S; apply/eqP; rewrite eq_le.
by rewrite (hle phi psi) // (hle psi phi).
Qed.

End RadonUniqueness.

Section CompactTransitive.
Variables G X : topologicalType.
Variables (mul : G -> G -> G) (inv : G -> G) (e : G) (A : G -> X -> X).
Hypothesis hT : is_topological_group mul inv e.
Hypothesis hGc : compact [set: G].
Hypothesis hX : hausdorff_space X.
Hypothesis hAc : continuous (fun p : G * X => A p.1 p.2).
Hypothesis hAm : forall g h x, A (mul g h) x = A g (A h x).
Hypothesis hAt : forall x y, exists g, A g x = y.

(** Source for [hG]: the group laws of G, Federer 2.7.1, p. 121, used
    in this section. *)
Let hG : is_group_laws mul inv e := topological_group_laws hT.

(** Source for [compact_transitive_unit]: A(e, x) = x, Federer 2.7.1,
    p. 121, for a transitive compatible action. Supporting lemma. *)
Lemma compact_transitive_unit x : A e x = x.
Proof. by have [g <-] := hAt x x; rewrite -hAm (group_mul1g hG). Qed.

(** Source for [compact_transitive_orbit_continuous]: A^x is
    continuous, Federer 2.7.1, p. 121. Supporting lemma. *)
Lemma compact_transitive_orbit_continuous x : continuous (orbit_map A x).
Proof.
have hp : continuous (fun g : G => (g, x)).
  by apply: topological_pair_continuous; [move=> ?|exact: cst_continuous].
by move=> g; have := continuous_comp (hp g) (@hAc (g, x)); exact.
Qed.

(** Source for [compact_transitive_orbit_open]: "for each x in X the
    map A^x ... is open", Federer 2.7.1, p. 121, for a continuous
    transitive action of a compact group on a Hausdorff space; supporting
    "transitive action A of O(n) on a homogeneous space X", 2.7.16,
    p. 139. Proof supplied: for U open in G the set Z of all g with
    A(g, x) in A^x(U) is the union of the open right translates U s,
    s in G^x; the complement of A^x(U) is the image of the compact set
    G ~ Z, hence closed. *)
Lemma compact_transitive_orbit_open x : is_open_map (orbit_map A x).
Proof.
move=> U hU.
pose Z := [set g | exists2 u, U u & A u x = A g x].
have hZ : Z = \bigcup_(s in isotropy_subgroup A x) ((fun h => mul h s) @` U).
  apply/seteqP; split=> g.
  - move=> [u hu hug]; exists (mul (inv u) g).
      by rewrite /isotropy_subgroup /= hAm -hug -hAm (group_mulVg hG) compact_transitive_unit.
    by exists u=> //; rewrite (group_mulKVg hG).
  - move=> [s hs [u hu <-]]; exists u=> //.
    by rewrite hAm hs.
have hZo : open Z.
  rewrite hZ; apply: bigcup_open=> s _.
  exact: (right_translation_open_map hT s).
have hcl : closed (orbit_map A x @` (~` Z)).
  apply: (compact_closed hX).
  apply: continuous_compact _ (subclosed_compact (open_closedC hZo) hGc (@subsetT _ _)).
  exact: continuous_subspaceT (compact_transitive_orbit_continuous (x:=x)).
have he : orbit_map A x @` U = ~` (orbit_map A x @` (~` Z)).
  apply/seteqP; split=> y.
  - by move=> [u hu <-] [g hg hgu]; apply: hg; exists u.
  - move=> hy; have [g hg] := hAt x y.
    have hgZ : Z g.
      by apply: contrapT=> hgZ; apply: hy; exists g.
    by have [u hu hug] := hgZ; exists u=> //; rewrite /orbit_map hug.
by rewrite he; exact: closed_openC hcl.
Qed.

(** Source for [compact_transitive_homogeneous]: a continuous
    transitive action of a compact topological group on a Hausdorff space
    makes it a homogeneous space in the sense of Federer 2.7.1, p. 121;
    supporting "every transitive action A of O(n) on a homogeneous space
    X", 2.7.16, p. 139. Supporting theorem. *)
Theorem compact_transitive_homogeneous : is_homogeneous_space mul A.
Proof.
split=> //.
- exact: compact_transitive_orbit_open.
- move=> x; apply/seteqP; split=> // y _; have [g hg] := hAt x y.
  by exists g.
Qed.

End CompactTransitive.

Section CompactHomogeneous.
Variables G X : topologicalType.
Variables (mul : G -> G -> G) (A : G -> X -> X).
Hypothesis hGc : compact [set: G].
Hypothesis hA : is_homogeneous_space mul A.

(** Source for [compact_homogeneous_space_compact]: a homogeneous space
    X of a compact group G is compact, being the image of G under the
    continuous map A^x (2.7.1, p. 121); supporting Federer 2.7.16,
    p. 139. Supporting lemma; for empty X there is nothing to prove. *)
Lemma compact_homogeneous_space_compact : compact [set: X].
Proof.
case: (pselect (exists x : X, True))=> [[x _]|hn].
- rewrite -(homogeneous_orbit_onto hA x).
  apply: continuous_compact _ hGc; exact: continuous_subspaceT (orbit_map_continuous hA x).
- have -> : [set: X] = set0.
    by apply/seteqP; split=> // y _; apply: hn; exists y.
  exact: compact0.
Qed.

(** Source for [compact_homogeneous_orbit_proper]: A^x is proper when G
    is compact and X Hausdorff, supporting the image measure
    (A^x)_# theta_n of Federer 2.7.16, p. 139 (2.2.17, p. 72; 2.5.19,
    p. 113). Supporting lemma: the inverse image of a compact set is
    closed in the compact space G. *)
Lemma compact_homogeneous_orbit_proper (x : X) : hausdorff_space X -> is_proper_map (orbit_map A x).
Proof.
move=> hX C hC; apply: (subclosed_compact _ hGc (@subsetT _ _)).
apply: preimage_closed; last exact: compact_closed hX hC.
by move=> g _; exact: orbit_map_continuous hA x g.
Qed.

End CompactHomogeneous.

(** Source for [is_normalised_invariant_measure]: "the measure
    (A^x)_# theta_n over X is invariant with [(A^x)_# theta_n] X = 1",
    Federer 2.7.16, p. 139: an invariant measure over X in the sense of
    2.7.1, p. 122, with total measure 1. Definition; for a homogeneous
    space of a compact group there is exactly one such measure
    (compact_invariant_measure_unique). *)
Definition is_normalised_invariant_measure (R : realType) (G : Type) (X : topologicalType)
    (A : G -> X -> X) (phi : set X -> \bar R) : Prop :=
  is_invariant_measure A phi /\ phi [set: X] = 1%E.

Section OrbitMeasures.
Variable R : realType.
Variables G X : topologicalType.
Variables (mul : G -> G -> G) (inv : G -> G) (e : G) (A : G -> X -> X).
Hypothesis hGc : is_locally_compact_hausdorff_group mul inv e.
Hypothesis hc : compact [set: G].
Hypothesis hA : is_homogeneous_space mul A.
Hypothesis hX : hausdorff_space X.
Local Notation KG := (@compactly_supported_continuous_functions R G).
Local Notation KX := (@compactly_supported_continuous_functions R X).

(** Source for [hXc]: X is compact, used in this section for Federer
    2.7.16, p. 139. *)
Let hXc : compact [set: X] := compact_homogeneous_space_compact hc hA.
(** Source for [hXl]: X is locally compact, the standing hypothesis of
    2.7.1, p. 121, used in this section. *)
Let hXl : locally_compact [set: X] := compact_space_locally_compact hXc.
(** Source for [hXs]: X is a countable union of compact sets, used in
    this section with 2.7.15, p. 133. *)
Let hXs : is_sigma_compact_space X.
Proof. by exists (fun _ => [set: X]); split=> // y _; exists 0%N. Qed.
(** Source for [hGs]: G is a countable union of compact sets, used in
    this section with 2.7.14, p. 131. *)
Let hGs : is_sigma_compact_space G.
Proof. by exists (fun _ => [set: G]); split=> // y _; exists 0%N. Qed.

(** Source for [orbit_pushforward_invariant_integral]: the integral
    (A^x)_#(lambda) on K(X) is a monotone invariant integral for every
    left Haar integral lambda of the compact group G, supporting
    "(A^x)_# theta_n over X is invariant", Federer 2.7.16, p. 139, as in
    2.7.12, p. 129. Supporting lemma. *)
Lemma orbit_pushforward_invariant_integral (x : X) (lambda : (G -> R) -> R) :
  is_left_haar_integral mul lambda ->
  is_monotone_daniell_integral KX (daniell_pushforward (orbit_map A x) lambda) /\
  is_covariant_on KX A (fun _ => 1) (daniell_pushforward (orbit_map A x) lambda).
Proof.
move=> [[_ hlaw] hM _].
have hf := orbit_map_continuous hA x.
have hp := compact_homogeneous_orbit_proper hc hA (x:=x) hX.
split; first exact (daniell_pushforward_monotone hf hp hM).
move=> v g hv; rewrite /daniell_pushforward.
have hvf := compactly_supported_compose hf hp hv.
rewrite -(hlaw _ g hvf); congr lambda; apply: funext=> h.
by rewrite /= /orbit_map /left_multiplication_action (homogeneous_action_compatible hA).
Qed.

(** Source for [compact_orbit_pushforward_invariant]: "For every
    transitive action A of O(n) on a homogeneous space X, and each x in
    X, the measure (A^x)_# theta_n over X is invariant with
    [(A^x)_# theta_n] X = 1", Federer 2.7.16, p. 139, for every compact
    group G and its normalised Haar measure theta. Direct formalisation;
    the proof is supplied (see the header). *)
Theorem compact_orbit_pushforward_invariant (theta : set G -> \bar R) (x : X) :
  is_normalised_haar_measure mul theta ->
  is_normalised_invariant_measure A (measure_pushforward (orbit_map A x) theta).
Proof.
move=> [htheta h1].
have [lambda [hlH hm hrep hreg]] := htheta.
have hf := orbit_map_continuous hA x.
have hp := compact_homogeneous_orbit_proper hc hA (x:=x) hX.
have [hnuM hnuC] := orbit_pushforward_invariant_integral x hlH.
set nu := daniell_pushforward (orbit_map A x) lambda in hnuM hnuC.
set psi := measure_pushforward (orbit_map A x) theta.
have hpsim : is_measure psi := measure_pushforward_is_measure _ hm.
have hpsirep : is_real_integral_functional psi KX nu := daniell_pushforward_integral hf hp hm hrep.
have hthetar : is_radon_measure theta.
  apply: (left_covariant_measure_radon hGc (chi := fun _ => 1)); last by right.
  exact: nonzero_invariant_measure_invariant htheta.
have hpsir : is_radon_measure psi := proper_continuous_radon_pushforward hm hthetar hX hXl hf hp.
have [phi [hphiC hphim hphirep hphireg _]] := covariant_measure_exists hnuM hnuC.
have hphir : is_radon_measure phi.
  exact: (homogeneous_covariant_measure_radon hGc hA hX hXl hphiC (or_intror hXs)).
have he : phi = psi := radon_representations_coincide hphim hpsim hphir hpsir hphirep hpsirep.
split; last by rewrite /psi /measure_pushforward preimage_setT.
by exists nu; split=> //; rewrite -he.
Qed.

(** Source for [compact_invariant_measure_unique]: two invariant
    measures over X with total measure 1 coincide, supporting "the O(n)
    invariant measures theta_{n,m} ..., theta*_{n,m} ..., gamma_{n,m}",
    Federer 2.7.16, p. 139. Proof supplied: by 2.7.11(2), p. 128, the
    associated invariant integrals nu_1, nu_2 satisfy nu_2 = c nu_1 on
    K(X); nu_i(1) = phi_i(X) = 1 gives c = 1, and the K(X) regular
    measure representing an integral is unique (2.5.3, p. 94). *)
Theorem compact_invariant_measure_unique (phi1 phi2 : set X -> \bar R) :
  is_normalised_invariant_measure A phi1 -> is_normalised_invariant_measure A phi2 -> phi1 = phi2.
Proof.
move=> [[nu1 [hM1 hC1 hm1 hrep1 hreg1]] h1] [[nu2 [hM2 hC2 hm2 hrep2 hreg2]] h2].
have hone := compact_space_constant_one R hXc.
have e1 : nu1 (fun _ => 1) = 1.
  by move: h1; rewrite (compact_representing_measure_total hXc hm1 hrep1); case.
have e2 : nu2 (fun _ => 1) = 1.
  by move: h2; rewrite (compact_representing_measure_total hXc hm2 hrep2); case.
have [x _] : exists x : X, True.
  apply: contrapT=> hn; move: h1; have -> : [set: X] = set0.
    by apply/seteqP; split=> // y _; apply: hn; exists y.
  by rewrite (measure_empty hm1)=> -[] /esym /eqP; rewrite oner_eq0.
have hchic : continuous ((fun _ => 1) : G -> real_line_metric R) by move=> g; exact: cvg_cst.
have hn1 : exists2 v, KX v & nu1 v <> 0.
  by exists (fun _ => 1)=> //; rewrite e1; exact/eqP/oner_neq0.
have hn2 : exists2 v, KX v & nu2 v <> 0.
  by exists (fun _ => 1)=> //; rewrite e2; exact/eqP/oner_neq0.
have hI1 : is_covariant_integral A (fun _ => 1) nu1.
  by split=> //; exact: monotone_daniell_is_daniell.
have hI2 : is_covariant_integral A (fun _ => 1) nu2.
  by split=> //; exact: monotone_daniell_is_daniell.
have hM1' : forall g h : G, (fun _ => 1 : R) (mul g h) = (fun _ => 1 : R) g * (fun _ => 1 : R) h.
  by move=> g h; rewrite mulr1.
have [c [_ hc2]] := covariant_integral_unique_multiple x hGc hA hX hM1' (fun _ => oner_neq0 R)
  hchic hI1 hI2 hn1 hn2.
have hc1 : c = 1 by move: (hc2 _ hone); rewrite e1 e2 mulr1.
have hrep2' : is_real_integral_functional phi2 KX nu1.
  by move=> v hv; rewrite -[nu1 v]mul1r -hc1 -hc2 //; exact: hrep2.
apply: funext=> S.
exact: (function_lattice_regular_representation_unique
  (@compactly_supported_continuous_functions_lattice R X) hm1 hm2 hrep1 hrep2' hreg1 hreg2 S).
Qed.

(** Source for [compact_orbit_pushforward_independent]: the measure
    (A^x)_# theta_n of Federer 2.7.16, p. 139, does not depend on x.
    Supporting corollary of compact_orbit_pushforward_invariant and
    compact_invariant_measure_unique. *)
Corollary compact_orbit_pushforward_independent (theta : set G -> \bar R) (x y : X) :
  is_normalised_haar_measure mul theta ->
  measure_pushforward (orbit_map A x) theta = measure_pushforward (orbit_map A y) theta.
Proof.
move=> h; apply: compact_invariant_measure_unique; exact: compact_orbit_pushforward_invariant.
Qed.

(** Source for [normalised_invariant_measure_exists]: "the O(n)
    invariant measures theta_{n,m} ..., theta*_{n,m} ..., gamma_{n,m}",
    Federer 2.7.16, p. 139: a nonempty homogeneous space X of a compact
    group G carries exactly one invariant measure with total measure 1,
    and it equals (A^x)_# theta for every x in X and the normalised Haar
    measure theta of G. Direct formalisation of the existence and
    uniqueness asserted by the definite article; the point x0 expresses
    that X is nonempty, without which no measure has total measure 1. *)
Theorem normalised_invariant_measure_exists (x0 : X) :
  exists phi : set X -> \bar R, [/\ is_normalised_invariant_measure A phi,
    forall psi, is_normalised_invariant_measure A psi -> psi = phi &
    forall theta x, is_normalised_haar_measure mul theta ->
      measure_pushforward (orbit_map A x) theta = phi].
Proof.
have [theta htheta] := normalised_haar_measure_exists R hGc hc.
have hphi := compact_orbit_pushforward_invariant x0 htheta.
exists (measure_pushforward (orbit_map A x0) theta); split=> //.
  by move=> psi hpsi; exact: compact_invariant_measure_unique.
move=> theta' y h'; apply: compact_invariant_measure_unique=> //.
exact: compact_orbit_pushforward_invariant.
Qed.

End OrbitMeasures.
