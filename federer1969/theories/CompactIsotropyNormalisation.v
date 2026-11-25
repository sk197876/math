(** Federer (1969), 2.7.12, printed p. 129: "If lambda is a left chi
    covariant integral of G, then A^x_#(lambda) is a chi covariant integral
    on K(X), which equals the function nu constructed in 2.7.11 provided mu
    is chosen so that mu(1) = 1, because [A^x_#(lambda) o mu^x] u =
    lambda[mu^x(u) o A^x] = lambda_g[mu_s u(g s)] = mu_s[lambda_g u(g s)] =
    mu_s[lambda(u)] = lambda(u) whenever u in K(G)." Standing hypotheses of
    2.7.1, p. 121: G is a locally compact Hausdorff topological group, X a
    locally compact Hausdorff homogeneous space of G, and the isotropy group
    G^x is compact; mu is a left Haar integral of G^x and mu^x the
    epimorphism of 2.7.10, p. 127 (is_coset_integral).
    CompactIsotropyIntegrals.v proves the displayed computation for every mu
    with mu(1) = 1. This module proves that such a mu exists: if lambda' is
    a left Haar integral of the compact group G^x (2.7.5, p. 125), then the
    constant function 1 belongs to K(G^x), lambda'(1) > 0, and mu =
    lambda'(1)^{-1} lambda' is a left Haar integral with mu(1) = 1
    (CompactGroupHaarNormalisation.v). For this mu the identity holds
    (compact_isotropy_normalised_coset), and A^x_#(lambda) equals the chi
    covariant integral nu with nu o mu^x = lambda constructed in 2.7.11, pp.
    128–129, which exists because Weil's condition holds and lambda is right
    Delta_G chi^{-1} covariant by 2.7.9(3)
    (compact_isotropy_normalised_factor). The local erratum has no entry for
    p. 129. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets functions
  reals constructive_ereal topology normedtype.
From Federer Require Import RealMetricBackground FunctionLatticeUP DaniellIntegralUP
  MonotoneDaniellIntegralUP CompactSupportFunctionUP DaniellSpacePushforward TopologicalGroupUP
  TopologicalGroupLaws HomogeneousSpaceUP HomogeneousSpaceLaws CovariantIntegralUP HaarIntegralUP
  HaarIntegralExistence ModularFunctionUP ModularFunction CovariantHaarCharacterisation
  SubtypeCompactHausdorff IsotropyGroupTopology CosetIntegralUP CosetIntegralExistence
  CovariantIntegralFactorisation WeilCondition CompactGroupHaarNormalisation
  CompactIsotropyIntegrals.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section CompactIsotropyNormalised.
Variable R : realType.
Variables G X : topologicalType.
Variables (mul : G -> G -> G) (inv : G -> G) (e : G) (A : G -> X -> X) (x : X).
Hypothesis hG : is_locally_compact_hausdorff_group mul inv e.
Hypothesis hA : is_homogeneous_space mul A.
Hypothesis hX : hausdorff_space X.
Local Notation S := (isotropy_subgroup A x).
Hypothesis hSc : compact S.
Local Notation KG := (@compactly_supported_continuous_functions R G).
Local Notation KX := (@compactly_supported_continuous_functions R X).
Variables (mulS : S -> S -> S) (invS : S -> S) (eS : S).
Hypothesis hR : is_subgroup_restriction mul inv e S mulS invS eS.

(** Source for [hScl]: G^x is closed in G, Federer 2.7.1, pp. 121–122,
    since X is Hausdorff. *)
Let hScl : closed S := isotropy_subgroup_closed hA hX.
(** Source for [hSG]: G^x is a locally compact Hausdorff group,
    Federer 2.7.10, p. 127. *)
Let hSG := subgroup_restriction_locally_compact_hausdorff hR hG hScl.
(** Source for [hSall]: the compact isotropy group G^x of Federer
    2.7.12, p. 129, is a compact space in its relative topology. *)
Let hSall : compact [set: S] := set_type_compact_whole hSc.

(** Source for [compact_isotropy_normalised_haar_exists]: "provided mu
    is chosen so that mu(1) = 1", Federer 2.7.12, p. 129: the compact
    group G^x has a left Haar integral mu with mu(1) = 1. Proof
    supplied: lambda'(1)^{-1} lambda' for a left Haar integral lambda'
    of G^x (2.7.5, p. 125), where lambda'(1) > 0. *)
Theorem compact_isotropy_normalised_haar_exists :
  exists mu : (S -> R) -> R, is_left_haar_integral mulS mu /\ mu (fun _ => 1) = 1.
Proof.
have [l hl] := left_haar_integral_exists R hSG.
have hpos := left_haar_integral_total_positive hSG hSall hl.
have hinv : 0 < (l (fun _ => 1))^-1 by rewrite invr_gt0.
exists (fun u => (l (fun _ => 1))^-1 * l u); split.
- exact: nonzero_invariant_integral_scale hinv hl.
- by rewrite mulVf ?gt_eqF.
Qed.

Variable chi : G -> R.
Hypothesis hchiM : forall g h, chi (mul g h) = chi g * chi h.
Hypothesis hchic : continuous (chi : G -> real_line_metric R).
Hypothesis hchip : forall g, 0 < chi g.
Variable lambda : (G -> R) -> R.
Hypothesis hlc : is_left_covariant_integral mul chi lambda.

(** Source for [compact_isotropy_normalised_coset]: "provided mu is
    chosen so that mu(1) = 1, because [A^x_#(lambda) o mu^x] u = ...
    = lambda(u) whenever u in K(G)", Federer 2.7.12, p. 129: there are a
    left Haar integral mu of G^x with mu(1) = 1 and the epimorphism mu^x
    of 2.7.10, p. 127, for this mu, and the identity holds for them.
    Direct formalisation. *)
Theorem compact_isotropy_normalised_coset :
  exists (mu : (S -> R) -> R) (M : (G -> R) -> X -> R),
    [/\ is_left_haar_integral mulS mu, mu (fun _ => 1) = 1, is_coset_integral mul A x mu M &
      forall u, KG u -> daniell_pushforward (orbit_map A x) lambda (M u) = lambda u].
Proof.
have [mu [hmu h1]] := compact_isotropy_normalised_haar_exists.
have [M hM] := coset_integral_exists hG hA hX hR hmu.
exists mu, M; split=> // u hu.
exact: (compact_isotropy_pushforward_coset hG hA hX hSc hR hmu hM hchiM hchic hchip hlc h1 hu).
Qed.

(** Source for [compact_isotropy_normalised_factor]: "If lambda is a
    left chi covariant integral of G, then A^x_#(lambda) is a chi
    covariant integral on K(X), which equals the function nu constructed
    in 2.7.11 provided mu is chosen so that mu(1) = 1", Federer 2.7.12,
    p. 129: for the normalised mu, the function nu of 2.7.11, p. 129,
    with nu o mu^x = lambda exists and is a chi covariant integral, and
    A^x_#(lambda) = nu on K(X). Direct formalisation; the existence of nu
    uses Weil's condition (compact_isotropy_weil_condition) and the right
    Delta_G chi^{-1} covariance of lambda (2.7.9(3), p. 127), as in
    2.7.11. *)
Theorem compact_isotropy_normalised_factor (hXl : locally_compact [set: X]) :
  exists (mu : (S -> R) -> R) (M : (G -> R) -> X -> R) (nu : (X -> R) -> R),
    [/\ is_left_haar_integral mulS mu, mu (fun _ => 1) = 1, is_coset_integral mul A x mu M &
      [/\ forall u, KG u -> nu (M u) = lambda u, is_covariant_integral A chi nu &
        forall v, KX v -> daniell_pushforward (orbit_map A x) lambda v = nu v]].
Proof.
have [mu [M [hmu h1 hM _]]] := compact_isotropy_normalised_coset.
have [DG hDG] := modular_function_exists R hG.
have [DS hDS] := modular_function_exists R hSG.
have hW := compact_isotropy_weil_condition hG hA hX hSc hR hDG hDS hchiM hchic hchip.
have hlD := covariant_integral_daniell hlc.
have hchi0 g : chi g != 0 := lt0r_neq0 (hchip g).
have hlr := left_covariant_right_modular hG hlD hchiM hchi0 hchic hDG hlc.
pose psi g := DG g * (chi g)^-1.
have hpsic : continuous (psi : G -> real_line_metric R).
  move=> g; apply: (@continuousM R G); first exact: (modular_function_continuous hDG).
  by apply: (@continuousV R G chi g); [exact: hchi0|exact: hchic].
have hpsiS (t : S) : psi (set_val t) = DS t.
  by rewrite /psi -(hW t) mulrC mulKf.
have [nu hfac] := coset_integral_factor_exists hG hA hX hR hmu hM hDS hlD hpsic hpsiS
  (covariant_integral_law hlr) hXl.
have hnu := coset_integral_factor_covariant hG hA hX hR hmu hM hlD hXl (covariant_integral_law hlc) hfac.
have heq := compact_isotropy_pushforward_factor hG hA hX hSc hR hmu hM hchiM hchic hchip hlc h1 hfac.
by exists mu, M, nu; split.
Qed.

End CompactIsotropyNormalised.
