(** Federer (1969), 2.7.13, printed pp. 130–131: "Suppose gamma is the K(X)
    regular measure associated with a monotone Daniell integral nu, x in X,
    beta is the K(G^x) regular measure associated with a left Haar integral
    mu of G^x, and alpha is the K(G) regular measure associated with the
    monotone Daniell integral nu o mu^x (see 2.7.10). Then there exists a
    linear epimorphism beta^x: L_1(alpha) -> L_1(gamma) such that, for each
    alpha summable function u, beta^x(u)(g x) = integral u(g s) d beta s
    whenever g in G, integral beta^x(u) d gamma = integral u d alpha." This
    module states the theorem. The K(X) regular measure associated with nu
    is a measure gamma which represents nu on K(X) (2.5.2, p. 92) and is
    K(X) regular (2.5.3, p. 94); likewise for alpha and beta, and mu^x is a
    map M with is_coset_integral (2.7.10). L_1 is the total-domain space
    total_scalar_lp phi 1 of the erratum, p. 2 (book p. 98 line 10), whose
    members are the phi summable real functions (TotalLoneSummability.v).
    Since a member of L_1(gamma) is determined only up to gamma almost
    equality, beta^x is linear, is defined on alpha almost equal functions,
    and is onto in this sense, and the fibre formula holds at gamma almost
    all points (CosetLoneIntegralUP.v). The specification determines
    beta^x(u) up to gamma null functions (coset_lone_integral_unique). Of
    Federer's hypotheses, the monotonicity of nu and the K(G^x) regularity
    of beta are not used: they are implied by, respectively irrelevant to,
    the representations used here. Of the standing hypotheses on X only the
    Hausdorff property is used, through 2.7.10. The local erratum has no
    entry for pp. 130–131. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets functions reals
  constructive_ereal topology.
From Federer Require Import MeasureUP MeasureAlmostUP MeasureIntegralUP SummableRealFunctionUP
  TotalScalarLpUP TotalLoneSummability FunctionLatticeUP FunctionLatticeRegularityUP
  RealIntegralFunctionalUP CompactSupportFunctionUP TopologicalGroupUP HomogeneousSpaceUP HaarIntegralUP
  IsotropyGroupTopology CosetIntegralUP CosetLoneIntegralUP CosetLoneIntegralLaws
  CosetLoneIntegralExistence CosetLoneIntegralOnto.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section CosetLoneIntegralEpimorphism.
Variable R : realType.
Variables G X : topologicalType.
Variables (mul : G -> G -> G) (inv : G -> G) (e : G) (A : G -> X -> X) (x : X).
Hypothesis hG : is_locally_compact_hausdorff_group mul inv e.
Hypothesis hA : is_homogeneous_space mul A.
Hypothesis hX : hausdorff_space X.
Local Notation S := (isotropy_subgroup A x).
Local Notation KG := (@compactly_supported_continuous_functions R G).
Local Notation KX := (@compactly_supported_continuous_functions R X).
Local Notation KS := (@compactly_supported_continuous_functions R S).
Variables (mulS : S -> S -> S) (invS : S -> S) (eS : S).
Hypothesis hR : is_subgroup_restriction mul inv e S mulS invS eS.
Variable mu : (S -> R) -> R.
Hypothesis hmu : is_left_haar_integral mulS mu.
Variable M : (G -> R) -> X -> R.
Hypothesis hM : is_coset_integral mul A x mu M.
Variable nu : (X -> R) -> R.
Variables (alpha : set G -> \bar R) (beta : set S -> \bar R) (gamma : set X -> \bar R).
Hypotheses (ha : is_measure alpha) (hb : is_measure beta) (hc : is_measure gamma).
Hypothesis harep : is_real_integral_functional alpha KG (fun u => nu (M u)).
Hypothesis hareg : is_function_lattice_regular KG alpha.
Hypothesis hbrep : is_real_integral_functional beta KS mu.
Hypothesis hcrep : is_real_integral_functional gamma KX nu.
Hypothesis hcreg : is_function_lattice_regular KX gamma.

(** Source for [coset_lone_integral_epimorphism]: Federer 2.7.13,
    pp. 130–131, "Then there exists a linear epimorphism
    beta^x: L_1(alpha) -> L_1(gamma) such that, for each alpha summable
    function u, beta^x(u)(g x) = integral u(g s) d beta s whenever
    g in G, integral beta^x(u) d gamma = integral u d alpha." Direct
    formalisation, with L_1 the total-domain spaces and the linearity,
    the well-definedness on L_1(alpha) and the surjectivity modulo
    null functions; the last conclusion is "mu^x = T|K(G)" from the
    proof. *)
Theorem coset_lone_integral_epimorphism :
  exists B : (G -> R) -> X -> R,
  [/\ is_coset_lone_integral mul A x alpha beta gamma B,
    forall u, total_scalar_lp alpha 1%E u -> total_scalar_lp gamma 1%E (B u),
    (forall u v, total_scalar_lp alpha 1%E u -> total_scalar_lp alpha 1%E v ->
       measure_almost_everywhere gamma [set y | B (fun g => u g + v g) y = B u y + B v y]) /\
    (forall c u, total_scalar_lp alpha 1%E u ->
       measure_almost_everywhere gamma [set y | B (fun g => c * u g) y = c * B u y]),
    (forall u v, total_scalar_lp alpha 1%E u -> total_scalar_lp alpha 1%E v ->
       measure_almost_everywhere alpha [set g | u g = v g] ->
       measure_almost_everywhere gamma [set y | B u y = B v y]) /\
    (forall v, total_scalar_lp gamma 1%E v ->
       exists2 u, total_scalar_lp alpha 1%E u & measure_almost_everywhere gamma [set y | B u y = v y]) &
    forall u, KG u -> measure_almost_everywhere gamma [set y | B u y = M u y]].
Proof.
have [B hB] := coset_lone_integral_exists hG hA hX hM ha hb hc harep hareg hbrep hcrep.
have hs u : total_scalar_lp alpha 1%E u -> summable_real_functions alpha u.
  by move=> hu; have h := total_lone_summable_real ha hu; exact: h.
exists B; split.
- exact: hB.
- by move=> u hu; have h := coset_lone_integral_lone ha hc hB hu; exact: h.
- split=> [u v hu hv|c u hu].
  + have h := coset_lone_integral_add hA ha hb hc hB (hs u hu) (hs v hv); exact: h.
  + have h := coset_lone_integral_scale hA ha hb hc hB c (hs u hu); exact: h.
- split=> [u v hu hv huv|v hv].
  + have h := coset_lone_integral_almost_equal hA ha hb hc hB (hs u hu) (hs v hv) huv; exact: h.
  + have hv' : summable_real_functions gamma v.
      by have h := total_lone_summable_real hc hv; exact: h.
    have [u hu hBu] := coset_lone_integral_onto hG hA hX hR hmu hM ha hb hc harep hbrep hcrep hcreg hB hv'.
    by exists u=> //; have h := summable_real_total_lone ha hu; exact: h.
- move=> u hu; have h := coset_lone_integral_extends hG hA hX hM hc harep hbrep hB hu; exact: h.
Qed.

End CosetLoneIntegralEpimorphism.
