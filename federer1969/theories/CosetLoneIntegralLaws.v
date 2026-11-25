(** Federer (1969), 2.7.13, printed p. 130: consequences of the two laws of
    the map beta^x: L_1(alpha) -> L_1(gamma), "beta^x(u)(g x) = integral u(g
    s) d beta s whenever g in G, integral beta^x(u) d gamma = integral u d
    alpha", specified by is_coset_lone_integral (CosetLoneIntegralUP.v).
    Every point of X is g x for some g in G (2.7.1, p. 121), so the fibre
    formula determines beta^x(u) at gamma almost all points; hence beta^x(u)
    is unique up to gamma almost equality, and beta^x is linear modulo gamma
    null functions. The proof of 2.7.13 records that "T(w) and T(u) are
    gamma almost equal to 0" when 0 <= u <= w and integral w d alpha = 0; in
    the same way beta^x(u) and beta^x(v) are gamma almost equal when u and v
    are alpha almost equal, so that beta^x is defined on L_1(alpha) as a
    space of functions modulo alpha null functions. The order laws and
    |beta^x(u)| <= beta^x(|u|) follow from the fibre formula and the
    monotonicity of the integral (2.4.4(5), p. 82). The local erratum has no
    entry for pp. 130–131. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets functions reals
  constructive_ereal topology.
From Federer Require Import MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasureIntegralUP
  MeasureIntegralUniqueness SummableRealFunctionUP SummableRealArithmetic LatticeL1ApproximationLaws
  TotalScalarLpUP TotalLoneSummability HomogeneousSpaceUP HomogeneousSpaceLaws SummableIncreasingLimits
  CosetLoneIntegralUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section CosetFibreIntegral.
Variable R : realType.
Variables G X : topologicalType.
Variables (mul : G -> G -> G) (A : G -> X -> X) (x : X).
Hypothesis hA : is_homogeneous_space mul A.
Local Notation S := (isotropy_subgroup A x).
Variable beta : set S -> \bar R.
Hypothesis hb : is_measure beta.

(** Source for [coset_fibre_integral_unique]: the value of
    "integral u(g s) d beta s" at a point g x does not depend on the
    choice of the representation g x, once the fibre formula of
    Federer 2.7.13, p. 130, holds there: two values r and r' given by
    the formula agree, because some g in G satisfies g x = y
    (2.7.1, p. 121). Supporting lemma. *)
Lemma coset_fibre_integral_unique u y r r' :
  coset_fibre_integral mul A x beta u y r -> coset_fibre_integral mul A x beta u y r' -> r = r'.
Proof.
move=> h h'; have [g hg] := homogeneous_transitive hA x y.
by have := measure_integral_unique (h g hg) (h' g hg); case.
Qed.

(** Source for [coset_fibre_integral_add]: "integral (u + v)(g s)
    d beta s = integral u(g s) d beta s + integral v(g s) d beta s",
    the additivity of the integral (2.4.4(4), p. 82) on each coset,
    supporting the linearity of beta^x in Federer 2.7.13, p. 130.
    Supporting lemma. *)
Lemma coset_fibre_integral_add u v y r r' :
  coset_fibre_integral mul A x beta u y r -> coset_fibre_integral mul A x beta v y r' ->
  coset_fibre_integral mul A x beta (fun g => u g + v g) y (r + r').
Proof.
move=> hu hv g hg; have hs := real_total_integral_add hb (hu g hg) (hv g hg); exact: hs.
Qed.

(** Source for [coset_fibre_integral_scale]: "integral c u(g s)
    d beta s = c integral u(g s) d beta s", the homogeneity of the
    integral (2.4.4(3), p. 82) on each coset, supporting the
    linearity of beta^x in Federer 2.7.13, p. 130. Supporting lemma. *)
Lemma coset_fibre_integral_scale c u y r :
  coset_fibre_integral mul A x beta u y r ->
  coset_fibre_integral mul A x beta (fun g => c * u g) y (c * r).
Proof. move=> hu g hg; have hs := real_total_integral_scale hb c (hu g hg); exact: hs. Qed.

(** Source for [coset_fibre_integral_le]: the monotonicity of the
    integral (2.4.4(5), p. 82) on each coset: if u <= v, then the fibre
    values satisfy r <= r'; supporting Federer 2.7.13, p. 130.
    Supporting lemma. *)
Lemma coset_fibre_integral_le u v y r r' : (forall g, u g <= v g) ->
  coset_fibre_integral mul A x beta u y r -> coset_fibre_integral mul A x beta v y r' -> r <= r'.
Proof.
move=> huv hu hv; have [g hg] := homogeneous_transitive hA x y.
have h := summable_total_integral_le_almost hb (hu g hg) (hv g hg)
  (measure_almost_everywhere_mono hb (fun s _ => huv _) (measure_almost_everywhere_true hb)).
by rewrite lee_fin in h.
Qed.

(** Source for [coset_fibre_integral_nonnegative]: the integral of a
    nonnegative function on a coset is nonnegative (2.4.4(2), p. 82);
    supporting Federer 2.7.13, p. 130. Supporting lemma. *)
Lemma coset_fibre_integral_nonnegative u y r : (forall g, 0 <= u g) ->
  coset_fibre_integral mul A x beta u y r -> 0 <= r.
Proof.
move=> hu0 hu.
have h0 : coset_fibre_integral mul A x beta (fun _ => 0) y 0.
  by move=> g _; exact: real_total_zero_integral hb.
exact (coset_fibre_integral_le hu0 h0 hu).
Qed.

End CosetFibreIntegral.

Section CosetLoneIntegralLaws.
Variable R : realType.
Variables G X : topologicalType.
Variables (mul : G -> G -> G) (A : G -> X -> X) (x : X).
Hypothesis hA : is_homogeneous_space mul A.
Local Notation S := (isotropy_subgroup A x).
Variables (alpha : set G -> \bar R) (beta : set S -> \bar R) (gamma : set X -> \bar R).
Hypotheses (ha : is_measure alpha) (hb : is_measure beta) (hc : is_measure gamma).
Variable B : (G -> R) -> X -> R.
Hypothesis hB : is_coset_lone_integral mul A x alpha beta gamma B.

(** Source for [coset_lone_integral_summable]: "beta^x: L_1(alpha) ->
    L_1(gamma)", Federer 2.7.13, p. 130: beta^x(u) is gamma summable
    for each alpha summable u, by "integral beta^x(u) d gamma =
    integral u d alpha". Direct consequence of the specification. *)
Lemma coset_lone_integral_summable u :
  summable_real_functions alpha u -> summable_real_functions gamma (B u).
Proof. by move=> [a hu]; exists a; have h := coset_lone_integral_identity hB hu; exact: h. Qed.

(** Source for [coset_lone_integral_lone]: "beta^x: L_1(alpha) ->
    L_1(gamma)", Federer 2.7.13, p. 130, for the total-domain spaces
    L_1 of the erratum, p. 2 (book p. 98 line 10). Direct consequence
    of the specification. *)
Theorem coset_lone_integral_lone u : total_scalar_lp alpha 1%E u -> total_scalar_lp gamma 1%E (B u).
Proof.
move=> hu; apply: (summable_real_total_lone hc); apply: coset_lone_integral_summable.
have h := total_lone_summable_real ha hu; exact: h.
Qed.

(** Source for [coset_lone_integral_unique]: beta^x(u) is determined
    gamma almost everywhere by "beta^x(u)(g x) = integral u(g s)
    d beta s whenever g in G", Federer 2.7.13, p. 130; any two maps
    with the two laws agree gamma almost everywhere on each alpha
    summable function. Supporting theorem, making precise the
    sense in which beta^x is a map into L_1(gamma). *)
Theorem coset_lone_integral_unique (B' : (G -> R) -> X -> R) :
  is_coset_lone_integral mul A x alpha beta gamma B' -> forall u, summable_real_functions alpha u ->
  measure_almost_everywhere gamma [set y | B u y = B' u y].
Proof.
move=> hB' u hu.
apply: (measure_almost_everywhere_mono hc _ (measure_almost_everywhere_and hc
  (coset_lone_integral_fibre hB hu) (coset_lone_integral_fibre hB' hu)))=> y /= [h h'].
exact (coset_fibre_integral_unique hA h h').
Qed.

(** Source for [coset_lone_integral_add]: beta^x is additive, part of
    "linear epimorphism", Federer 2.7.13, p. 130: beta^x(u + v) =
    beta^x(u) + beta^x(v) gamma almost everywhere, by the fibre
    formula and the additivity of the integral on each coset. Direct
    consequence of the specification. *)
Theorem coset_lone_integral_add u v : summable_real_functions alpha u -> summable_real_functions alpha v ->
  measure_almost_everywhere gamma [set y | B (fun g => u g + v g) y = B u y + B v y].
Proof.
move=> hu hv; have huv := summable_real_add ha hu hv.
have h3 := measure_almost_everywhere_and hc (coset_lone_integral_fibre hB huv)
  (measure_almost_everywhere_and hc (coset_lone_integral_fibre hB hu) (coset_lone_integral_fibre hB hv)).
apply: (measure_almost_everywhere_mono hc _ h3)=> y /= [h [h1 h2]].
exact (coset_fibre_integral_unique hA h (coset_fibre_integral_add hb h1 h2)).
Qed.

(** Source for [coset_lone_integral_scale]: beta^x is homogeneous,
    part of "linear epimorphism", Federer 2.7.13, p. 130:
    beta^x(c u) = c beta^x(u) gamma almost everywhere, for every real
    c. Direct consequence of the specification. *)
Theorem coset_lone_integral_scale c u : summable_real_functions alpha u ->
  measure_almost_everywhere gamma [set y | B (fun g => c * u g) y = c * B u y].
Proof.
move=> hu; have hcu := summable_real_scale ha c hu.
apply: (measure_almost_everywhere_mono hc _ (measure_almost_everywhere_and hc
  (coset_lone_integral_fibre hB hcu) (coset_lone_integral_fibre hB hu)))=> y /= [h h1].
exact (coset_fibre_integral_unique hA h (coset_fibre_integral_scale hb c h1)).
Qed.

(** Source for [coset_lone_integral_le]: beta^x is monotone gamma
    almost everywhere, supporting "T(u_h) increases to T(u)",
    Federer 2.7.13, proof, p. 130. Supporting theorem. *)
Theorem coset_lone_integral_le u v : summable_real_functions alpha u -> summable_real_functions alpha v ->
  (forall g, u g <= v g) -> measure_almost_everywhere gamma [set y | B u y <= B v y].
Proof.
move=> hu hv huv.
apply: (measure_almost_everywhere_mono hc _ (measure_almost_everywhere_and hc
  (coset_lone_integral_fibre hB hu) (coset_lone_integral_fibre hB hv)))=> y /= [h1 h2].
exact (coset_fibre_integral_le hA hb huv h1 h2).
Qed.

(** Source for [coset_lone_integral_nonnegative]: beta^x(u) >= 0
    gamma almost everywhere when u >= 0, supporting "T(w) and T(u)
    are gamma almost equal to 0", Federer 2.7.13, proof, p. 130.
    Supporting theorem. *)
Theorem coset_lone_integral_nonnegative u : summable_real_functions alpha u -> (forall g, 0 <= u g) ->
  measure_almost_everywhere gamma [set y | 0 <= B u y].
Proof.
move=> hu hu0; apply: (measure_almost_everywhere_mono hc _ (coset_lone_integral_fibre hB hu))=> y /= h.
exact (coset_fibre_integral_nonnegative hA hb hu0 h).
Qed.

(** Source for [coset_lone_integral_absolute]: |beta^x(u)| <=
    beta^x(|u|) gamma almost everywhere, from
    -|u(g s)| <= u(g s) <= |u(g s)| on each coset, as in 2.4.4(7),
    p. 82; supporting
    Federer 2.7.13, p. 130. Supporting theorem. *)
Theorem coset_lone_integral_absolute u : summable_real_functions alpha u ->
  measure_almost_everywhere gamma [set y | `|B u y| <= B (fun g => `|u g|) y].
Proof.
move=> hu; have hau := summable_real_absolute ha hu.
apply: (measure_almost_everywhere_mono hc _ (measure_almost_everywhere_and hc
  (coset_lone_integral_fibre hB hu) (coset_lone_integral_fibre hB hau)))=> y /= [h1 h2].
rewrite ler_norml; apply/andP; split.
- have h3 := coset_fibre_integral_scale hb (-1) h2.
  have hle : forall g, -1 * `|u g| <= u g by move=> g; rewrite mulN1r; exact: lerNnormlW.
  have := coset_fibre_integral_le hA hb hle h3 h1; by rewrite mulN1r.
- by apply: (coset_fibre_integral_le hA hb _ h1 h2)=> g; exact: ler_norm.
Qed.

(** Source for [coset_lone_integral_almost_equal]: beta^x maps alpha
    almost equal functions to gamma almost equal functions, so that it
    is defined on L_1(alpha) modulo null functions, Federer 2.7.13,
    p. 130. The proof follows "T(w) and T(u) are gamma almost equal to
    0" of the proof: with w = |u - v|, integral beta^x(w) d gamma =
    integral w d alpha = 0 and beta^x(w) >= 0, hence beta^x(w) = 0
    gamma almost everywhere, hence u(g s) = v(g s) for beta almost all
    s at gamma almost all points g x. Supporting theorem. *)
Theorem coset_lone_integral_almost_equal u v : summable_real_functions alpha u ->
  summable_real_functions alpha v -> measure_almost_everywhere alpha [set g | u g = v g] ->
  measure_almost_everywhere gamma [set y | B u y = B v y].
Proof.
move=> hu hv huv.
pose w g := `|u g - v g|.
have hw : summable_real_functions alpha w.
  have h := summable_real_absolute ha (summable_real_subtract ha hu hv); exact: h.
have hw0 : is_measure_integral alpha (real_total_integrand w) 0%E.
  have hz := real_total_zero_integral ha.
  apply: (summable_total_almost_equal_integral ha hz).
  apply: (measure_almost_everywhere_mono ha _ huv)=> g /= hg.
  by rewrite /w hg subrr normr0.
have hBw := coset_lone_integral_identity hB hw0.
have hBw0 : measure_almost_everywhere gamma [set y | 0 <= B w y].
  by apply: coset_lone_integral_nonnegative=> // g; exact: normr_ge0.
have hz := summable_total_nonnegative_zero_almost hc hBw hBw0.
have h4 := measure_almost_everywhere_and hc hz (measure_almost_everywhere_and hc
  (coset_lone_integral_fibre hB hw) (measure_almost_everywhere_and hc
    (coset_lone_integral_fibre hB hu) (coset_lone_integral_fibre hB hv))).
apply: (measure_almost_everywhere_mono hc _ h4)=> y /= [hy0 [hwy [huy hvy]]].
apply: (coset_fibre_integral_unique hA _ hvy)=> g hg.
have hwg := hwy g hg; rewrite /= in hy0; rewrite hy0 in hwg.
have hz' := summable_total_nonnegative_zero_almost hb hwg
  (measure_almost_everywhere_mono hb (fun s _ => normr_ge0 _) (measure_almost_everywhere_true hb)).
apply: (summable_total_almost_equal_integral hb (huy g hg)).
apply: (measure_almost_everywhere_mono hb _ hz')=> s /= hs.
by apply/eqP; rewrite -subr_eq0 -normr_eq0; apply/eqP; exact: hs.
Qed.

(** Source for [coset_lone_integral_contraction]: integral
    |beta^x(u)| d gamma <= integral |u| d alpha, from
    |beta^x(u)| <= beta^x(|u|) and "integral beta^x(|u|) d gamma =
    integral |u| d alpha", Federer 2.7.13, p. 130: beta^x does not
    increase the L_1 seminorm. Supporting theorem for the surjectivity. *)
Theorem coset_lone_integral_contraction u (c d : R) : summable_real_functions alpha u ->
  is_measure_integral gamma (real_total_integrand (fun y => `|B u y|)) c%:E ->
  is_measure_integral alpha (real_total_integrand (fun g => `|u g|)) d%:E -> c <= d.
Proof.
move=> hu hcB hdu.
have hB' := coset_lone_integral_identity hB hdu.
have h := summable_total_integral_le_almost hc hcB hB' (coset_lone_integral_absolute hu).
by rewrite lee_fin in h.
Qed.

End CosetLoneIntegralLaws.
