(** Federer (1969), 2.5.14, p. 107: "If f in K(X)+, s > 0, U = {x : f(x) >
    s} and t > s, then alpha(U) >= h^-1 lambda[inf{f, t+h} - inf{f, t}]
    whenever h > 0; consequently Phi(U) = phi(U)." The function g = h^-1
    [inf{f, t+h} - inf{f, t}] belongs to K(X), takes values in [0, 1], and
    vanishes outside the closed set {x : f(x) >= t}, which lies in U; hence
    g is a test function in the supremum defining alpha(U). The consequence
    Phi(U) = phi(U) is obtained from the agreement of Phi and phi on F1,
    proved in CompactOpenContentLevelAgreement.v without the printed pair of
    right limits; positive strict levels belong to F1. The erratum p. 2,
    book p. 107 line 24, concerns the measure symbol in the comparison
    Phi(V) = alpha(V) <= phi(V) and does not affect this inequality. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  constructive_ereal topology.
From mathcomp Require Import lra.
From Federer Require Import RealMetricBackground CompactSupportFunctionUP CompactSupportFunctionLattice
  CompactSupportLevels FunctionLatticeUP FunctionLatticeLevelFamilies MonotoneDaniellIntegralUP
  CompactOpenContentUP ExtendedRealBoundsUP RealIntegralFunctionalUP OpenCoverContentUP MeasureUP
  CompactOpenContentLevelAgreement CountableOrderIntervals.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section LevelEstimate.
Variable R : realType.
Variable X : topologicalType.
Local Notation KX := (@compactly_supported_continuous_functions R X).

(** Source for [truncation_difference]: the function
    inf{f, t+h} - inf{f, t} in the displayed inequality of Federer
    2.5.14, p. 107. Definition used in the following lemmas. *)
Definition truncation_difference (f : X -> R) (t h : R) (x : X) : R :=
  Order.min (f x) (t + h) - Order.min (f x) t.

(** Source for [truncation_difference_bounds]: the values of
    inf{f, t+h} - inf{f, t} lie between 0 and h, supporting the
    inequality of Federer 2.5.14, p. 107. *)
Lemma truncation_difference_bounds (f : X -> R) (t h : R) x :
  0 <= h -> 0 <= truncation_difference f t h x <= h.
Proof.
move=> hh; rewrite /truncation_difference.
by case: (leP (f x) t)=> h1; case: (leP (f x) (t + h))=> h2; apply/andP; split; lra.
Qed.

(** Source for [truncation_difference_zero]: inf{f, t+h} - inf{f, t}
    vanishes where f(x) <= t, supporting the support inclusion
    {x : f(x) >= t} in U behind Federer 2.5.14, p. 107. *)
Lemma truncation_difference_zero (f : X -> R) (t h : R) x :
  0 <= h -> f x <= t -> truncation_difference f t h x = 0.
Proof.
move=> hh hft; rewrite /truncation_difference.
by case: (leP (f x) t)=> h1; case: (leP (f x) (t + h))=> h2; rewrite ?subrr //; lra.
Qed.

(** Source for [truncation_difference_member]: inf{f, t+h} - inf{f, t}
    belongs to K(X) whenever f does and t >= 0, h >= 0, as needed to
    apply lambda in Federer 2.5.14, p. 107. Stone's truncation law
    and the ordered difference law of the lattice K(X), 2.5.1, p. 91,
    and 2.5.13, p. 106. *)
Lemma truncation_difference_member (f : X -> R) (t h : R) :
  KX f -> 0 <= t -> 0 <= h -> KX (truncation_difference f t h).
Proof.
move=> hf ht hh.
have hL := @compactly_supported_continuous_functions_lattice R X.
have hth : 0 <= t + h by rewrite addr_ge0.
apply: (function_lattice_ordered_difference hL (function_lattice_truncation hL ht hf)
  (function_lattice_truncation hL hth hf))=> x.
by rewrite /=; case: (leP (f x) t)=> h1; case: (leP (f x) (t + h))=> h2; lra.
Qed.

(** Source for [truncation_quotient_test_function]: the function
    g = h^-1 [inf{f, t+h} - inf{f, t}] is admissible in the supremum
    alpha(U) of Federer 2.5.14, p. 107, where U = {x : f(x) > s} and
    0 <= s < t, h > 0: g is in K(X), 0 <= g <= 1, and
    spt g is contained in the closed set {x : f(x) >= t}, hence in U.
    Supporting lemma. *)
Lemma truncation_quotient_test_function (f : X -> R) (s t h : R) :
  KX f -> 0 <= s -> s < t -> 0 < h ->
  is_compact_open_test_function [set x | s < f x]
    (fun x => h^-1 * truncation_difference f t h x).
Proof.
move=> hf hs hst hh.
have hL := @compactly_supported_continuous_functions_lattice R X.
have ht : 0 <= t by apply: le_trans hs (ltW hst).
have hhi : 0 <= h^-1 by rewrite invr_ge0 ltW.
split; first exact: (function_lattice_scale hL hhi (truncation_difference_member hf ht (ltW hh))).
split.
- move=> x; have /andP[h0 h1] := truncation_difference_bounds f t x (ltW hh).
  apply/andP; split; first exact: mulr_ge0 hhi h0.
  by rewrite ler_pdivrMl // mulr1.
- have hc : closed [set x | t <= f x].
    exact ((@continuous_closedP X (real_line_metric R) f).1 hf.1 _
      (@order_closed_upper_ray_closed _ [the orderTopologicalType _ of R^o] t)).
  apply: subset_trans (real_function_support_in_closed_set hc _) _.
  + move=> x hx; rewrite (truncation_difference_zero (ltW hh)) ?mulr0 //.
    by rewrite leNgt; apply/negP=> hlt; apply: hx; exact: ltW hlt.
  + move=> x hx; exact: (lt_le_trans hst (hx : t <= f x)).
Qed.

(** Source for [compact_open_content_truncation_lower_bound]: the
    displayed inequality of Federer 2.5.14, p. 107,
    alpha(U) >= h^-1 lambda[inf{f, t+h} - inf{f, t}] for f in K(X)+,
    s > 0, U = {x : f(x) > s}, t > s and h > 0. Direct formalisation.
    Of the properties of lambda only the positive homogeneity law of
    2.5.2, p. 92, is used; f need only be nonnegative for U to be a
    positive strict level, hence open. *)
Theorem compact_open_content_truncation_lower_bound (A : (X -> R) -> R) (a : set X -> \bar R)
    (f : X -> R) (s t h : R) :
  (forall c g, 0 <= c -> KX g -> A (fun x => c * g x) = c * A g) ->
  is_compact_open_content A a -> positive_function_lattice KX f ->
  0 < s -> s < t -> 0 < h ->
  ((h^-1 * A (truncation_difference f t h))%:E <= a [set x | (s < f x)%R])%E.
Proof.
move=> hscale ha hf hs hst hh.
have ht : 0 <= t by apply: le_trans (ltW hs) (ltW hst).
have hU : open [set x | s < f x].
  by apply: compact_support_strict_level_open; exists f, s.
have hhi : 0 <= h^-1 by rewrite invr_ge0 ltW.
rewrite -(hscale _ _ hhi (truncation_difference_member hf.1 ht (ltW hh))).
apply: (extended_real_supremum_upper (ha _ hU)).
exists (fun x => h^-1 * truncation_difference f t h x); split=> //.
exact: truncation_quotient_test_function hf.1 (ltW hs) hst hh.
Qed.

(** Source for [monotone_daniell_truncation_lower_bound]: the
    inequality of Federer 2.5.14, p. 107, under the hypothesis of
    2.5.14 that lambda is a monotone Daniell integral on K(X).
    Direct formalisation, as a corollary of the preceding theorem. *)
Theorem monotone_daniell_truncation_lower_bound (A : (X -> R) -> R) (a : set X -> \bar R)
    (f : X -> R) (s t h : R) :
  is_monotone_daniell_integral KX A ->
  is_compact_open_content A a -> positive_function_lattice KX f ->
  0 < s -> s < t -> 0 < h ->
  ((h^-1 * A (fun x => Order.min (f x) (t + h) - Order.min (f x) t))%:E
    <= a [set x | (s < f x)%R])%E.
Proof.
move=> hA ha hf hs hst hh.
exact: (@compact_open_content_truncation_lower_bound A a f s t h
  (monotone_daniell_integral_scale hA) ha hf hs hst hh).
Qed.

(** Source for [compact_open_envelope_strict_level_value]: the
    consequence Phi(U) = phi(U) for U = {x : f(x) > s}, f in K(X)+,
    s > 0, in Federer 2.5.14, p. 107. Here mu is any measure
    representing lambda by actual integrals on K(X), as the K(X) regular
    measure phi of 2.5.14 does, and nu is the open-cover envelope Phi of
    alpha. Direct formalisation, derived from the agreement on F1 in
    CompactOpenContentLevelAgreement.v, which uses compact closed-level
    approximants instead of the printed right limits as h and t
    decrease to 0 and s. *)
Theorem compact_open_envelope_strict_level_value
    (mu nu : set X -> \bar R) (A : (X -> R) -> R) (a : set X -> \bar R)
    (hm : is_measure mu)
    (hA : is_real_integral_functional mu KX A)
    (ha : is_compact_open_content A a) (hc : is_open_cover_content a)
    (hn : is_open_cover_envelope a nu) :
  hausdorff_space X -> locally_compact (@setT X) ->
  forall (f : X -> R) (s : R), positive_function_lattice KX f -> 0 < s ->
  nu [set x | s < f x] = mu [set x | s < f x].
Proof.
move=> hh hl f s hf hs.
apply: (@compact_open_envelope_increasing_level_value R X mu nu A a hm hA ha hc hn hh hl).
by apply: function_lattice_strict_level_increasing; exists f, s.
Qed.

End LevelEstimate.
