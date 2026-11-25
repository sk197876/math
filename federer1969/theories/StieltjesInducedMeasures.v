(** Federer (1969), 2.5.17, p. 111: from 2.5.13, 2.5.6 and 2.5.3 there exist
    regular measures psi^+ and psi^- with (1) mu(f) = int f dpsi^+ - int f
    dpsi^- whenever f in K(R), and (2) psi^+{x : a < x < b} + psi^-{x : a <
    x < b} <= V_a^b g for a < b. The measures are those of the
    representation theorem 2.5.6 applied to the Daniell integral mu induced
    by g; the inequality (2) is obtained from the suiting sequences of the
    open interval and the bound |mu(h)| <= V_a^b g for |h| <= 1 supported in
    [a, b]. Borel regularity of the measures is not separately recorded
    here. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  constructive_ereal topology normedtype.
From mathcomp Require Import lra.
From Federer Require Import RealMetricBackground ExtendedRealBoundsUP ExtendedRealBounds
  CurveVariationUP CurveArcLength FunctionLatticeUP FunctionLatticeRegularityUP
  PositiveLatticeRegularity LatticeAdditiveFunctional DaniellIntegralUP DaniellVariationUP
  DaniellVariationBounds DaniellRepresentation DaniellCoverUP RegularDaniellEnvelope
  RealIntegralFunctionalUP MeasureUP MeasureIntegralUP CompactSupportFunctionUP
  CompactSupportFunctionLattice StieltjesSums StieltjesIntegral StieltjesDaniellIntegral
  IntervalBumpFunctions
  SummableRealFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [positive_lattice_is_lattice]: supporting closure of L+
    under the lattice operations of Federer 2.5.1, p. 91, used to apply
    the regular measure envelope of 2.5.2 to L+ in 2.5.17, p. 111. *)
Lemma positive_lattice_is_lattice (R : realType) (X : Type) (L : set (X -> R)) :
  is_function_lattice L -> is_function_lattice (positive_function_lattice L).
Proof.
move=> hL; constructor.
- move=> f g [hf hf0] [hg hg0]; split; first exact (function_lattice_add hL hf hg).
  by move=> x; rewrite addr_ge0 ?hf0 ?hg0.
- move=> c f hc [hf hf0]; split; first exact (function_lattice_scale hL hc hf).
  by move=> x; rewrite mulr_ge0 ?hf0.
- move=> f g [hf hf0] [hg hg0]; split; first exact (function_lattice_minimum hL hf hg).
  by move=> x; rewrite le_min hf0 hg0.
- move=> c f hc [hf hf0]; split; first exact (function_lattice_truncation hL hc hf).
  by move=> x; rewrite le_min hf0 hc.
- move=> f g [hf hf0] [hg hg0] hfg; split; first exact (function_lattice_ordered_difference hL hf hg hfg).
  by move=> x; rewrite subr_ge0; exact: hfg.
Qed.

Section InducedMeasures.
Variable R : realType.
Variable g : R -> R.
Hypothesis hg : curve_locally_finite_variation (g : R -> real_line_metric R).
Local Notation KR := (@compactly_supported_continuous_functions R R).
Local Notation mu := (induced_daniell g).

(** Source for [KR_scale]: a scalar multiple of a member of K(R) belongs
    to K(R), supporting the signed combinations in Federer 2.5.17,
    p. 111. *)
Lemma KR_scale (c : R) (f : R -> R) : KR f -> KR (fun x => c * f x).
Proof.
move=> [hf hc]; split; first exact: continuous_scale (KR_continuous (conj hf hc)).
rewrite /real_function_support.
apply: (subclosed_compact (@closed_closure _ [set x | c * f x <> 0]) hc).
rewrite /real_function_support; apply: closureS=> x hx h0.
by apply: hx; rewrite h0 mulr0.
Qed.

(** Source for [positive_variation_monotone]: the positive variation of
    2.5.5, p. 96, is nondecreasing on L+, supporting the costs of the
    suiting sequences in Federer 2.5.17, p. 111. *)
Lemma positive_variation_monotone (X : Type) (L : set (X -> R)) (A P : (X -> R) -> R)
    (f f' : X -> R) :
  is_daniell_positive_variation L A P -> positive_function_lattice L f ->
  positive_function_lattice L f' -> function_le f f' -> P f <= P f'.
Proof.
move=> hP hf hf' hff'; apply: (daniell_positive_variation_least hP hf)=> k [hk [hk0 hkf]].
have hk' : lattice_positive_order_interval L f' k.
  by split=> //; split=> // x; exact: le_trans (hkf x) (hff' x).
have := extended_real_supremum_upper (hP f' hf') (ex_intro _ k (conj hk' erefl)).
by rewrite lee_fin.
Qed.

(** Source for [induced_daniell_interval_bound]: for f in K(R)+ with
    f <= 1 vanishing outside {x : a < x < b}, and 0 <= k1, k2 <= f in
    K(R), mu(k1) - mu(k2) <= V_a^b g, the bound behind condition (2) of
    Federer 2.5.17, p. 111. *)
Lemma induced_daniell_interval_bound (a b : R) (f k1 k2 : R -> R) :
  a <= b -> (forall x, f x <= 1) -> (forall x, f x <> 0 -> a < x < b) ->
  lattice_positive_order_interval KR f k1 -> lattice_positive_order_interval KR f k2 ->
  mu k1 - mu k2 <= total_variation g a b.
Proof.
move=> hab hf1 hfz [hk1 [hk10 hk1f]] [hk2 [hk20 hk2f]].
have hk2' := KR_scale (-1) hk2.
have hsum := function_lattice_add (@compactly_supported_continuous_functions_lattice R R) hk1 hk2'.
have -> : mu k1 - mu k2 = mu (fun x => k1 x + (-1) * k2 x).
  by rewrite (induced_daniell_add hg hk1 hk2') (induced_daniell_scale hg (-1) hk2) mulN1r.
have hz : forall x, k1 x + (-1) * k2 x <> 0 -> a < x < b.
  move=> x hx; apply: hfz=> h0.
  have h1 : k1 x = 0 by apply/le_anti; rewrite hk10 andbT -h0; exact: hk1f.
  have h2 : k2 x = 0 by apply/le_anti; rewrite hk20 andbT -h0; exact: hk2f.
  by apply: hx; rewrite h1 h2 mulr0 addr0.
rewrite (induced_daniell_value hg hsum hab hz).
apply: le_trans (ler_norm _) _; rewrite -[total_variation g a b]mul1r.
apply: (stieltjes_integral_bound hg (KR_continuous hsum) hab)=> x _.
have := hk10 x; have := hk20 x; have := hk1f x; have := hk2f x; have := hf1 x.
by rewrite mulN1r ler_norml=> *; apply/andP; split; lra.
Qed.

(** Source for [induced_variations_interval_bound]: P(f) + Q(f) <= V_a^b g
    for the positive and negative variations of mu and f as above,
    Federer 2.5.17, p. 111. *)
Lemma induced_variations_interval_bound (P Q : (R -> R) -> R) (a b : R) (f : R -> R) :
  is_daniell_positive_variation KR mu P -> is_daniell_negative_variation KR mu Q ->
  a <= b -> positive_function_lattice KR f -> (forall x, f x <= 1) ->
  (forall x, f x <> 0 -> a < x < b) ->
  P f + Q f <= total_variation g a b.
Proof.
move=> hP hQ hab hf hf1 hfz.
have hQle : Q f <= total_variation g a b - P f.
  apply: (daniell_positive_variation_least hQ hf)=> k2 hk2.
  rewrite lerBrDr addrC -lerBrDr.
  apply: (daniell_positive_variation_least hP hf)=> k1 hk1.
  by rewrite lerBrDr; have := induced_daniell_interval_bound hab hf1 hfz hk1 hk2; lra.
by lra.
Qed.

(** Source for [stieltjes_induced_measures]: the measures psi^+ and psi^-
    induced by g, Federer 2.5.17, p. 111, with the conditions (1) and
    (2). The positive and negative variations of mu are included. *)
Theorem stieltjes_induced_measures :
  exists (P Q : (R -> R) -> R) (psip psim : set R -> \bar R),
    is_daniell_positive_variation KR mu P /\ is_daniell_negative_variation KR mu Q /\
    is_measure psip /\ is_measure psim /\
    is_function_lattice_regular KR psip /\ is_function_lattice_regular KR psim /\
    (forall f, KR f -> exists u v : R,
      is_measure_integral psip (real_total_integrand f) u%:E /\
      is_measure_integral psim (real_total_integrand f) v%:E /\ mu f = u - v) /\
    forall a b : R, a <= b -> (psip `]a, b[ + psim `]a, b[ <= (total_variation g a b)%:E)%E.
Proof.
have hL := @compactly_supported_continuous_functions_lattice R R.
have hD := induced_daniell_is_daniell hg.
have hne : exists f, KR f by exists (fun _ => 0); exact: compactly_supported_zero_function.
have [P [Q [psip [psim [hP [hQ [hm [hn [hr [hs [hi [hj [hform _]]]]]]]]]]]]] :=
  daniell_integral_representation hL hD hne.
exists P, Q, psip, psim; split=> //; split=> //; split=> //; split=> //.
split; first exact ((@function_lattice_regular_positive_iff R R KR psip).1 hr).
split; first exact ((@function_lattice_regular_positive_iff R R KR psim).1 hs).
split=> // a b hab.
have hLp : is_function_lattice (positive_function_lattice KR) := positive_lattice_is_lattice hL.
have henvP := regular_representing_measure_envelope hLp hm hi hr.
have henvQ := regular_representing_measure_envelope hLp hn hj hs.
pose SP := [set z : \bar R | exists n, z = (P (interval_bump a b n))%:E].
pose SQ := [set z : \bar R | exists n, z = (Q (interval_bump a b n))%:E].
have hcP : is_daniell_sequence_cost P (interval_bump a b) (extended_real_sup SP).
  by split; [exact: extended_real_sup_upper | exact: extended_real_sup_least].
have hcQ : is_daniell_sequence_cost Q (interval_bump a b) (extended_real_sup SQ).
  by split; [exact: extended_real_sup_upper | exact: extended_real_sup_least].
have hmuV := daniell_cover_lower henvP (interval_bump_suiting (R := R) a b) hcP.
have hnuV := daniell_cover_lower henvQ (interval_bump_suiting (R := R) a b) hcQ.
have hbump : forall n, positive_function_lattice KR (interval_bump a b n).
  by move=> n; split; [exact: interval_bump_member | move=> x; exact: interval_bump_ge0].
have hV : forall n, P (interval_bump a b n) + Q (interval_bump a b n) <= total_variation g a b.
  move=> n; apply: induced_variations_interval_bound hP hQ hab (hbump n) _ _.
  - by move=> x; exact: interval_bump_le1.
  - by move=> x; exact: interval_bump_support.
have hcost : (extended_real_sup SP + extended_real_sup SQ <= (total_variation g a b)%:E)%E.
  apply: extended_sup_sum_bound.
  - by exists (P (interval_bump a b 0))%:E, 0%N.
  - by exists (Q (interval_bump a b 0))%:E, 0%N.
  - by move=> x [n ->]; exists (P (interval_bump a b n)).
  - by move=> y [n ->]; exists (Q (interval_bump a b n)).
  - move=> x y [n ->] [m ->]; rewrite -EFinD lee_fin.
    have hnm : (n <= maxn n m)%N := leq_maxl n m.
    have hmn : (m <= maxn n m)%N := leq_maxr n m.
    have h1 := positive_variation_monotone hP (hbump n) (hbump (maxn n m))
      (fun x => interval_bump_monotone a b x hnm).
    have h2 := positive_variation_monotone hQ (hbump m) (hbump (maxn n m))
      (fun x => interval_bump_monotone a b x hmn).
    by have := hV (maxn n m); lra.
exact: le_trans (leeD hmuV hnuV) hcost.
Qed.

End InducedMeasures.
