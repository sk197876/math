(** Exceptional upper-density levels in Federer (1969), 2.10.18(3), pp.
    180–181. The finite Borel regular restriction is dominated by psi; the
    open infimum estimate yields t psi(B)<=mu(B)<=psi(B). *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals constructive_ereal topology lra.
From Federer Require Import MeasureUP MeasureBasic MeasureAlmostUP MeasureAlmostBasic BorelRegularMeasureUP
  CaratheodoryLimitUP CaratheodoryLimitMeasure CaratheodoryEnlargementUP CaratheodoryFiniteDensityBound
  CaratheodoryZeroDensityLimit CaratheodoryDensityUpperBound MeasureDerivates CoveringRelationLimits
  FiniteMeasureSelfExpansion ExtendedRealReciprocalBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [caratheodory_submeasure_density_level_null]: supporting
    nullity of the sets B_n in 2.10.18(3),
    pp. 180–181. Finiteness belongs to the smaller
    measure mu on X, not to psi on X. *)
Lemma caratheodory_submeasure_density_level_null (R : realType) (X : metricType R)
    (F : set (set X)) (c mu psi : set X -> \bar R)
    (E : set X -> set X) (k t : R) :
  is_caratheodory_enlargement F c E k -> is_measure mu -> is_borel_regular_measure mu ->
  mu setT < +oo -> (forall B, mu B<=psi B) ->
  is_caratheodory_limit (fun j : set_type F => val j) (fun j => c (val j)) psi ->
  (forall S, F S -> closed S) -> (forall S, F S -> measure_measurable mu S) ->
  (1<t)%R ->
  psi [set x | t%:E<covering_upper_limit (caratheodory_family_relation F) (measure_ratio_function mu c) x]=0.
Proof.
move=> hE hm hr hfin hdom hpsi hclosed hmeas ht.
pose B := [set x | t%:E<covering_upper_limit (caratheodory_family_relation F) (measure_ratio_function mu c) x].
have hcost (j : set_type F) : 0<=c (val j : set X).
  exact: ltW (@caratheodory_enlargement_cost_positive R X F c E k hE _ (set_valP j)).
have hpm := caratheodory_limit_is_measure hpsi hcost.
have ht0 : (0<t)%R := lt_trans (@ltr01 R) ht.
have hb := @caratheodory_finite_density_bound R X F c mu psi E k B t
  hE hm hr hfin hpsi hclosed hmeas ht0 (fun x hx => hx).
have hpn := @measure_nonnegative R X psi hpm B.
have h1t : (1 : \bar R)<=t%:E by rewrite lee_fin; exact: ltW ht.
have hmul := lee_wpmul2r hpn h1t; rewrite mul1e in hmul.
have hBfin : psi B < +oo.
  apply: le_lt_trans (le_trans hmul hb) _.
  exact: le_lt_trans (@measure_mono R X mu hm B setT (subsetT B)) hfin.
exact: finite_nonnegative_self_expansion_zero hpn hBfin ht (le_trans hb (hdom B)).
Qed.

(** Source for [caratheodory_submeasure_upper_density]: supporting countable
    exceptional-level conclusion for 2.10.18(3), p. 181 Positive reciprocal
    levels exhaust all values above one. *)
Theorem caratheodory_submeasure_upper_density (R : realType) (X : metricType R)
    (F : set (set X)) (c mu psi : set X -> \bar R)
    (E : set X -> set X) (k : R) :
  is_caratheodory_enlargement F c E k -> is_measure mu -> is_borel_regular_measure mu ->
  mu setT < +oo -> (forall B, mu B<=psi B) ->
  is_caratheodory_limit (fun j : set_type F => val j) (fun j => c (val j)) psi ->
  (forall S, F S -> closed S) -> (forall S, F S -> measure_measurable mu S) ->
  measure_almost_everywhere psi [set x | covering_upper_limit (caratheodory_family_relation F)
    (measure_ratio_function mu c) x<=1].
Proof.
move=> hE hm hr hfin hdom hpsi hclosed hmeas.
have hcost (j : set_type F) : 0<=c (val j : set X).
  exact: ltW (@caratheodory_enlargement_cost_positive R X F c E k hE _ (set_valP j)).
have hpm := caratheodory_limit_is_measure hpsi hcost.
pose L x := covering_upper_limit (caratheodory_family_relation F) (measure_ratio_function mu c) x.
pose B n := [set x | (1+((n.+1)%:R : R)^-1)%:E<L x].
have hB n : psi (B n)=0.
  have hpos : (0<((n.+1)%:R : R)^-1)%R by rewrite invr_gt0 ltr0n.
  have ht : (1<1+((n.+1)%:R : R)^-1)%R.
    have hh := ler_ltD (lexx (1%R : R)) hpos.
    by rewrite addr0 in hh.
  exact: (@caratheodory_submeasure_density_level_null R X F c mu psi E k
    (1+((n.+1)%:R : R)^-1)%R hE hm hr hfin hdom hpsi hclosed hmeas ht).
have hN : psi (\bigcup_n B n)=0.
  exact: (@measure_null_countable_union R X [the choiceType of (nat : Type)] psi hpm
    setT B (countableP _) (fun n _ => hB n)).
apply: (@measure_null_subset R X psi hpm _ (\bigcup_n B n))=> // x hx.
have hp : 1<L x by rewrite ltNge; apply/negP.
have [n hn] : exists n : nat, (1+((n.+1)%:R : R)^-1)%:E<L x.
  move: hp; case: (L x)=> [r| |] hp //.
  - rewrite lte_fin in hp.
    have hd : (0<r-1)%R by lra.
    have [n hn] := positive_reciprocal_nat_small hd.
    exists n; rewrite lte_fin.
    have hh := ler_ltD (lexx (1%R : R)) hn.
    by rewrite [(1+(r-1))%R]addrC subrK in hh.
  - exists 0%N; exact: ltry.
exists n=> //; exact hn.
Qed.
