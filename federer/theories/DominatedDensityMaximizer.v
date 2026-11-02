(** Federer (1969), 2.5.7, pp. 98–99: the maximal member k+ of the dominated
    density family in all three exponent cases. Finite q uses its Lq norm;
    infinite q uses the actual weighted covering-set integrals. The zero
    measure is handled explicitly before invoking a positive- mass cover.
    This is the maximality step, not yet the assertion that k+ represents
    the functional. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal.
From Federer Require Import MeasureUP MeasureBasic MeasureAlmostUP CountablyMeasurableUP
  FunctionLatticeUP MonotoneDaniellIntegralUP TotalScalarLpUP TotalScalarLpFiniteSeminorm
  LpConjugatePair LpDominatedDensityFamily FiniteDensityMaximizer InfinityDensityMaximizer.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [dominated_density_maximal_member]: the maximal- density
    conclusion of the middle part of Federer 2.5.7, pp. 98–99 The
    countable-measurability hypothesis is used only for q=infinity. All
    mathematical closure and strictness premises have been proved. *)
Theorem dominated_density_maximal_member (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) p q (P : (X -> R) -> R) (M : R) :
  is_lp_conjugate_pair p q -> (q=+oo -> measure_countably_measurable mu setT) -> (0 <= M)%R ->
  is_monotone_daniell_integral (positive_function_lattice (total_scalar_lp mu p)) P ->
  (forall f, positive_function_lattice (total_scalar_lp mu p) f -> (0 <= P f)%R) ->
  (forall f, positive_function_lattice (total_scalar_lp mu p) f ->
    (P f <= M*finite_total_scalar_lp_norm mu p f)%R) ->
  exists k, lp_dominated_density_family mu p q P k /\
    forall u, lp_dominated_density_family mu p q P u ->
      measure_almost_everywhere mu [set x | (k x <= u x)%R] ->
      ~ (0 < mu [set x | (k x < u x)%R]).
Proof.
move=> hpq hX hM hP hP0 hPb.
have [hz|hpos] := leP (mu setT) 0.
- exists (fun _ => 0%R); split.
  + exact: (@zero_lp_dominated_density R X mu hm p q P (lp_conjugate_pair_admissible hpq).2 hP0).
  + move=> u hu hku hstrict.
    have hle : mu [set x | (0 < u x)%R] <= 0.
      apply: le_trans _ hz; apply: (@measure_mono R X mu hm)=> x _; exact: I.
    by rewrite ltNge hle in hstrict.
- case: hpq hX hP hP0 hPb=> [[a [ha [-> ->]]]|[[-> ->]|[-> ->]]] hX hP hP0 hPb.
  + apply: (@finite_density_maximal_member R X mu hm a%:E _ P M _ hM hP hP0 hPb).
    left; exists a; by split=> //; split.
  + exact: (@infinity_density_maximal_member R X mu hm P M (hX erefl) hpos hM hP hP0 hPb).
  + apply: (@finite_density_maximal_member R X mu hm +oo 1%R P M _ hM hP hP0 hPb).
    by right; right.
Qed.
