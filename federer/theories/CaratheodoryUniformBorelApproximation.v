(** Federer (1969), 2.10.24(1), p. 187: supporting construction of the
    increasing Borel sets B_j. The density estimate is 2.10.18(3), p. 180;
    the proved weak enlargement version also permits zero costs. Finite
    Borel hulls and summable exceptional losses expand Federer's terse
    choice. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import MeasureUP MeasureBasic MeasureRestriction MeasureAlmostUP MeasureAlmostBasic
  BorelRegularMeasureUP TopologicalBorel CaratheodoryLimitUP CaratheodoryLimitMeasure CaratheodoryBorelRegular
  CaratheodoryWeakEnlargementUP WeakCaratheodoryRestrictedDensity WeakCaratheodoryDensityQuotient
  CaratheodoryDensityFunction CaratheodoryDensityUpperBound CoveringLimitGraphEquivalence CoveringRelationLimits
  BorelUniformGeneratorBounds IncreasingBorelApproximation GeometricErrorBudget
  NonnegativeSum NonnegativeSumSupport MetricDiameter.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [caratheodory_finite_restriction_density_bound]:
    supporting form of 2.10.18(3), p. 180, used
    in 2.10.24(1), p. 187. The corrected weak-cost
    version of the restriction estimate is already proved;
    this lemma only identifies its numerator with psi(A cap S). *)
Lemma caratheodory_finite_restriction_density_bound (R : realType) (X : metricType R)
    (F : set (set X)) (c psi : set X -> \bar R)
    (E : set X -> set X) (k : R) (A : set X) :
  is_weak_caratheodory_enlargement F c E k ->
  is_caratheodory_limit (fun j : set_type F=>val j) (fun j=>c (val j)) psi ->
  (forall S, F S -> closed S) -> psi A< +oo ->
  measure_almost_everywhere psi [set x | covering_upper_limit (caratheodory_family_relation F)
    (caratheodory_density_function psi c A) x<=1].
Proof.
move=> hE hp hclosed hAfin.
have hh := @weak_caratheodory_restricted_upper_density R X F c psi E k A hE hp hclosed hAfin.
have hm := caratheodory_limit_is_measure hp (fun j=>weak_enlargement_cost_nonnegative hE (set_valP j)).
apply: (@measure_almost_everywhere_mono R X psi hm _ _ _ hh)=> x hx.
have heq : covering_upper_limit (caratheodory_family_relation F)
    (caratheodory_measure_cost_ratio (measure_restrict psi A) c) x=
    covering_upper_limit (caratheodory_family_relation F) (caratheodory_density_function psi c A) x.
  apply: (covering_limits_graph_equivalent _ x).1=> y S hS z.
  by rewrite /caratheodory_measure_cost_ratio /caratheodory_density_function /measure_restrict /= setTI.
change (covering_upper_limit (caratheodory_family_relation F) (caratheodory_density_function psi c A) x<=1).
by rewrite -heq.
Qed.

(** Source for [caratheodory_increasing_borel_generator_bounds]:
    supporting B_j and positive a_j of 2.10.24(1),
    p. 187. An arbitrary sequence of factors t_j>1
    is allowed. Each B_j lies in the prescribed
    increasing finite Borel source A_j; the lost union
    is null. Zero-cost generators retain the corrected convention. *)
Theorem caratheodory_increasing_borel_generator_bounds (R : realType) (X : metricType R)
    (F : set (set X)) (c psi : set X -> \bar R)
    (E : set X -> set X) (k : R) (A : nat -> set X) (t : nat -> R) :
  is_weak_caratheodory_enlargement F c E k ->
  is_caratheodory_limit (fun j : set_type F=>val j) (fun j=>c (val j)) psi ->
  (forall S, F S -> closed S) ->
  (forall n, borel_set (A n)) -> (forall n, psi (A n)< +oo) ->
  (forall n m, (n<=m)%N -> A n `<=` A m) -> (forall n, (1<t n)%R) ->
  exists (B : nat -> set X) (r : nat -> R),
    (forall n, borel_set (B n)) /\
    (forall n m, (n<=m)%N -> B n `<=` B m) /\
    (forall n, B n `<=` A n) /\
    psi ((\bigcup_n A n) `\` \bigcup_n B n)=0 /\
    (forall n, (0<r n)%R) /\
    forall n S, F S -> extended_metric_diameter S<=(r n)%:E -> psi (B n `&` S)<=(t n)%:E*c S.
Proof.
move=> hE hp hclosed hA hAfin hinc ht.
have hc S (hS : F S) := weak_enlargement_cost_nonnegative hE hS.
have hm := caratheodory_limit_is_measure hp (fun j=>hc _ (set_valP j)).
have hr := caratheodory_limit_borel_regular hp (fun j=>hc _ (set_valP j))
  (fun j=>closed_borel_set (hclosed _ (set_valP j))).
have hS S (hFS : F S) : measure_measurable psi S :=
  borel_regular_borel_measurable hm hr (closed_borel_set (hclosed _ hFS)).
have happrox n := @borel_uniform_generator_approximation R X F c psi (A n) (t n)
  (geometric_error_budget 1 n) hm hr (hA n) (hAfin n) hc hS (ht n)
  (geometric_error_budget_positive n (@ltr01 R))
  (@caratheodory_finite_restriction_density_bound R X F c psi E k (A n) hE hp hclosed (hAfin n)).
pose C n := projT1 (cid (happrox n)).
pose r n := projT1 (cid (projT2 (cid (happrox n)))).
have hC n := projT2 (cid (projT2 (cid (happrox n)))).
have hsum : nonnegative_sum setT (fun n=>psi (A n `\` C n))< +oo.
  apply: le_lt_trans _ (ltry ((1:R)/2)).
  apply: le_trans _ (geometric_error_sum_bound (@ltr01 R)).
  apply: nonnegative_sum_mono=> n _; exact: ltW (hC n).2.2.2.1.
have [B [hB [hBinc [hBC hnull]]]] := @increasing_borel_approximation_from_losses R X psi A C hm
  (fun n=>(hC n).1) (fun n=>(hC n).2.1) hinc hsum.
exists B,r; split=> //; split=> //; split.
- move=> n x hx; exact: (hC n).2.1 x (hBC n x hx).
- split=> //; split; first by move=> n; exact: (hC n).2.2.1.
  move=> n S hFS hdS; apply: le_trans _ ((hC n).2.2.2.2 S hFS hdS).
  apply: (@measure_mono R X psi hm)=> x [hx hxS]; split=> //; exact: hBC n x hx.
Qed.
