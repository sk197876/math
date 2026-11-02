(** Federer (1969), 2.5.7, pp. 98–99: select k+ maximizing tau on U when the
    density exponent q is finite. We use the proved chain closure and
    almost-order monotonicity; these imply that the chain representative
    dominates every scalar score, which is sufficient for the same supremum
    argument without a separate scalar limit calculation. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal.
From Federer Require Import MeasureUP MeasureAlmostUP MeasureAlmostBasic FunctionLatticeUP MonotoneDaniellIntegralUP
  ExtendedRealBoundsUP ExtendedIncreasingLimitSupremum TotalScalarLpUP TotalScalarLpNormLaws
  TotalScalarLpFiniteSeminorm LpConjugatePair LpDominatedDensityFamily LpDominatedDensityMaximum
  RealLowerLimitReplacement TotalScalarLpIncreasingLimit LpDominatedDensityIncreasingLimit
  PositiveFiniteLpStrictOrder IncreasingFamilyMaximizer.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [finite_density_norm_maximizer]: existence of k+ attaining
    the supremum of tau in Federer 2.5.7, p. 99, finite-q cases All closure
    hypotheses of the countable maximization lemma are discharged for the
    actual family U. *)
Theorem finite_density_norm_maximizer (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) p (q : R) (P : (X -> R) -> R) (M : R) :
  is_lp_conjugate_pair p q%:E -> (0 <= M)%R ->
  is_monotone_daniell_integral (positive_function_lattice (total_scalar_lp mu p)) P ->
  (forall f, positive_function_lattice (total_scalar_lp mu p) f -> (0 <= P f)%R) ->
  (forall f, positive_function_lattice (total_scalar_lp mu p) f ->
    (P f <= M*finite_total_scalar_lp_norm mu p f)%R) ->
  exists k, lp_dominated_density_family mu p q%:E P k /\
    forall u, lp_dominated_density_family mu p q%:E P u ->
      (finite_total_scalar_lp_norm mu q%:E u <= finite_total_scalar_lp_norm mu q%:E k)%R.
Proof.
move=> hpq hM hP hP0 hPb.
pose U := lp_dominated_density_family mu p q%:E P.
have hb u : U u -> (0 <= finite_total_scalar_lp_norm mu q%:E u <= M)%R.
  move=> hu; apply/andP; split.
  - apply: fine_ge0; exact: (@total_scalar_lp_norm_nonnegative R X mu hm _ _ hu.1.1 hu.1.2.1).
  - have hh := @lp_dominated_density_norm_bound R X mu hm p q%:E P u M hpq hM hPb hu.
    by rewrite -(@finite_total_scalar_lp_norm_exact R X mu hm q%:E u hu.1) lee_fin in hh.
have hnonempty : exists u, U u.
  exists (fun _ => 0%R); exact: (@zero_lp_dominated_density R X mu hm p q%:E P (lp_conjugate_pair_admissible hpq).2 hP0).
have hmax u v : U u -> U v -> U (fun x => Order.max (u x) (v x)).
  exact: (@lp_dominated_density_maximum R X mu hm p q%:E P u v hpq hP).
have hmono u v : U u -> U v -> function_le u v ->
    (finite_total_scalar_lp_norm mu q%:E u <= finite_total_scalar_lp_norm mu q%:E v)%R.
  move=> hu hv huv; apply: (@positive_finite_lp_norm_almost_order R X mu hm q u v hu.1 hv.1 hu.2.1 hv.2.1).
  apply: (@measure_almost_everywhere_mono R X mu hm setT _ _ (measure_almost_everywhere_true hm))=> x _; exact: huv.
have hchain (v : nat -> X -> R) : (forall n, U (v n)) ->
    (forall n x, (v n x <= v n.+1 x)%R) -> exists k, U k /\
    forall n, (finite_total_scalar_lp_norm mu q%:E (v n) <= finite_total_scalar_lp_norm mu q%:E k)%R.
  move=> hv hstep.
  have hinc n m x : (n <= m)%N -> (v n x <= v m x)%R.
    exact: (@homo_leq R (fun n => v n x) (fun a b => is_true (a <= b)%R)
      (fun a => lexx a) (fun b a c hab hbc => le_trans hab hbc) (fun n => hstep n x) n m).
  have [hk [_ hl]] := @lp_dominated_density_increasing_limit R X mu hm p q%:E P M v hpq hM hPb hv hinc.
  exists (real_lower_limit_replacement v); split=> // n.
  apply: (@positive_finite_lp_norm_almost_order R X mu hm q _ _ (hv n).1 hk.1 (hv n).2.1 hk.2.1).
  apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ hl)=> x hx.
  have hh : (v n x)%:E <= (real_lower_limit_replacement v x)%:E.
    apply: (extended_real_supremum_upper (extended_increasing_limit_supremum hx)); by exists n.
  by rewrite lee_fin in hh.
have [k [hk [hku _]]] := @increasing_function_family_maximizer R X U
  (finite_total_scalar_lp_norm mu q%:E) M hnonempty hb hmax hmono hchain.
by exists k.
Qed.

(** Source for [finite_density_maximal_member]: no strict larger density
    exists above k+ in Federer's almost order, 2.5.7, p. 99 This is
    maximality, before the later representation argument. *)
Corollary finite_density_maximal_member (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) p (q : R) (P : (X -> R) -> R) (M : R) :
  is_lp_conjugate_pair p q%:E -> (0 <= M)%R ->
  is_monotone_daniell_integral (positive_function_lattice (total_scalar_lp mu p)) P ->
  (forall f, positive_function_lattice (total_scalar_lp mu p) f -> (0 <= P f)%R) ->
  (forall f, positive_function_lattice (total_scalar_lp mu p) f ->
    (P f <= M*finite_total_scalar_lp_norm mu p f)%R) ->
  exists k, lp_dominated_density_family mu p q%:E P k /\
    forall u, lp_dominated_density_family mu p q%:E P u ->
      measure_almost_everywhere mu [set x | (k x <= u x)%R] ->
      ~ (0 < mu [set x | (k x < u x)%R]).
Proof.
move=> hpq hM hP hP0 hPb.
have [k [hk hmax]] := @finite_density_norm_maximizer R X mu hm p q P M hpq hM hP hP0 hPb.
exists k; split=> // u hu hku hpos.
have hh := @positive_finite_lp_norm_strict_order R X mu hm q k u hk.1 hu.1 hk.2.1 hu.2.1 hku hpos.
by rewrite ltNge (hmax u hu) in hh.
Qed.
