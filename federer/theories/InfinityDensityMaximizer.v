(** Federer (1969), 2.5.7, p. 99: select a maximal density in case p=1,
    q=infinity by the weighted covering-set integral functional. The finite
    positive-mass cover is constructed from countable measurability and
    nonzero measure; it is not an additional assumption. As in the finite-q
    proof, chain domination of scalar scores suffices for the supremum
    argument. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal.
From Federer Require Import MeasureUP MeasureAlmostUP MeasureAlmostBasic CountablyMeasurableUP
  FunctionLatticeUP MonotoneDaniellIntegralUP ExtendedRealBoundsUP ExtendedIncreasingLimitSupremum
  TotalScalarLpUP TotalScalarLpFiniteSeminorm LpConjugatePair LpDominatedDensityFamily
  LpDominatedDensityMaximum RealLowerLimitReplacement LpDominatedDensityIncreasingLimit
  PositiveFiniteMeasurableCover CoverDensityScore IncreasingFamilyMaximizer.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [infinity_density_cover_maximizer]: the actual maximum of the
    covering-set score on U in Federer 2.5.7, p. 99 All integral bounds and
    chain-closure premises are discharged. *)
Theorem infinity_density_cover_maximizer (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (F : nat -> set X)
    (P : (X -> R) -> R) (M : R) :
  (forall n, measure_measurable mu (F n) /\ 0 < mu (F n) < +oo) ->
  (0 <= M)%R ->
  is_monotone_daniell_integral (positive_function_lattice (total_scalar_lp mu 1)) P ->
  (forall f, positive_function_lattice (total_scalar_lp mu 1) f -> (0 <= P f)%R) ->
  (forall f, positive_function_lattice (total_scalar_lp mu 1) f ->
    (P f <= M*finite_total_scalar_lp_norm mu 1 f)%R) ->
  exists k, lp_dominated_density_family mu 1 +oo P k /\
    forall u, lp_dominated_density_family mu 1 +oo P u ->
      (cover_density_score mu F u <= cover_density_score mu F k)%R.
Proof.
move=> hF hM hP hP0 hPb.
pose U := lp_dominated_density_family mu 1 +oo P.
have hpq : @is_lp_conjugate_pair R 1 +oo by right; left.
have hnorm u : U u -> total_scalar_lp_norm mu +oo u <= M%:E.
  exact: (@lp_dominated_density_norm_bound R X mu hm 1 +oo P u M hpq hM hPb).
have hb u : U u -> (0 <= cover_density_score mu F u <= M)%R.
  move=> hu; exact: (@cover_density_score_bounds R X mu hm F u M hF hM hu.1 hu.2.1 (hnorm u hu)).
have hnonempty : exists u, U u.
  exists (fun _ => 0%R); exact: (@zero_lp_dominated_density R X mu hm 1 +oo P (leey _) hP0).
have hmax u v : U u -> U v -> U (fun x => Order.max (u x) (v x)).
  exact: (@lp_dominated_density_maximum R X mu hm 1 +oo P u v hpq hP).
have hmono u v : U u -> U v -> function_le u v ->
    (cover_density_score mu F u <= cover_density_score mu F v)%R.
  move=> hu hv huv; apply: (@cover_density_score_almost_order R X mu hm F u v M hF hM
    hu.1 hv.1 hu.2.1 hv.2.1 (hnorm u hu) (hnorm v hv)).
  apply: (@measure_almost_everywhere_mono R X mu hm setT _ _ (measure_almost_everywhere_true hm))=> x _; exact: huv.
have hchain (v : nat -> X -> R) : (forall n, U (v n)) ->
    (forall n x, (v n x <= v n.+1 x)%R) -> exists k, U k /\
    forall n, (cover_density_score mu F (v n) <= cover_density_score mu F k)%R.
  move=> hv hstep.
  have hinc n m x : (n <= m)%N -> (v n x <= v m x)%R.
    exact: (@homo_leq R (fun n => v n x) (fun a b => is_true (a <= b)%R)
      (fun a => lexx a) (fun b a c hab hbc => le_trans hab hbc) (fun n => hstep n x) n m).
  have [hk [hkb hl]] := @lp_dominated_density_increasing_limit R X mu hm 1 +oo P M v hpq hM hPb hv hinc.
  exists (real_lower_limit_replacement v); split=> // n.
  apply: (@cover_density_score_almost_order R X mu hm F _ _ M hF hM
    (hv n).1 hk.1 (hv n).2.1 hk.2.1 (hnorm _ (hv n)) hkb).
  apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ hl)=> x hx.
  have hh : (v n x)%:E <= (real_lower_limit_replacement v x)%:E.
    apply: (extended_real_supremum_upper (extended_increasing_limit_supremum hx)); by exists n.
  by rewrite lee_fin in hh.
have [k [hk [hku _]]] := @increasing_function_family_maximizer R X U
  (cover_density_score mu F) M hnonempty hb hmax hmono hchain.
by exists k.
Qed.

(** Source for [infinity_density_maximal_member]: no strictly larger density
    lies above k+ in Federer's almost order, 2.5.7, p. 99, case (ii) This
    construction explicitly uses the countable- measurability hypothesis;
    the zero measure is treated separately. *)
Theorem infinity_density_maximal_member (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (P : (X -> R) -> R) (M : R) :
  measure_countably_measurable mu setT -> 0 < mu setT -> (0 <= M)%R ->
  is_monotone_daniell_integral (positive_function_lattice (total_scalar_lp mu 1)) P ->
  (forall f, positive_function_lattice (total_scalar_lp mu 1) f -> (0 <= P f)%R) ->
  (forall f, positive_function_lattice (total_scalar_lp mu 1) f ->
    (P f <= M*finite_total_scalar_lp_norm mu 1 f)%R) ->
  exists k, lp_dominated_density_family mu 1 +oo P k /\
    forall u, lp_dominated_density_family mu 1 +oo P u ->
      measure_almost_everywhere mu [set x | (k x <= u x)%R] ->
      ~ (0 < mu [set x | (k x < u x)%R]).
Proof.
move=> hX hpos hM hP hP0 hPb.
have [F [hcover hF]] := @positive_finite_measurable_cover R X mu hm hX hpos.
have [k [hk hmax]] := @infinity_density_cover_maximizer R X mu hm F P M hF hM hP hP0 hPb.
have hpq : @is_lp_conjugate_pair R 1 +oo by right; left.
have hnorm u := @lp_dominated_density_norm_bound R X mu hm 1 +oo P u M hpq hM hPb.
exists k; split=> // u hu hku hstrict.
have hh := @cover_density_score_strict_order R X mu hm F k u M hcover hF hM
  hk.1 hu.1 hk.2.1 hu.2.1 (hnorm k hk) (hnorm u hu) hku hstrict.
by rewrite ltNge (hmax u hu) in hh.
Qed.
