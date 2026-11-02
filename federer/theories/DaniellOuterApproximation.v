(** Federer (1969), 2.5.3, pp. 94–95: outer approximations by F1 sets for
    the measure constructed in 2.5.2. We choose a threshold from the
    requested finite error bound, an equivalent quantitative version of that
    step. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal.
From Federer Require Import FunctionLatticeUP FunctionLatticeLevelFamilies DaniellCoverUP DaniellCoverBasic
  DaniellSuitingLevelCover RealIntegralFunctionalUP MeasureUP MeasureBasic ExtendedRealBoundsUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [daniell_finite_outer_approximation]: quantitative F1 outer
    approximation supporting the regularity proof in Federer 2.5.3, pp.
    94–95 Every real strict upper bound r for phi(S) admits an F1 superset
    of measure at most r. *)
Theorem daniell_finite_outer_approximation (R : realType) (X : choiceType)
    (L : set (X -> R)) (A : (X -> R) -> R) (mu : set X -> \bar R)
    (hm : is_measure mu) (hA : is_real_integral_functional mu L A)
    (hc : is_daniell_cover_envelope L A mu) (S : set X) (r : R) :
  mu S < r%:E -> exists V,
    S `<=` V /\ function_lattice_increasing_levels L V /\ mu V <= r%:E.
Proof.
move=> hr.
have hfin : mu S \is a fin_num.
  rewrite ge0_fin_numE; last exact: (@measure_nonnegative R X mu hm S).
  exact: lt_trans hr (ltry r).
pose m := fine (mu S).
have hmE : mu S=m%:E := esym (fineK hfin).
have hm0 : (0 <= m)%R.
  have h := @measure_nonnegative R X mu hm S; by move: h; rewrite hmE lee_fin.
have hmr : (m < r)%R by move: hr; rewrite hmE lte_fin.
pose q := ((m+r)/2)%R.
have hmq : (m < q)%R := (midf_lt hmr).1.
have hqr : (q < r)%R := (midf_lt hmr).2.
have hq0 : (0 < q)%R := le_lt_trans hm0 hmq.
have hr0 : (0 < r)%R := lt_trans hq0 hqr.
pose t := (q/r)%R.
have ht0 : (0 < t)%R by rewrite /t divr_gt0.
have ht1 : (t < 1)%R by rewrite /t (@ltr_pdivrMr R r 1 q hr0) mul1r.
have hmuq : mu S < q%:E by rewrite hmE lte_fin.
have [f [c [hf [hcost hcq]]]] := daniell_cover_approximation hc hmuq.
have hvalues n : (A (f n) <= q)%R.
  have hfn : (A (f n))%:E <= c.
    apply: (extended_real_supremum_upper hcost); by exists n.
  have h := ltW (le_lt_trans hfn hcq); by move: h; rewrite lee_fin.
have [V [hSV [hV hbound]]] := @daniell_suiting_strict_level_cover R X L A mu hm hA S f q t hf hvalues ht0 ht1.
exists V; split=> //; split=> //.
have hqt : (q/t=r)%R.
  by rewrite /t invfM invrK mulrA mulfV ?mul1r // gt_eqF.
by rewrite hqt in hbound.
Qed.
