(** Federer (1969), 2.5.3, first further condition, p. 94, proof p. 95:
    inner approximation by closed unit levels minus F1 sets. We follow that
    proof and keep explicit error estimates. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal.
From Federer Require Import FunctionLatticeUP FunctionLatticeLevelFamilies FunctionLatticeLevelMeasurability
  FunctionLatticeUnionInnerApproximation RepresentedLatticeClosedLevels FiniteMeasurableDifferenceValue
  DaniellCoverUP DaniellOuterApproximation RealIntegralFunctionalUP MeasureUP MeasureBasic
  MeasureSplit MeasureFiniteClosure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [daniell_inner_difference_approximation]: quantitative form
    of the first further condition in Federer 2.5.3, p. 94, proved on p. 95.
    this is stronger than the printed 4 delta bound and supports the same
    supremum identity. A is measurable and has finite mass. *)
Theorem daniell_inner_difference_approximation (R : realType) (X : choiceType)
    (L : set (X -> R)) (F : (X -> R) -> R) (hL : is_function_lattice L)
    (mu : set X -> \bar R) (hm : is_measure mu) (hF : is_real_integral_functional mu L F)
    (hc : is_daniell_cover_envelope L F mu) (A : set X) (d : R) :
  measure_measurable mu A -> mu A < +oo -> (0 < d)%R ->
  exists (h : X -> R) (E : set X), positive_function_lattice L h /\
    function_lattice_increasing_levels L E /\
    [set x | (1 <= h x)%R] `\` E `<=` A /\
    measure_measurable mu ([set x | (1 <= h x)%R] `\` E) /\
    mu A <= mu ([set x | (1 <= h x)%R] `\` E)+(d+(d+d))%R%:E.
Proof.
move=> hA hAfin hd.
have hAf : mu A \is a fin_num by rewrite ge0_fin_numE //; exact: (@measure_nonnegative R X mu hm A).
have hr : mu A < (fine (mu A)+d)%R%:E by rewrite -(fineK hAf) lte_fin ltrDl.
have [V [hAV [hV hVb]]] := @daniell_finite_outer_approximation R X L F mu hm hF hc A _ hr.
have hVfin : mu V < +oo := le_lt_trans hVb (ltry _).
have hVf : mu V \is a fin_num by rewrite ge0_fin_numE //; exact: (@measure_nonnegative R X mu hm V).
have hlow : (fine (mu V)-d)%R%:E < mu V by rewrite -(fineK hVf) lte_fin ltrBlDl ltrDr.
have [h [hh [hCV hCb]]] := @represented_lattice_union_inner_approximation R X L F hL mu hm hF V _ hV hlow.
pose C := [set x | (1 <= h x)%R].
have hC : measure_measurable mu C := @represented_lattice_closed_upper_level_measurable R X L F mu hm hF h 1%R hh.1.
have hCf : mu C \is a fin_num.
  rewrite ge0_fin_numE; last exact: (@measure_nonnegative R X mu hm C).
  exact: le_lt_trans (@measure_mono R X mu hm C V hCV) hVfin.
have hVC : mu (V `\` C) <= d%:E.
  rewrite (@finite_measurable_difference_value R X mu hm V C hC hCV hVfin) lee_fin lerBlDr.
  have hb : (fine (mu V)-d <= fine (mu C))%R.
    have hb := ltW hCb; by move: hb; rewrite -(fineK hCf) lee_fin.
  by move: hb; rewrite lerBlDr addrC.
have hVA : mu (V `\` A) <= d%:E.
  rewrite (@finite_measurable_difference_value R X mu hm V A hA hAV hVfin) lee_fin lerBlDr addrC.
  by move: hVb; rewrite -(fineK hVf) lee_fin.
have hAC : mu (A `\` C) <= d%:E.
  apply: (le_trans _ hVC); apply: (@measure_mono R X mu hm)=> x [hx hn]; by split=> //; exact: hAV x hx.
have hCA : mu (C `\` A) <= d%:E.
  apply: (le_trans _ hVA); apply: (@measure_mono R X mu hm)=> x [hx hn]; by split=> //; exact: hCV x hx.
have hCA2 : mu (C `\` A) < (d+d)%R%:E.
  apply: (le_lt_trans hCA); by rewrite lte_fin ltrDl.
have [E [hCAE [hE hEb]]] := @daniell_finite_outer_approximation R X L F mu hm hF hc (C `\` A) _ hCA2.
pose K := C `\` E.
have hKA : K `<=` A.
  move=> x [hx hn]; apply: contrapT=> hna; apply: hn; exact: hCAE x (conj hx hna).
have hEm := @represented_lattice_increasing_level_measurable R X L F mu hm hF E hE.
have hK : measure_measurable mu K := @measure_measurable_difference R X mu hm C E hC hEm.
have hcover : A `\` K `<=` (A `\` C) `|` E.
  move=> x [hx hn]; case: (pselect (C x))=> hcX; last by left; split.
  right; apply: contrapT=> hne; apply: hn; by split.
have herror : mu (A `\` K) <= (d+(d+d))%R%:E.
  apply: (le_trans (@measure_binary_cover R X mu hm _ _ _ hcover)).
  rewrite EFinD; exact: leeD hAC hEb.
have hIK : A `&` K=K.
  apply/seteqP; split=> x; first by move=> [_ hx].
  move=> hx; split=> //; exact: hKA x hx.
exists h,E; split=> //; split=> //; split=> //; split=> //.
rewrite (hK A) hIK; exact: leeD (lexx _) herror.
Qed.
