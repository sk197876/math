(** Federer (1969), 2.5.14, p. 108: supporting scalar approximation for the
    vector representation with the Radon measure Phi. Compact inner
    approximation and open outer approximation are from 2.2.5, p. 63;
    compact cutoffs replace the characteristic tests in the density proof of
    2.5.3, p. 95. This does not assert global K(X)-regularity of an
    arbitrary Radon measure. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology lra.
From Federer Require Import MeasureUP MeasureBasic MeasureSplit MeasureFiniteClosure
  RadonMeasureUP RadonBorelRegularity RadonApproximationBounds RadonCompactApproximation
  CompactSupportFunctionUP CompactCutoffUP LocalizedCompactCutoffUP LocalizedCompactCutoff
  FunctionLatticeUP RealIntegralFunctionalUP SummableRealFunctionUP SummableRealArithmetic
  MeasureIntegralUP MeasureCharacteristicIntegral CharacteristicFunctionUP
  RealTotalCharacteristicBounds LatticeL1ApproximationUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [radon_compact_characteristic_approximable]:
    supporting density of K(X)+ for Federer 2.5.14,
    p. 108. Finite measurable characteristic functions admit
    compactly supported continuous approximants with arbitrarily
    small actual integral error, by 2.2.5, p. 63. *)
Theorem radon_compact_characteristic_approximable (R : realType) (X : topologicalType)
    (mu : set X -> \bar R) (hm : is_measure mu) (hr : is_radon_measure mu)
    (F : (X -> R) -> R)
    (hF : is_real_integral_functional mu (positive_function_lattice (@compactly_supported_continuous_functions R X)) F)
    (A : set X) (s : X -> R) :
  is_characteristic_function A s -> measure_measurable mu A -> mu A < +oo ->
  is_positive_lattice_l1_approximable mu (@compactly_supported_continuous_functions R X) s.
Proof.
move=> hs hA hfin.
have haf : mu A \is a fin_num by rewrite ge0_fin_numE //; exact: (@measure_nonnegative R X mu hm A).
have hsi : is_measure_integral mu (real_total_integrand s) (fine (mu A))%:E.
  rewrite fineK //; exact: (@measure_characteristic_integral R X mu hm A s hs hA).
have hss : summable_real_functions mu s by exists (fine (mu A)).
split=> // e he.
have he2 : (0<e/2)%R by rewrite divr_gt0 // ltr0n.
have [K [hK [hKA hAK]]] := @radon_compact_approximation R X mu hm hr A (e/2)%R hA hfin he2.
have [V [hV [hAV [hVfin hVA]]]] := @radon_finite_open_error R X mu hm hr A (e/2)%R hA hfin he2.
have hKV : K `<=` V by move=> x hx; exact: hAV x (hKA x hx).
pose u := @localized_compact_cutoff R X K V (radon_hausdorff hr) (radon_locally_compact hr) hK hV hKV.
have hu := @localized_compact_cutoff_specification R X K V (radon_hausdorff hr) (radon_locally_compact hr) hK hV hKV.
have hcut := localized_compact_cutoff_laws hu.
have huK := compact_cutoff_function hcut.
have hu0 : function_nonnegative u by move=> x; exact: (andP (compact_cutoff_range hcut x)).1.
have hus : summable_real_functions mu u by exists (F u); exact: hF u (conj huK hu0).
have [q hq] := summable_real_absolute hm (summable_real_subtract hm hus hss).
exists u,q; split; first by split.
split=> //.
have hKm := radon_compact_measurable hm hr hK.
have hVm := radon_open_measurable hr hV.
have hdiff := measure_measurable_difference hm hVm hKm.
have hqbd : q%:E <= mu (V `\` K).
  have h := @real_total_integral_supported_upper_bound R X mu hm (V `\` K)
    (fun x => `|u x-s x|%R) q%:E 1%R hdiff (@ltr01 R) hq.
  rewrite mul1e in h; apply: h.
  - move=> x _; have [h0 h1] := andP (compact_cutoff_range hcut x).
    change (is_true (0<=u x)%R) in h0; change (is_true (u x<=1)%R) in h1.
    case: (pselect (A x))=> hx.
    + rewrite (characteristic_on_set hs hx) ler_norml; apply/andP; split; lra.
    + rewrite (characteristic_off_set hs hx) subr0 (ger0_norm h0); exact h1.
  - move=> x hx; case: (pselect (K x))=> hk.
    + have hux : u x = 1%R := compact_cutoff_on_set hcut hk.
      by rewrite hux (characteristic_on_set hs (hKA x hk)) subrr normr0.
    + have hnv : ~ V x by move=> hv; apply: hx; by split.
      have hns : ~ real_function_support u x by move=> hu'; apply: hnv; exact: (@localized_compact_cutoff_support R X K V u hu x hu').
      have hna : ~ A x by move=> ha; apply: hnv; exact: hAV.
      by rewrite (real_function_zero_off_support hns) (characteristic_off_set hs hna) subrr normr0.
have hcover : (V `\` K) `<=` (V `\` A) `|` (A `\` K).
  move=> x [hv hk]; case: (pselect (A x))=> ha; [right|left]; by split.
have hb := @measure_binary_cover R X mu hm _ _ _ hcover.
have hAKfin : mu (A `\` K) \is a fin_num.
  rewrite ge0_fin_numE; last exact: (@measure_nonnegative R X mu hm (A `\` K)).
  exact: lt_trans hAK (ltry _).
have hsmall := lte_leD hAKfin hVA (ltW hAK).
rewrite -EFinD -splitr in hsmall.
have h := le_lt_trans (le_trans hqbd hb) hsmall; by rewrite lte_fin in h.
Qed.
