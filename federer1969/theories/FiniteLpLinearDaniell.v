(** Federer (1969), 2.5.7, p. 98: bounded linear functionals on finite-p
    total scalar Lebesgue spaces are Daniell integrals. The corrected closed
    unit ball and total-domain conventions follow erratum p. 2, book p. 98
    lines 10–11. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import MeasureUP VectorFunctionLattice FunctionLatticeSeminormUP FunctionOperatorSeminorm
  TotalScalarLpUP TotalScalarLpLattice TotalScalarLpFiniteSeminorm TotalScalarLpFunctionalBounds
  FiniteLpIncreasingContinuity MonotoneDaniellIntegralUP DaniellIntegralUP
  ExtendedRealOrderLimit RealScalarOrderLimits RealErrorOrderLimit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [finite_lp_bounded_linear_increasing_continuity]: ordinary
    convergence of the functional values required in Federer 2.5.7, p. 98
    The original functional may have both signs and need not be monotone. *)
Lemma finite_lp_bounded_linear_increasing_continuity (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (p : R)
    (A : (X -> R) -> R) M :
  (1 <= p)%R -> is_linear_functional_on_functions (total_scalar_lp mu p%:E) A ->
  (forall f, total_scalar_lp mu p%:E f -> (`|A f| <= M*finite_total_scalar_lp_norm mu p%:E f)%R) ->
  forall f g, (forall n, total_scalar_lp mu p%:E (f n)) -> total_scalar_lp mu p%:E g ->
    real_functions_increase_to f g -> extended_order_limit (fun n => (A (f n))%:E) (A g)%:E.
Proof.
move=> hp hA hb f g hf hg hl.
pose d n x := (g x-f n x)%R.
have hd n : total_scalar_lp mu p%:E (d n).
  exact: (@total_scalar_lp_subtract R X mu hm p%:E g (f n) hg (hf n)).
have hNlim := @finite_lp_increasing_error_norm_limit R X mu hm p f g hp hf hg hl.
have hlim : extended_order_limit (fun n => (finite_total_scalar_lp_norm mu p%:E (d n))%:E) 0.
  have he : (fun n => (finite_total_scalar_lp_norm mu p%:E (d n))%:E)=
      (fun n => total_scalar_lp_norm mu p%:E (d n)).
    apply: funext=> n; exact: (@finite_total_scalar_lp_norm_exact R X mu hm p%:E (d n) (hd n)).
  rewrite he; exact: hNlim.
have hscale := @real_scalar_order_limit R (fun n => finite_total_scalar_lp_norm mu p%:E (d n)) 0%R M hlim.
rewrite mulr0 in hscale.
apply: (@real_integral_error_comparison_limit R (fun n => A (f n))
  (fun n => (M*finite_total_scalar_lp_norm mu p%:E (d n))%R) (A g) _ hscale)=> n.
have he := @vector_lattice_additive_difference R X (total_scalar_lp mu p%:E) A
  (@total_scalar_lp_vector_lattice R X mu hm p%:E hp) hA.1 g (f n) hg (hf n).
rewrite distrC -he; exact: hb _ (hd n).
Qed.

(** Source for [finite_lp_bounded_linear_is_daniell]: the complete
    preliminary Daniell assertion of Federer 2.5.7, p. 98, for 1 <= p <
    infinity Unlike the infinity case, increasing continuity is derived
    here. *)
Theorem finite_lp_bounded_linear_is_daniell (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (p : R) (A : (X -> R) -> R) :
  (1 <= p)%R -> is_linear_functional_on_functions (total_scalar_lp mu p%:E) A ->
  function_operator_seminorm (total_scalar_lp mu p%:E) A (finite_total_scalar_lp_norm mu p%:E) < +oo ->
  is_daniell_integral (total_scalar_lp mu p%:E) A.
Proof.
move=> hp hA hb.
have [M [hM [hM0 hbound]]] := @total_scalar_lp_functional_bound R X mu hm p%:E A hp hA hb.
apply: (@bounded_lp_linear_daniell_with_increasing_continuity R X mu hm p%:E A hp hA hb).
exact: (@finite_lp_bounded_linear_increasing_continuity R X mu hm p A M hp hA hbound).
Qed.
