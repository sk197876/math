(** Federer (1969), 2.5.7, pp. 98–99: bounded linear functionals on total
    scalar Lp have finite upper bounds on positive order intervals. Erratum
    p. 2, book p. 98 lines 10–11, specifies total functions and the closed
    unit ball. Increasing continuity is treated separately. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import MeasureUP FunctionLatticeUP DaniellIntegralUP MonotoneDaniellIntegralUP
  ExtendedRealOrderLimit FunctionLatticeSeminormUP FunctionOperatorSeminorm
  TotalScalarLpUP TotalScalarLpLattice TotalScalarLpFiniteSeminorm.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [total_scalar_lp_unit_ball_criterion]: exact compatibility of
    the finite-valued norm interface with the closed ball in Federer 2.5.7,
    p. 98, erratum p. 2, book p. 98 line 11 *)
Lemma total_scalar_lp_unit_ball_criterion (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) p (f : X -> R) :
  total_scalar_lp mu p f ->
  (finite_total_scalar_lp_norm mu p f <= 1)%R = (total_scalar_lp_norm mu p f <= 1).
Proof.
move=> hf; by rewrite -(@finite_total_scalar_lp_norm_exact R X mu hm p f hf) lee_fin.
Qed.

(** Source for [total_scalar_lp_functional_bound]: the bound |mu(f)| <= M
    phi_(p)(f) from the exact corrected M in Federer 2.5.7, pp. 98–99 Zero
    measure and zero-seminorm vectors are included. *)
Theorem total_scalar_lp_functional_bound (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) p (A : (X -> R) -> R) :
  1 <= p -> is_linear_functional_on_functions (total_scalar_lp mu p) A ->
  function_operator_seminorm (total_scalar_lp mu p) A (finite_total_scalar_lp_norm mu p) < +oo ->
  exists M : R,
    function_operator_seminorm (total_scalar_lp mu p) A (finite_total_scalar_lp_norm mu p)=M%:E /\
    (0 <= M)%R /\ forall f, total_scalar_lp mu p f ->
      (`|A f| <= M*finite_total_scalar_lp_norm mu p f)%R.
Proof.
move=> hp hA hbound; exact: (@function_operator_seminorm_finite_bound R X
  (total_scalar_lp mu p) A (finite_total_scalar_lp_norm mu p)
  (@total_scalar_lp_vector_lattice R X mu hm p hp) hA
  (@finite_total_scalar_lp_norm_laws R X mu hm p) hbound).
Qed.

(** Source for [total_scalar_lp_functional_order_bound]: the
    finite-variation bound in Federer 2.5.7, p. 98 It proves the third
    Daniell hypothesis without assuming that A preserves order. *)
Lemma total_scalar_lp_functional_order_bound (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) p (A : (X -> R) -> R) (M : R) :
  (0 <= M)%R ->
  (forall f, total_scalar_lp mu p f -> (`|A f| <= M*finite_total_scalar_lp_norm mu p f)%R) ->
  forall f, total_scalar_lp mu p f -> forall k,
    lattice_positive_order_interval (total_scalar_lp mu p) f k ->
    (A k <= M*finite_total_scalar_lp_norm mu p f)%R.
Proof.
move=> hM hb f hf k hk.
have hgf : forall x, (`|k x| <= `|f x|)%R.
  move=> x; have hf0 := le_trans (hk.2.1 x) (hk.2.2 x).
  by rewrite (ger0_norm (hk.2.1 x)) (ger0_norm hf0); exact: hk.2.2.
have hn := @finite_total_scalar_lp_norm_order R X mu hm p k f hk.1 hf hgf.
apply: le_trans (ler_norm (A k)) _.
apply: le_trans (hb k hk.1) _.
case: (eqVneq M 0%R)=> [->|hneq]; first by rewrite !mul0r.
have hpos : (0 < M)%R by rewrite lt_neqAle eq_sym hneq hM.
by rewrite (ler_pM2l hpos).
Qed.

(** Source for [bounded_lp_linear_daniell_with_increasing_continuity]:
    preliminary Daniell conclusion in Federer 2.5.7, p. 98 This supporting
    theorem proves the first three Daniell laws from linearity and
    boundedness. Ordinary increasing continuity is explicit here, as in
    endpoint case (iii); its finite-p derivation is a separate argument. *)
Theorem bounded_lp_linear_daniell_with_increasing_continuity (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) p (A : (X -> R) -> R) :
  1 <= p -> is_linear_functional_on_functions (total_scalar_lp mu p) A ->
  function_operator_seminorm (total_scalar_lp mu p) A (finite_total_scalar_lp_norm mu p) < +oo ->
  (forall f g, (forall n, total_scalar_lp mu p (f n)) -> total_scalar_lp mu p g ->
    real_functions_increase_to f g -> extended_order_limit (fun n => (A (f n))%:E) (A g)%:E) ->
  is_daniell_integral (total_scalar_lp mu p) A.
Proof.
move=> hp hA hb hc.
have [M [hM [hM0 hbound]]] := @total_scalar_lp_functional_bound R X mu hm p A hp hA hb.
constructor.
- exact: hA.1.
- move=> c f hc0 hf; exact: hA.2 c f hf.
- move=> f hf; exists (M*finite_total_scalar_lp_norm mu p f)%R.
  exact: (@total_scalar_lp_functional_order_bound R X mu hm p A M hM0 hbound f hf).
- exact: hc.
Qed.
