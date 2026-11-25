(** Federer (1969), 2.5.3, proof p. 95: approximation of finite positive
    combinations. We prove those properties using finite integral error
    witnesses. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal.
From Federer Require Import FunctionLatticeUP FunctionLatticeLaws LatticeL1ApproximationUP
  RealIntegralFunctionalUP RealIntegralErrorArithmetic SummableRealFunctionUP SummableRealArithmetic
  MeasureUP MeasureIntegralUP MeasureAlmostUP MeasureAlmostBasic MeasureConullZeroIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [real_total_zero_integral]: supporting zero-error boundary in
    Federer 2.5.3, proof p. 95 It uses the earlier null-function integral,
    and permits infinite total mass. *)
Lemma real_total_zero_integral (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) :
  is_measure_integral mu (real_total_integrand (fun _ : X => (0%R : R))) 0.
Proof.
apply: (@measure_almost_zero_integral R X mu hm (real_total_integrand (fun _ : X => 0%R))).
apply: (@measure_almost_everywhere_mono R X mu hm setT _ _ (measure_almost_everywhere_true hm))=> x _.
by apply/real_total_integrand_graph.
Qed.

(** Source for [positive_lattice_l1_approximable_zero]: empty
    finite-combination case of Federer 2.5.3, proof p. 95 Membership of zero
    is explicit because the empty lattice has no approximants. *)
Lemma positive_lattice_l1_approximable_zero (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (L : set (X -> R)) :
  L (fun _ => 0%R) -> is_positive_lattice_l1_approximable mu L (fun _ => 0%R).
Proof.
move=> hzero; have hi := @real_total_zero_integral R X mu hm.
split; first by exists 0%R.
move=> d hd; exists (fun _ => 0%R),0%R; split; first by split=> // x.
split=> //.
have he : (fun _ : X => `|(0%R : R)-0|%R)=(fun _ => (0%R : R)).
  by apply: funext=> x; rewrite subrr normr0.
by rewrite he.
Qed.

(** Source for [positive_lattice_l1_approximable_add]: Supporting Federer
    2.5.3, p. 95. *)
Lemma positive_lattice_l1_approximable_add (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (L : set (X -> R)) (F : (X -> R) -> R)
    (hL : is_function_lattice L) (hF : is_real_integral_functional mu L F) (f g : X -> R) :
  is_positive_lattice_l1_approximable mu L f -> is_positive_lattice_l1_approximable mu L g ->
  is_positive_lattice_l1_approximable mu L (fun x => (f x+g x)%R).
Proof.
move=> [hf hfa] [hg hga]; split; first exact: (@summable_real_add R X mu hm f g hf hg).
move=> d hd; have hd2 : (0 < d/2)%R by rewrite divr_gt0 // ltr0n.
have [k [a [hk [ha had]]]] := hfa _ hd2.
have [l [b [hl [hb hbd]]]] := hga _ hd2.
have hks : summable_real_functions mu k by exists (F k); exact: hF k hk.1.
have hls : summable_real_functions mu l by exists (F l); exact: hF l hl.1.
have [e [he heb]] := @real_total_integral_error_add R X mu hm k f l g a b hks hf hls hg ha hb.
exists (fun x => (k x+l x)%R),e; split.
- split; first exact: (@function_lattice_add R X L hL k l hk.1 hl.1).
  move=> x; exact: addr_ge0 (hk.2 x) (hl.2 x).
- split=> //; have hsum := ltrD had hbd.
  rewrite -splitr in hsum; exact: le_lt_trans heb hsum.
Qed.

(** Source for [positive_lattice_l1_approximable_scale]: Supporting Federer
    2.5.3, p. 95.The zero coefficient is treated without dividing by it. *)
Lemma positive_lattice_l1_approximable_scale (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (L : set (X -> R))
    (hL : is_function_lattice L) (f : X -> R) (c : R) :
  (0 <= c)%R -> is_positive_lattice_l1_approximable mu L f ->
  is_positive_lattice_l1_approximable mu L (fun x => (c*f x)%R).
Proof.
move=> hc [hf hfa].
case: (eqVneq c 0%R)=> hc0.
- have [k [e [hk _]]] := hfa 1%R ltr01.
  have he : (fun x => (c*f x)%R)=(fun _ => (0%R : R)) by apply: funext=> x; rewrite hc0 mul0r.
  rewrite he; apply: (@positive_lattice_l1_approximable_zero R X mu hm L).
  exact: (@function_lattice_zero R X L hL k hk.1).
- have hcpos : (0 < c)%R by rewrite lt_neqAle eq_sym hc0 hc.
  split; first exact: (@summable_real_scale R X mu hm f c hf).
  move=> d hd; have hdc : (0 < d/c)%R by rewrite divr_gt0.
  have [k [e [hk [he hed]]]] := hfa _ hdc.
  exists (fun x => (c*k x)%R),(c*e)%R; split.
  + split; first exact: (@function_lattice_scale R X L hL c k hc hk.1).
    move=> x; exact: mulr_ge0 hc (hk.2 x).
  + split; first exact: (@real_total_integral_error_scale R X mu hm k f e c hc he).
    have hh : (c*e < c*(d/c))%R by rewrite ltr_pM2l.
    by rewrite mulrCA divff // mulr1 in hh.
Qed.
