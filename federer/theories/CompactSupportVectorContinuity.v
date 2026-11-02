(** Federer (1969), 2.5.14, p. 108, vector-valued paragraph: the compactness
    estimate of 2.5.13, p. 107, proves sequential continuity for the norms
    nu o xi_n. Linearity and finite order bounds remain hypotheses; the
    sequence-continuity clause of 2.5.12(5) is a conclusion. Source
    conventions: OrderBoundedVectorFunctionalUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealNormUP FunctionLatticeUP VectorDaniellHypotheses
  OrderBoundedVectorFunctionalUP OrderBoundedVectorAbsolute
  CompactSupportFunctionUP CompactCutoffUP CompactCutoff
  CompactDecreasingUniformApproximation RealErrorOrderLimit ExtendedRealOrderLimit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [compact_support_vector_functional_limit]: the
    vector analogue of the estimate in Federer 2.5.13,
    p. 107, explicitly invoked in 2.5.14, p. 108.
    A compact cutoff bounds the common support; uniform decay
    and the finite order bound force T(xi_n) to tend to zero. *)
Theorem compact_support_vector_functional_limit (R : realType) (X : topologicalType)
    (E : lmodType R) (N : E -> R) (hN : is_real_norm N)
    (Q : set (X -> E)) (T : (X -> E) -> R)
    (hh : hausdorff_space X) (hl : locally_compact (@setT X)) :
  is_vector_function_space Q ->
  is_vector_lattice_module hN (@compactly_supported_continuous_functions R X) Q ->
  is_order_bounded_vector_functional N (@compactly_supported_continuous_functions R X) Q T ->
  forall xi : nat -> X -> E, (forall n, Q (xi n)) ->
    (forall x, extended_decreases_to (fun n => (N (xi n x))%:E) (0 : R)%:E) ->
    extended_order_limit (fun n => (T (xi n))%:E) (0 : R)%:E.
Proof.
move=> hQ hM hT xi hxi hdec.
pose L := @compactly_supported_continuous_functions R X.
pose g n x := N (xi n x).
have hg n : L (g n) := @vector_lattice_module_norm R X E N hN L Q hM (xi n) (hxi n).
pose K := real_function_support (g 0%N).
have hK : compact K := (hg 0%N).2.
pose u := @compact_cutoff R X K hh hl hK.
have hu := @compact_cutoff_specification R X K hh hl hK.
have huL : L u := compact_cutoff_function hu.
have hu0 : function_nonnegative u by move=> x; exact: (andP (compact_cutoff_range hu x)).1.
have [c [hc hb]] := @order_bounded_vector_absolute_bound R X E N hN L Q T u hQ hT (conj huL hu0).
apply: real_error_extended_order_limit=> e he.
have hcp : c<c+1 by rewrite ltrDl; exact: ltr01.
have hden : 0<c+1 := le_lt_trans hc hcp.
pose d := e/(c+1).
have hd : 0<d by rewrite /d divr_gt0.
have [M hMsmall] := @compact_decreasing_uniform_approximation R X K g d hK
  (fun n => (hg n).1) hdec hd.
exists M=> n hn.
have hgu : function_le (g n) (fun x => d*u x).
  move=> x; case: (pselect (K x))=> hx.
  - rewrite /u (compact_cutoff_on_set hu hx) mulr1; exact: ltW (hMsmall n hn x hx).
  - have hzero : g 0%N x=0 := real_function_zero_off_support hx.
    have hmono : g n x<=g 0%N x := (hdec x).1 0%N n (leq0n n).
    rewrite hzero in hmono.
    apply: le_trans hmono _; exact: mulr_ge0 (ltW hd) (hu0 x).
have hbnd := @order_bounded_vector_scaled_bound R X E N hN L Q T u c d (xi n)
  hQ hT hb hd (hxi n) hgu.
rewrite subr0; apply: le_lt_trans hbnd _.
have hm : d*c<d*(c+1) by rewrite ltr_pM2l.
by rewrite /d divfK ?gt_eqF // in hm.
Qed.

(** Source for [compact_support_vector_variation_functional]:
    Federer 2.5.14, p. 108, applies the compactness argument
    to obtain the sequence-continuity clause of 2.5.12(5),
    p. 103. This supporting theorem packages the resulting
    hypotheses for the subsequent variation construction. *)
Theorem compact_support_vector_variation_functional (R : realType) (X : topologicalType)
    (E : lmodType R) (N : E -> R) (hN : is_real_norm N)
    (Q : set (X -> E)) (T : (X -> E) -> R)
    (hh : hausdorff_space X) (hl : locally_compact (@setT X)) :
  is_vector_function_space Q ->
  is_vector_lattice_module hN (@compactly_supported_continuous_functions R X) Q ->
  is_order_bounded_vector_functional N (@compactly_supported_continuous_functions R X) Q T ->
  is_vector_variation_functional N (@compactly_supported_continuous_functions R X) Q T.
Proof.
move=> hQ hM hT; constructor.
- exact: order_bounded_vector_add hT.
- exact: order_bounded_vector_scale hT.
- exact: order_bounded_vector_bound hT.
- exact: compact_support_vector_functional_limit hh hl hQ hM hT.
Qed.
