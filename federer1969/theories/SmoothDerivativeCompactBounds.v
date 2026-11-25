(** Federer (1969), 4.1.1, p. 343: all derivatives through
    a fixed finite order have a finite common norm bound on K.
    The proof reuses continuity on compact sets and does not assume
    a supremum, finite target dimension or target completeness. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormRegularity ContinuousMultilinearUP
  ContinuousMultilinearSealed ContinuousMultilinearNorm NormCompactFunctionBound
  SmoothCompactSet SmoothFunctionDerivativesUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section CompactDerivativeBounds.
Variable R:realType.
Variables X Y:lmodType R.
Variables (NX:X->R) (NY:Y->R).
Hypothesis hNX:is_real_norm NX.
Hypothesis hNY:is_real_norm NY.
Variable U:set X.
Variable E:lmodType R.
Variable value:E->X->Y.
Local Notation Z := (fun k=>@ContinuousMultilinear.space R k X Y NX NY hNX hNY).
Local Notation ZN := (fun k=>@ContinuousMultilinear.norm R k X Y NX NY hNX hNY).
Local Notation hZ := (fun k=>@ContinuousMultilinear.laws R k X Y NX NY hNX hNY).
Variable D:forall k,X->Hom E (Z k).
Hypothesis hD:@is_smooth_function_derivatives R X Y NX NY hNX hNY U E value D.

(** Source for [smooth_derivative_compact_order_bound]: each
    derivative is bounded on the original compact K, supporting
    the seminorms of Federer 4.1.1, p. 343. *)
Lemma smooth_derivative_compact_order_bound (K:smooth_compact_set hNX U) f k :
  exists C:R,0<C /\ forall x,smooth_compact_carrier K x ->
    @ZN k (@D k x f)<=C.
Proof.
exact:(@norm_class_zero_compact_bounded R X (Z k) NX (@ZN k) hNX
  (continuous_multilinear_norm_is_norm hNY (hZ k)) U (smooth_compact_carrier K)
  (fun x=>@D k x f) (smooth_compact_is_compact K) (smooth_compact_in_domain K)
  (smooth_derivative_continuous hD k f)).
Qed.

(** Source for [smooth_derivative_compact_finite_order_bound]:
    one finite bound controls every derivative through i on K,
    supporting nu^i_K in Federer 4.1.1, p. 343. The empty compact
    set and the order-zero family are retained. *)
Theorem smooth_derivative_compact_finite_order_bound
    (K:smooth_compact_set hNX U) f i :
  exists C:R,0<=C /\ forall (j:'I_i.+1) x,
    smooth_compact_carrier K x -> @ZN j (@D j x f)<=C.
Proof.
have hChoices(j:'I_i.+1):exists C:R,0<C /\ forall x,
    smooth_compact_carrier K x -> @ZN j (@D j x f)<=C.
  exact:smooth_derivative_compact_order_bound.
have [M hM]:=choice hChoices.
pose C:=\sum_(j:'I_i.+1) M j.
have hC:0<=C by apply:sumr_ge0=>j _; exact:ltW (hM j).1.
exists C; split=>// j x hx.
apply:le_trans ((hM j).2 x hx) _.
rewrite /C (bigD1 j) //= lerDl.
by apply:sumr_ge0=>k _; exact:ltW (hM k).1.
Qed.
End CompactDerivativeBounds.
