(** Federer (1969), 3.2.6, p. 246: evaluate
    the exact sign sets at a point carrying an actual
    derivative. Uniqueness excludes simultaneous positive
    and negative derivatives, without supplying a default. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets topology.
From Federer Require Import RealMetricBackground RealCurveDerivativeUP ScalarCurveDerivativeLoci PartialFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [positive_real_derivative_locus_at]: supporting
    pointwise evaluation of A_1 in Federer 3.2.6,
    p. 246, by uniqueness of the actual derivative. *)
Lemma positive_real_derivative_locus_at (R:realType) (f:R->R) x v:
  has_real_curve_derivative f x v ->
  (positive_real_derivative_locus f x <-> 0<v).
Proof.
move=>hv; split.
- move=>[w [hw hp]]; have he:v=w:=@partial_function_single_valued R R (real_curve_derivative f) x v w hv hw.
  by rewrite he.
- move=>hp; by exists v.
Qed.

(** Source for [negative_real_derivative_locus_at]: supporting
    pointwise evaluation of A_2 in Federer 3.2.6,
    p. 246, by uniqueness of the actual derivative. *)
Lemma negative_real_derivative_locus_at (R:realType) (f:R->R) x v:
  has_real_curve_derivative f x v ->
  (negative_real_derivative_locus f x <-> v<0).
Proof.
move=>hv; split.
- move=>[w [hw hp]]; have he:v=w:=@partial_function_single_valued R R (real_curve_derivative f) x v w hv hw.
  by rewrite he.
- move=>hp; by exists v.
Qed.

(** Source for [scalar_sign_interval_sets_at]: supporting
    evaluation of A_1,A_2 in Federer 3.2.6, p. 246,
    at an interior source point with actual derivative v. *)
Lemma scalar_sign_interval_sets_at (R:realType) (f:R->R) a b x v:
  a<x -> x<b -> has_real_curve_derivative f x v ->
  (scalar_positive_derivative_set f a b x <-> 0<v) /\
  (scalar_negative_derivative_set f a b x <-> v<0).
Proof.
move=>hax hxb hv.
have hI:(`]a,b[:set (real_line_metric R)) x by rewrite /= in_itv /= hax hxb.
split; split.
- by move=>[_ hx]; exact ((positive_real_derivative_locus_at hv).1 hx).
- move=>hx; split=>//; exact ((positive_real_derivative_locus_at hv).2 hx).
- by move=>[_ hx]; exact ((negative_real_derivative_locus_at hv).1 hx).
- move=>hx; split=>//; exact ((negative_real_derivative_locus_at hv).2 hx).
Qed.

(** Source for [scalar_derivative_sign_sets_subinterval]:
    supporting containment in the original interval for
    A_1 and A_2 in Federer 3.2.6, p. 246. *)
Lemma scalar_derivative_sign_sets_subinterval (R:realType) (f:R->R) a b:
  scalar_positive_derivative_set f a b `<=` (`[a,b]:set (real_line_metric R)) /\
  scalar_negative_derivative_set f a b `<=` (`[a,b]:set (real_line_metric R)).
Proof.
split=>x [hI _]; move:hI; rewrite /= in_itv /= =>/andP[hax hxb];
  by rewrite /= in_itv /= (ltW hax) (ltW hxb).
Qed.
