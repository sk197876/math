(** Federer (1969), 4.1.7, p. 356: the
    original first-order operators are controlled by
    the next derivative seminorm on the same compact
    set, as in 4.1.1, pp. 343–346. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP ContinuousMultilinearSealed
  SmoothCompactSet SmoothFunctionSpaceUP SmoothFunctionDerivativesUP SmoothDerivativeSeminormUP
  SmoothFirstOrderUP SmoothFirstOrderHigherBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section SmoothFirstOrderSeminormBound.
Variable R:realType.
Variables X Y Z:lmodType R.
Variables (NX:X->R) (NY:Y->R) (NZ:Z->R).
Hypotheses (hNX:is_real_norm NX) (hNY:is_real_norm NY) (hNZ:is_real_norm NZ).
Variable U:X->Prop.
Variables E F:lmodType R.
Variables (ev:E->X->Y) (fv:F->X->Z).
Hypothesis hF:is_smooth_function_space hNX hNZ U fv.
Local Notation J := (fun j=>@ContinuousMultilinear.space R j X Y NX NY hNX hNY).
Local Notation Q := (fun j=>@ContinuousMultilinear.space R j X Z NX NZ hNX hNZ).
Variable D:forall j,X->Hom E (J j).
Variable G:forall j,X->Hom F (Q j).
Hypothesis hD:@is_smooth_function_derivatives R X Y NX NY hNX hNY U E ev D.
Hypothesis hG:@is_smooth_function_derivatives R X Z NX NZ hNX hNZ U F fv G.
Variable M:Hom (J 1%N) Z.
Hypothesis hM:norm_bounded_linear
  (@ContinuousMultilinear.norm R 1 X Y NX NY hNX hNY) NZ M.
Variable P:Hom E F.
Hypothesis hP:is_smooth_first_order_operator U fv D M P.

(** Source for [smooth_first_order_seminorm_bound]: the
    original nu^i_K of the first-order image is
    bounded by a finite multiple of nu^(i+1)_K,
    supporting Federer 4.1.7, p. 356. *)
Theorem smooth_first_order_seminorm_bound (K:smooth_compact_set hNX U)
    i (p:E->R) (q:F->R):
  @is_smooth_derivative_seminorm R X Y NX NY hNX hNY U E D K i.+1 p ->
  @is_smooth_derivative_seminorm R X Z NX NZ hNX hNZ U F G K i q ->
  exists C:R,0<=C /\forall f,q (P f)<=C * p f.
Proof.
move=>hp hq.
have hChoice (j:'I_i.+1):exists C:R,0<=C /\forall f x,U x->
    @ContinuousMultilinear.norm R j X Z NX NZ hNX hNZ (@G j x (P f))<=
      C * @ContinuousMultilinear.norm R j.+1 X Y NX NY hNX hNY (@D j.+1 x f).
  exact:(@smooth_first_order_higher_bound R X Y Z NX NY NZ hNX hNY hNZ
    U E F ev fv hF D G hD hG M hM P hP j).
have [N hN]:=choice hChoice.
pose C:=\sum_(j:'I_i.+1) N j.
have hC:0<=C by apply:sumr_ge0=>j _; exact:(hN j).1.
exists C; split=>// f.
apply:(@smooth_derivative_seminorm_least R X Z NX NZ hNX hNZ U F G K i q hq (P f)
  (C * p f) (mulr_ge0 hC (smooth_derivative_seminorm_nonnegative hp f)))=>j hj x hx.
have hj':(j<i.+1)%N by rewrite ltnS.
pose c:'I_i.+1:=Ordinal hj'.
have hNext:(j.+1<=i.+1)%N by [].
have hStep:=le_trans ((hN c).2 f x (smooth_compact_in_domain K x hx))
  (ler_wpM2l (hN c).1 (smooth_derivative_seminorm_bound hp f hNext hx)).
have hNC:N c<=C.
  rewrite /C (bigD1 c) //= lerDl.
  apply:sumr_ge0=>d _; exact:(hN d).1.
exact:(le_trans hStep (ler_wpM2r (smooth_derivative_seminorm_nonnegative hp f) hNC)).
Qed.
End SmoothFirstOrderSeminormBound.
