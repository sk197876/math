(** Federer (1969), 4.1.7, pp. 355–356: the
    fixed coefficient operations are continuous for
    the original derivative-seminorm topologies of
    4.1.1, pp. 343–344. This file proves the needed
    finite bound from actual higher derivatives. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP ContinuousMultilinearSealed
  SmoothCompactSet SmoothFunctionSpaceUP SmoothFunctionDerivativesUP SmoothDerivativeSeminormUP
  SmoothTargetOperatorUP SmoothTargetOperatorDerivatives.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section SmoothTargetSeminormBound.
Variable R:realType.
Variables X Y Z:lmodType R.
Variables (NX:X->R) (NY:Y->R) (NZ:Z->R).
Hypotheses (hNX:is_real_norm NX) (hNY:is_real_norm NY) (hNZ:is_real_norm NZ).
Variable U:X->Prop.
Variables E F:lmodType R.
Variables (ev:E->X->Y) (fv:F->X->Z).
Hypothesis hE:is_smooth_function_space hNX hNY U ev.
Hypothesis hF:is_smooth_function_space hNX hNZ U fv.
Local Notation Pjet := (fun j=>@ContinuousMultilinear.space R j X Y NX NY hNX hNY).
Local Notation Qjet := (fun j=>@ContinuousMultilinear.space R j X Z NX NZ hNX hNZ).
Variable D:forall j,X->Hom E (Pjet j).
Variable G:forall j,X->Hom F (Qjet j).
Hypothesis hD:@is_smooth_function_derivatives R X Y NX NY hNX hNY U E ev D.
Hypothesis hG:@is_smooth_function_derivatives R X Z NX NZ hNX hNZ U F fv G.
Variable L:Hom Y Z.
Hypothesis hL:norm_bounded_linear NY NZ L.
Variable P:Hom E F.
Hypothesis hP:is_smooth_target_operator U ev fv L P.

(** Source for [smooth_target_operator_seminorm_bound]:
    each target derivative seminorm is bounded by a
    finite multiple of the same-order source seminorm,
    supporting Federer 4.1.7, pp. 355–356. *)
Theorem smooth_target_operator_seminorm_bound (K:smooth_compact_set hNX U)
    i (p:E->R) (q:F->R):
  @is_smooth_derivative_seminorm R X Y NX NY hNX hNY U E D K i p ->
  @is_smooth_derivative_seminorm R X Z NX NZ hNX hNZ U F G K i q ->
  exists C:R,0<=C /\ forall f,q (P f)<=C * p f.
Proof.
move=>hp hq.
have [J [hJ [hJb hDer]]]:=@smooth_target_derivative_family_exists R X Y Z NX NY NZ
  hNX hNY hNZ U E F ev fv hE hF D G hD hG L hL P hP.
have hChoice (j:'I_i.+1):exists C:R,0<=C /\ forall z,
    @ContinuousMultilinear.norm R j X Z NX NZ hNX hNZ (J j z)<=
      C * @ContinuousMultilinear.norm R j X Y NX NY hNX hNY z.
  exact:hJb.
have [M hM]:=choice hChoice.
pose C:=\sum_(j:'I_i.+1) M j.
have hC:0<=C by apply:sumr_ge0=>j _; exact:(hM j).1.
exists C; split=>// f.
apply:(@smooth_derivative_seminorm_least R X Z NX NZ hNX hNZ U F G K i q hq (P f)
  (C * p f) (mulr_ge0 hC (smooth_derivative_seminorm_nonnegative hp f)))=>j hj x hx.
rewrite (@hDer j f x (smooth_compact_in_domain K x hx)).
have hj':(j<i.+1)%N by rewrite ltnS.
pose c:'I_i.+1:=Ordinal hj'.
have hStep:=le_trans ((hM c).2 (@D j x f))
  (ler_wpM2l (hM c).1 (smooth_derivative_seminorm_bound hp f hj hx)).
have hMC:M c<=C.
  rewrite /C (bigD1 c) //= lerDl.
  apply:sumr_ge0=>d _; exact:(hM d).1.
exact:(le_trans hStep (ler_wpM2r (smooth_derivative_seminorm_nonnegative hp f) hMC)).
Qed.
End SmoothTargetSeminormBound.
