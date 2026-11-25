(** Federer (1969), 4.1.1, p. 346: differentiation is
    continuous in the derivative-seminorm topology. Finitely
    many existing higher-derivative bounds supply one constant
    for every prescribed derivative order and compact set. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP ContinuousMultilinearSealed
  SmoothCompactSet SmoothFunctionDerivativesUP SmoothDerivativeSeminormUP
  SmoothDirectionalDerivativeUP SmoothDirectionalHigherBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Section DirectionalSeminormBound.
Variable R:realType.
Variables X Y:lmodType R.
Variables (NX:X->R) (NY:Y->R).
Hypothesis hNX:is_real_norm NX.
Hypothesis hNY:is_real_norm NY.
Variable U:set X.
Hypothesis hU:forall x,U x -> norm_domain_interior NX U x.
Variable E:lmodType R.
Variable ev:E->X->Y.
Local Notation Z := (fun k=>@ContinuousMultilinear.space R k X Y NX NY hNX hNY).
Local Notation ZN := (fun k=>@ContinuousMultilinear.norm R k X Y NX NY hNX hNY).
Variable D:forall k,X->Hom E (Z k).
Hypothesis hD:@is_smooth_function_derivatives R X Y NX NY hNX hNY U E ev D.
Variable v:X.
Variable P:Hom E E.
Hypothesis hP:@is_smooth_directional_derivative R X Y NX NY hNX hNY U E ev D v P.

(** Source for [smooth_directional_seminorm_bound]: nu^i_K of
    the directional derivative is bounded by a finite multiple
    of nu^(i+1)_K of the original function, supporting continuity
    of D_j and its transpose in Federer 4.1.1, p. 346. *)
Theorem smooth_directional_seminorm_bound (K:smooth_compact_set hNX U)
    i (p q:E->R):
  @is_smooth_derivative_seminorm R X Y NX NY hNX hNY U E D K i p ->
  @is_smooth_derivative_seminorm R X Y NX NY hNX hNY U E D K i.+1 q ->
  exists C:R,0<=C /\ forall f,p (P f)<=C * q f.
Proof.
move=>hp hq.
have hChoice (j:'I_i.+1):exists C:R,0<=C /\ forall f x,U x ->
    @ZN j (@D j x (P f))<=C * @ZN j.+1 (@D j.+1 x f).
  exact:(smooth_directional_higher_derivative_bound hU hD hP j).
have [M hM]:=choice hChoice.
pose C:=\sum_(j:'I_i.+1) M j.
have hC:0<=C by apply:sumr_ge0=>j _; exact:(hM j).1.
exists C; split=>// f.
apply:(@smooth_derivative_seminorm_least R X Y NX NY hNX hNY U E D K i p hp (P f)
  (C * q f) (mulr_ge0 hC (smooth_derivative_seminorm_nonnegative hq f)))=>j hj x hx.
have hj':(j<i.+1)%N by rewrite ltnS.
pose a:'I_i.+1:=Ordinal hj'.
have hEst: @ZN j (@D j x (P f))<=M a * @ZN j.+1 (@D j.+1 x f):=
  (hM a).2 f x (smooth_compact_in_domain K x hx).
have hNext:(j.+1<=i.+1)%N by [].
have hNorm:=smooth_derivative_seminorm_bound hq f hNext hx.
have hFirst:=le_trans hEst (ler_wpM2l (hM a).1 hNorm).
have hMC:M a<=C.
  rewrite /C (bigD1 a) //= lerDl.
  apply:sumr_ge0=>b _; exact:(hM b).1.
exact:(le_trans hFirst (ler_wpM2r (smooth_derivative_seminorm_nonnegative hq f) hMC)).
Qed.
End DirectionalSeminormBound.
