(** Federer (1969), 4.1.1, pp. 344–345: multiplication
    by a fixed smooth scalar is bounded on every compact
    derivative seminorm. The proof reuses the scalar-vector
    Leibniz estimate of 3.1.14, p. 226, with the same K
    and the same derivative order as the original seminorm. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormRegularity
  ContinuousMultilinearUP ContinuousMultilinearSealed ContinuousMultilinearNorm
  NormHigherDifferentialUP NormHigherDifferentialLocal NormCompactFunctionBound
  ScalarVectorLeibnizBound SmoothCompactSet SmoothFunctionSpaceUP
  SmoothFunctionDerivativesUP SmoothDerivativeSeminormUP SmoothMultiplierUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section MultiplierSeminormBound.
Variable R:realType.
Variables X Y:lmodType R.
Variables (NX:X->R) (NY:Y->R).
Hypothesis hNX:is_real_norm NX.
Hypothesis hNY:is_real_norm NY.
Variable U:set X.
Hypothesis hU:forall x,U x ->norm_domain_interior NX U x.
Variable E:lmodType R.
Variable ev:E->X->Y.
Hypothesis hE:is_smooth_function_space hNX hNY U ev.
Local Notation Z := (fun k=>@ContinuousMultilinear.space R k X Y NX NY hNX hNY).
Local Notation ez := (fun k=>@ContinuousMultilinear.evaluation R k X Y NX NY hNX hNY).
Local Notation ZN := (fun k=>@ContinuousMultilinear.norm R k X Y NX NY hNX hNY).
Local Notation hZ := (fun k=>@ContinuousMultilinear.laws R k X Y NX NY hNX hNY).
Local Notation NS := (fun t:R^o=>`|t|).
Local Notation hNS := (@scalar_absolute_value_norm R).
Local Notation W := (fun k=>@ContinuousMultilinear.space R k X R^o NX NS hNX hNS).
Local Notation ew := (fun k=>@ContinuousMultilinear.evaluation R k X R^o NX NS hNX hNS).
Local Notation WN := (fun k=>@ContinuousMultilinear.norm R k X R^o NX NS hNX hNS).
Local Notation hW := (fun k=>@ContinuousMultilinear.laws R k X R^o NX NS hNX hNS).
Variable D:forall k,X->Hom E (Z k).
Hypothesis hD:@is_smooth_function_derivatives R X Y NX NY hNX hNY U E ev D.
Variable u:X->R.
Hypothesis hu:norm_class_all_orders hNX hNS U u.
Variable P:Hom E E.
Hypothesis hP:is_smooth_multiplier U ev u P.

(** Source for [smooth_multiplier_seminorm_bound]: nu^i_K of
    u phi is at most C nu^i_K(phi) for one nonnegative C
    depending only on u, K and i, supporting the multiplication
    operators in Federer 4.1.1, pp. 344–345. No finite target
    dimension or target completeness is assumed. *)
Theorem smooth_multiplier_seminorm_bound (K:smooth_compact_set hNX U)
    i (p:E->R):
  @is_smooth_derivative_seminorm R X Y NX NY hNX hNY U E D K i p ->
  exists C:R,0<=C /\ forall f,p (P f)<=C * p f.
Proof.
move=>hp.
pose Du k:=projT1 (cid (hu k).2).
have hDu k:=projT2 (cid (hu k).2).
have hChoice (j:'I_i.+1):exists M:R,0<M /\ forall x,
    smooth_compact_carrier K x -> @WN j (Du j x)<=M.
  exact (@norm_class_zero_compact_bounded R X (W j) NX (@WN j) hNX
    (continuous_multilinear_norm_is_norm hNS (hW j)) U (smooth_compact_carrier K)
    (Du j) (smooth_compact_is_compact K) (smooth_compact_in_domain K) (hDu j).2).
have [B hB]:=choice hChoice.
pose M:=\sum_(j:'I_i.+1) B j.
have hM:0<=M by apply:sumr_ge0=>j _; exact:ltW (hB j).1.
have hBM (j:'I_i.+1):B j<=M.
  rewrite /M (bigD1 j) //= lerDl.
  apply:sumr_ge0=>l _; exact:ltW (hB l).1.
pose Cj j:=\sum_(l<j.+1) ('C(j,l))%:R * M.
have hCj j:0<=Cj j.
  apply:sumr_ge0=>l _; exact:mulr_ge0 (ler0n _ _) hM.
pose C:=\sum_(j:'I_i.+1) Cj j.
have hC:0<=C by apply:sumr_ge0=>j _; exact:hCj.
exists C; split=>// f.
apply:(@smooth_derivative_seminorm_least R X Y NX NY hNX hNY U E D K i p hp (P f)
  (C * p f) (mulr_ge0 hC (smooth_derivative_seminorm_nonnegative hp f)))=>j hj x hx.
have hux:=smooth_compact_in_domain K x hx.
have hScalar l (hl:(l<=j)%N):@WN l (Du l x)<=M.
  have hli:=leq_trans hl hj.
  have hlt:(l<i.+1)%N by rewrite ltnS.
  exact:le_trans ((hB (Ordinal hlt)).2 x hx) (hBM (Ordinal hlt)).
have hVector l (hl:(l<=j)%N):@ZN l (@D l x f)<=p f.
  exact:(smooth_derivative_seminorm_bound hp f (leq_trans hl hj) hx).
have hEq y (hy:U y) (_:U y):ev (P f) y=u y*:ev f y:=hP f hy.
have hLocal:=@norm_higher_differential_local_agreement R X Y NX NY hNX hNY
  Z ez ZN hZ j U U U (ev (P f)) (fun y=>u y*:ev f y) hU
  (fun y hy=>iff_refl (U y)) hEq x hux (@D j x (P f)).
have hProduct:=hLocal.1 (@smooth_derivative_exact R X Y NX NY hNX hNY U E ev D hD
  j (P f) x hux).
have hEst:=@norm_scalar_vector_higher_differential_bound R X Y NX NY hNX hNY
  Z ez ZN hZ W ew WN hW U u (ev f) j x
  (fun l=>Du l x) (fun l=>@D l x f) (fun _=>M) (fun _=>p f) j (@D j x (P f))
  hux (hu j) (smooth_function_evaluation_smooth hE f j)
  (fun l hl=>(hDu l).1 x hux)
  (fun l hl=>@smooth_derivative_exact R X Y NX NY hNX hNY U E ev D hD l f x hux)
  hScalar hVector (leqnn j) hProduct.
have hSum: \sum_(l<j.+1) ('C(j,l))%:R*(M * p f)=Cj j * p f.
  rewrite /Cj [RHS]big_distrl.
  by apply:eq_bigr=>l _; rewrite mulrA.
rewrite hSum in hEst.
have hjlt:(j<i.+1)%N by rewrite ltnS.
pose a:'I_i.+1:=Ordinal hjlt.
have hJC:Cj j<=C.
  rewrite /C (bigD1 a) //= lerDl.
  apply:sumr_ge0=>l _; exact:hCj.
exact:le_trans hEst (ler_wpM2r (smooth_derivative_seminorm_nonnegative hp f) hJC).
Qed.
End MultiplierSeminormBound.
