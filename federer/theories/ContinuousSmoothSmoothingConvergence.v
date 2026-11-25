(** Federer (1969), 4.1.3, p. 348, using 4.1.2, p. 347: the
    actual smoothing family converges in every original
    derivative seminorm and hence in E(R^n,Y).
    The proof uses only the exact seminorm laws
    and their previously proved neighbourhood base. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology lra.
From Federer Require Import Hom RealNormUP NormMetric CompleteMetricUP VectorDaniellHypotheses
  GrassmannAbbreviations EuclideanInnerProduct InnerNorm HilbertFormCompactness
  ContinuousMultilinearSealed SmoothCompactSet SmoothFunctionSpaceUP SmoothFunctionDerivativesUP
  SmoothDerivativeSeminormUP SmoothFunctionTopology FiniteCommonRadius SmoothingKernelUP SmoothingDilationUP
  SmoothSmoothingFamilyUP ContinuousSmoothDerivativeUniform.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section ContinuousSmoothSmoothingConvergence.
Variable R:realType.
Variable n:nat.
Local Notation X := (R_n R n).
Local Notation N := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hN := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Variable Y:lmodType R.
Variable NY:Y->R.
Hypothesis hNY:is_real_norm NY.
Hypothesis hY:is_complete_metric_space (real_norm_metric_space hNY).
Variable E:lmodType R.
Variable ev:E->X->Y.
Hypothesis hE:is_smooth_function_space hN hNY (fun _=>True) ev.
Local Notation Z := (fun j=>@ContinuousMultilinear.space R j X Y N NY hN hNY).
Local Notation ZN := (fun j=>@ContinuousMultilinear.norm R j X Y N NY hN hNY).
Variable D:forall j,X->Hom E (Z j).
Hypothesis hD:@is_smooth_function_derivatives R X Y N NY hN hNY (fun _=>True) E ev D.
Variable phi:X->R.
Hypothesis hPhi:is_smoothing_kernel phi.
Variable family:R->X->R.
Hypothesis hFamily:is_smoothing_dilation phi family.
Variable P:R->Hom E E.
Hypothesis hP:is_smooth_smoothing_family hNY ev family P.

(** Source for [continuous_smooth_seminorm_uniform]: every original
    nu_K^i(P_epsilon f-f) tends to zero,
    the exact seminorm meaning of the convergence
    assertion in Federer 4.1.2, p. 347. *)
Theorem continuous_smooth_seminorm_uniform f
    (K:smooth_compact_set hN (fun _=>True)) i (p:E->R):
  @is_smooth_derivative_seminorm R X Y N NY hN hNY (fun _=>True) E D K i p ->
  forall eta:R,0<eta ->exists d:R,0<d /\ forall e:R,0<e ->e<d ->
    p (P e f-f)<eta.
Proof.
move=>hp eta hEta.
have hEta2:0<eta/2 by rewrite divr_gt0 // ltr0n.
have hEach (j:'I_i.+1):exists d:R,0<d /\ forall e:R,e<d ->0<e ->
    forall a,smooth_compact_carrier K a ->@ZN (val j) (@D (val j) a (P e f-f))<eta/2.
  have [d [hd hUniform]]:=@continuous_smooth_derivative_uniform R n Y NY hNY hY E ev hE D hD
    phi hPhi family hFamily P hP (val j) f K (eta/2) hEta2.
  exists d; split=>// e hSmall he a ha; exact:(hUniform e he hSmall a ha).
have [d [hd hUniform]]:=@finite_common_radius R (Finite.clone 'I_i.+1 _) R (fun e=>e)
  (fun j e=>0<e ->forall a,smooth_compact_carrier K a ->@ZN (val j) (@D (val j) a (P e f-f))<eta/2) hEach.
exists d; split=>// e he hSmall.
have hBound:p (P e f-f)<=eta/2.
  apply:(@smooth_derivative_seminorm_least R X Y N NY hN hNY (fun _=>True) E D K i p hp
    (P e f-f) (eta/2) (ltW hEta2)).
  move=>j hj a ha.
  have hji:(j<i.+1)%N by rewrite ltnS.
  pose jj:'I_i.+1:=Ordinal hji.
  exact:ltW (hUniform jj e hSmall he a ha).
apply:le_lt_trans hBound _; lra.
Qed.

(** Source for [continuous_smooth_neighbourhood_limit]: the actual
    positive-scale family P_epsilon f tends to f in
    Federer's original E topology, 4.1.2, p. 347.
    Every original open neighbourhood eventually contains it. *)
Theorem continuous_smooth_neighbourhood_limit f A:
  smooth_function_opens hD A ->A f ->
  exists d:R,0<d /\ forall e:R,0<e ->e<d ->A (P e f).
Proof.
move=>hA hf.
have [[i K] [r [hr hBall]]]:=((smooth_function_topology_laws hD).2 A).1 hA f hf.
have [d [hd hUniform]]:=@continuous_smooth_seminorm_uniform f K i
  (smooth_function_derivative_seminorm hD K i) (smooth_function_derivative_seminorm_laws hD K i) r hr.
exists d; split=>// e he hSmall.
apply:hBall; exact:(hUniform e he hSmall).
Qed.
End ContinuousSmoothSmoothingConvergence.
