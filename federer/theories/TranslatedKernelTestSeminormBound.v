(** Federer (1969), 4.1.2, p. 347: finite
    derivative seminorms of the translated kernel tests are
    bounded by a finite constant times the norm of y.
    This discharges continuity of their distribution evaluations. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals topology lra.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormRegularity
  GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerNorm HilbertFormCompactness
  FiniteNormEquivalence ContinuousMultilinearUP ContinuousMultilinearNorm ContinuousMultilinearSealed
  NormHigherDifferentialUP NormCompactSupportHigherBound SmoothCompactSet SmoothFunctionSpaceUP
  SmoothFunctionDerivativesUP SmoothDerivativeSeminormUP SmoothFunctionTopology SmoothTestSpaces SmoothTestEvaluation
  TranslatedKernelTestUP TranslatedKernelTestExistence ScalarVectorSmoothDerivativeBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section TranslatedKernelTestSeminormBound.
Variable R:realType.
Variable n:nat.
Local Notation X := (R_n R n).
Local Notation N := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hN := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation NS := (fun t:R^o=>`|t|).
Local Notation hNS := (@scalar_absolute_value_norm R).
Variable Y:lmodType R.
Variable NY:Y->R.
Hypothesis hNY:is_real_norm NY.
Variable E:lmodType R.
Variable ev:E->X->Y.
Hypothesis hE:is_smooth_function_space hN hNY (fun _=>True) ev.
Local Notation Z := (fun j=>@ContinuousMultilinear.space R j X Y N NY hN hNY).
Local Notation P := (fun j=>@ContinuousMultilinear.space R j X R^o N NS hN hNS).
Local Notation ep := (fun j=>@ContinuousMultilinear.evaluation R j X R^o N NS hN hNS).
Local Notation PN := (fun j=>@ContinuousMultilinear.norm R j X R^o N NS hN hNS).
Local Notation hP := (fun j=>@ContinuousMultilinear.laws R j X R^o N NS hN hNS).
Local Notation ZN := (fun j=>@ContinuousMultilinear.norm R j X Y N NY hN hNY).
Variable D:forall j,X->Hom E (Z j).
Hypothesis hD:@is_smooth_function_derivatives R X Y N NY hN hNY (fun _=>True) E ev D.
Variable psi:X->R.
Hypothesis hPsi:norm_class_all_orders hN hNS (fun _=>True) psi.
Variable r:R.
Hypothesis hOff:forall x,r<N x ->psi x=0.
Variable B:X->Hom Y (smooth_test_space hE).
Hypothesis hB:@is_translated_kernel_tests R X Y N NY hN hNY E ev hE psi B.

(** Source for [translated_kernel_test_seminorm_bound]: the
    continuous dependence on y of all finite kernel
    derivatives in Federer 4.1.2, p. 347.
    Every original seminorm is bounded; the target Y
    may have arbitrary dimension. *)
Theorem translated_kernel_test_seminorm_bound z i
    (K:smooth_compact_set hN (fun _=>True)):
  exists C:R,0<=C /\ forall y,
    smooth_function_derivative_seminorm hD K i (smooth_test_inclusion hE (B z y))<=C*NY y.
Proof.
pose F:=fun x=>psi (x-z).
pose A:set X:=[set x|N (x-z)<=r].
have hA:compact [set x:real_norm_metric_space hN|A x].
  exact:(@finite_norm_closed_ball_compact R X n (@coordinate_basis R n) (@coordinate_basisP R n) N hN z r).
have hZero x:~A x ->F x=0.
  move=>hx; apply:hOff; by rewrite ltNge; apply/negP.
have hF:=@translated_scalar_kernel_smooth R n psi hPsi z.
have hOne j:exists C:R,0<=C /\ forall y x,
    @ZN j (@D j x (smooth_test_inclusion hE (B z y)))<=C*NY y.
  have[G [M [hG [hM [hBound hGOff]]]]]:=@norm_compact_support_higher_differential_bound R X R^o
    N NS hN hNS P ep PN hP A F j hA hZero (hF j).
  exists M; split; first exact:ltW hM.
  move=>y x.
  have h:=@scalar_vector_smooth_derivative_bound R X Y N NY hN hNY E ev D hD
    F j G y (smooth_test_inclusion hE (B z y)) hG (fun t=>hB z y t) x.
  exact:(le_trans h (ler_wpM2r (real_seminorm_nonnegative hNY.1 y) (hBound x))).
have hThrough l:exists C:R,0<=C /\ forall j,(j<=l)%N ->forall y x,
    @ZN j (@D j x (smooth_test_inclusion hE (B z y)))<=C*NY y.
  elim:l=>[|l [C [hC hAll]]].
  - have[C [hC hBound]]:=hOne 0%N.
    exists C; split=>// j; rewrite leqn0=>/eqP ->; exact hBound.
  - have[C' [hC' hLast]]:=hOne l.+1.
    exists (C+C'); split; first exact:addr_ge0 hC hC'.
    move=>j hj y x.
    have[hEqual|hNotEqual]:=eqVneq j l.+1.
    + rewrite hEqual; apply:le_trans (hLast y x) _.
      apply:ler_wpM2r; first exact:real_seminorm_nonnegative hNY.1 y.
      by lra.
    + have hSmall:(j<=l)%N by move:hj; rewrite leq_eqVlt (negPf hNotEqual) /= ltnS.
      apply:le_trans (hAll j hSmall y x) _.
      apply:ler_wpM2r; first exact:real_seminorm_nonnegative hNY.1 y.
      by lra.
have[C [hC hAll]]:=hThrough i.
exists C; split=>// y.
apply:(smooth_derivative_seminorm_least (smooth_function_derivative_seminorm_laws hD K i)).
- exact:mulr_ge0 hC (real_seminorm_nonnegative hNY.1 y).
- move=>j hj x hx; exact:hAll j hj y x.
Qed.
End TranslatedKernelTestSeminormBound.
