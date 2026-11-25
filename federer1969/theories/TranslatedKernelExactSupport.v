(** Federer (1969), 4.1.4, pp. 348–349: the translated
    radius-e kernel test is supported in the actual closed
    radius-e ball. This gives its support inside A at each
    original inward point. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric GrassmannAbbreviations FiniteCoordinates
  EuclideanInnerProduct InnerNorm HilbertFormCompactness FiniteNormEquivalence
  SmoothCompactSet SmoothFunctionSpaceUP SmoothFunctionSupport SmoothTestSpaces SmoothTestEvaluation
  TranslatedKernelTestUP InnerParallelFamilyUP InnerParallelFamilyLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section TranslatedKernelExactSupport.
Variable R:realType.
Variable n:nat.
Local Notation X := (R_n R n).
Local Notation N := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hN := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Variable Y:lmodType R.
Variable NY:Y->R.
Hypothesis hNY:is_real_norm NY.
Variable E:lmodType R.
Variable ev:E->X->Y.
Hypothesis hE:is_smooth_function_space hN hNY (fun _=>True) ev.
Local Notation DT := (smooth_test_space hE).
Variable psi:X->R.
Variable r:R.
Hypothesis hOff:forall x,r<N x ->psi x=0.
Variable B:X->Hom Y DT.
Hypothesis hB:@is_translated_kernel_tests R X Y N NY hN hNY E ev hE psi B.

(** Source for [translated_kernel_test_exact_support]: the
    support inclusion for Phi_e(x-z)y needed for D_j g_e=0
    in Federer 4.1.4, p. 349. It includes zero vectors and
    dimension zero, with the actual closed ball. *)
Lemma translated_kernel_test_exact_support z y:
  @smooth_function_support R X Y N hN (fun _=>True) DT (smooth_test_value hE) (B z y)
    `<=` [set x|N (x-z)<=r].
Proof.
pose K:=@Build_smooth_compact_set R X N hN (fun _=>True)
  [set x|N (x-z)<=r] (fun _ _=>Logic.I)
  (@finite_norm_closed_ball_compact R X n (@coordinate_basis R n) (@coordinate_basisP R n) N hN z r).
change (@smooth_function_support R X Y N hN (fun _=>True) E ev
  (smooth_test_inclusion hE (B z y)) `<=` smooth_compact_carrier K).
apply:(smooth_function_compact_support_iff hE K _).2=>x hx.
change (smooth_test_value hE (B z y) x=0).
rewrite hB (@hOff (x-z)); first exact:scale0r.
rewrite ltNge; apply/negP=>hNear; apply:hx; exact hNear.
Qed.

(** Source for [translated_kernel_test_inward_support]: at an
    original inward point z the kernel test is supported in A,
    the locality inference in Federer 4.1.4, p. 349. *)
Theorem translated_kernel_test_inward_support (A:set X) (O:R->set X)
    (hO:is_inner_parallel_family N A O):0<r ->forall z,O r z ->forall y,
  @smooth_function_support R X Y N hN (fun _=>True) DT (smooth_test_value hE) (B z y) `<=` A.
Proof.
move=>hr z hz y x hx.
exact:(@inner_parallel_closed_ball_inside R X N A O hO r hr z hz x
  (@translated_kernel_test_exact_support z y x hx)).
Qed.
End TranslatedKernelExactSupport.
