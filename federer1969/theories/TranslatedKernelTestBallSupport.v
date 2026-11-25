(** Federer (1969), 4.1.2, p. 347,
    used in 4.1.18, pp. 375–376: each
    original translated kernel test is supported in
    the literal closed kernel ball, uniformly over
    every coefficient. Reuse the original compact support
    criterion of 4.1.1, p. 344. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerNorm
  HilbertFormCompactness FiniteNormEquivalence SmoothCompactSet
  SmoothFunctionSpaceUP SmoothFunctionSupport SmoothTestSpaces SmoothTestEvaluation
  TranslatedKernelTestUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [translated_kernel_test_ball_support]:
    the exact support of the translated test lies
    in the closed radius-r ball about its centre,
    supporting the smoothing density carrier in Federer
    4.1.18, pp. 375–376. No symmetry is
    imposed on the original kernel. *)
Theorem translated_kernel_test_ball_support (R:realType) n (Y:lmodType R)
    (NY:Y->R) (hNY:is_real_norm NY) (E:lmodType R) (ev:E->R_n R n->Y)
    (hE:is_smooth_function_space (inner_norm_real_norm (@euclidean_inner_productP R n))
      hNY (fun _=>True) ev)
    (psi:R_n R n->R) r (B:R_n R n->Hom Y (smooth_test_space hE)):
  (forall x,r<inner_norm (@euclidean_inner_productP R n) x->psi x=0)->
  @is_translated_kernel_tests R (R_n R n) Y
    (inner_norm (@euclidean_inner_productP R n)) NY
    (inner_norm_real_norm (@euclidean_inner_productP R n)) hNY E ev hE psi B->
  forall z y,@smooth_function_support R (R_n R n) Y
    (inner_norm (@euclidean_inner_productP R n))
    (inner_norm_real_norm (@euclidean_inner_productP R n)) (fun _=>True)
    E ev (smooth_test_inclusion hE (B z y)) `<=`
    [set x|inner_norm (@euclidean_inner_productP R n) (x-z)<=r].
Proof.
move=>hOff hB z y.
pose X:=R_n R n.
pose N:=inner_norm (@euclidean_inner_productP R n).
pose hN:=inner_norm_real_norm (@euclidean_inner_productP R n).
pose K:=@Build_smooth_compact_set R X N hN (fun _=>True)
  [set x|N (x-z)<=r] (fun _ _=>Logic.I)
  (@finite_norm_closed_ball_compact R X n (@coordinate_basis R n)
    (@coordinate_basisP R n) N hN z r).
apply:(smooth_function_compact_support_iff hE K _).2=>x hx.
change (smooth_test_value hE (B z y) x=0).
have hRadius:r<N (x-z) by rewrite ltNge;apply/negP=>h;apply:hx.
by rewrite hB (hOff (x-z) hRadius) scale0r.
Qed.
