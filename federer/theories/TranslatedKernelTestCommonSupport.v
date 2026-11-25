(** Federer (1969), 4.1.2, pp. 347-348:
    kernel tests with nearby centres have one common
    compact support, independently of the vector coefficient.
    This permits one original finite-order distribution bound. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals topology lra.
From Federer Require Import Hom RealNormUP NormMetric GrassmannAbbreviations FiniteCoordinates
  EuclideanInnerProduct InnerNorm HilbertFormCompactness FiniteNormEquivalence
  SmoothCompactSet SmoothFunctionSpaceUP SmoothFunctionSupport SmoothTestSpaces SmoothTestEvaluation TranslatedKernelTestUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [translated_kernel_test_common_support]: the
    common compact support needed for the continuous dual-valued
    density and interchange in Federer 4.1.2, pp. 347-348.
    The centre may move through a whole norm ball. *)
Theorem translated_kernel_test_common_support (R:realType) n (Y:lmodType R)
    (NY:Y->R) (hNY:is_real_norm NY) (E:lmodType R) (ev:E->R_n R n->Y)
    (hE:is_smooth_function_space (inner_norm_real_norm (@euclidean_inner_productP R n)) hNY (fun _=>True) ev)
    (psi:R_n R n->R) r (B:R_n R n->Hom Y (smooth_test_space hE)):
  (forall x,r<inner_norm (@euclidean_inner_productP R n) x ->psi x=0) ->
  @is_translated_kernel_tests R (R_n R n) Y
    (inner_norm (@euclidean_inner_productP R n)) NY
    (inner_norm_real_norm (@euclidean_inner_productP R n)) hNY E ev hE psi B ->
  forall z,exists C:smooth_compact_set
      (inner_norm_real_norm (@euclidean_inner_productP R n)) (fun _=>True),
    forall h,inner_norm (@euclidean_inner_productP R n) h<=1 ->forall y,
      @smooth_function_support R (R_n R n) Y (inner_norm (@euclidean_inner_productP R n))
        (inner_norm_real_norm (@euclidean_inner_productP R n)) (fun _=>True) E ev
        (smooth_test_inclusion hE (B (z+h) y)) `<=` smooth_compact_carrier C.
Proof.
move=>hOff hB z.
pose X:=R_n R n.
pose N:=inner_norm (@euclidean_inner_productP R n).
pose hN:=inner_norm_real_norm (@euclidean_inner_productP R n).
pose C:=@Build_smooth_compact_set R X N hN (fun _=>True) [set x|N (x-z)<=r+1]
  (fun _ _=>Logic.I)
  (@finite_norm_closed_ball_compact R X n (@coordinate_basis R n) (@coordinate_basisP R n) N hN z (r+1)).
exists C=>h hh y; apply:(smooth_function_compact_support_iff hE C _).2=>x hx.
change (smooth_test_value hE (B (z+h) y) x=0); rewrite hB.
have hLarge:r+1<N (x-z) by rewrite ltNge; apply/negP=>hSmall; apply:hx.
have hTriangle:=real_seminorm_triangle hN.1 (x-(z+h)) h.
have hId:(x-(z+h))+h=x-z by rewrite opprD addrA subrK.
rewrite hId in hTriangle.
change (is_true (N (x-z)<=N (x-(z+h))+N h)) in hTriangle.
change (is_true (N h<=1)) in hh.
have hRadius:r<N (x-(z+h)) by nra.
by rewrite (@hOff (x-(z+h)) hRadius) scale0r.
Qed.
