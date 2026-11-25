(** Federer (1969), 4.1.2, p. 347: smoothing
    sends compactly supported smooth functions to such
    functions. Every bounded range of positive scales
    has one compact support bound, in the original
    support definition and smooth-space representation. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP NormMetric GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerNorm HilbertFormCompactness
  SmoothCompactSet SmoothFunctionSpaceUP SmoothFunctionSupport SmoothCompactThickening CompactSmoothingSupport
  SmoothingKernelUP SmoothingDilationUP SmoothSmoothingFamilyUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section SmoothSmoothingSupport.
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
Local Notation support := (@smooth_function_support R X Y N hN (fun _=>True) E ev).
Variable phi:X->R.
Hypothesis hPhi:is_smoothing_kernel phi.
Variable family:R->X->R.
Hypothesis hFamily:is_smoothing_dilation phi family.
Variable P:R->Hom E E.
Hypothesis hP:is_smooth_smoothing_family hNY ev family P.

(** Source for [smooth_smoothing_support_bound]: the single
    compact support step for a fixed original
    source support and bounded positive scales,
    supporting Federer 4.1.2, p. 347. *)
Theorem smooth_smoothing_support_bound (K:smooth_compact_set hN (fun _=>True)) r:
  0<=r ->exists C:smooth_compact_set hN (fun _=>True),
    (smooth_compact_carrier K `<=` smooth_compact_carrier C) /\
    forall e:R,0<e ->e<=r ->forall f:E,
      support f `<=` smooth_compact_carrier K ->
      support (P e f) `<=` smooth_compact_carrier C.
Proof.
move=>hr.
have [C [hKC hThick]]:=@smooth_compact_thickening R X N hN n
  (@coordinate_basis R n) (@coordinate_basisP R n) K r hr.
exists C; split=>// e he her f hf.
apply:(smooth_function_compact_support_iff hE C (P e f)).2.
exact:(@compact_smoothing_support_bound R n Y NY hNY phi hPhi family hFamily
  (smooth_compact_carrier K) (smooth_compact_carrier C) r e (ev f) (ev (P e f))
  hThick he her ((smooth_function_compact_support_iff hE K f).1 hf) (@hP e he f)).
Qed.
End SmoothSmoothingSupport.
