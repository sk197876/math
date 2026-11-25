(** Federer (1969), 4.1.2, p. 347: the
    actual smoothed test functions converge in the
    original D topology. One compact support step
    and the exact E seminorm estimates prove
    convergence in the literal final topology. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import Hom ModuleQuotient RealNormUP NormMetric CompleteMetricUP VectorDaniellHypotheses
  GrassmannAbbreviations EuclideanInnerProduct InnerNorm HilbertFormCompactness ContinuousMultilinearSealed
  LinearSubspaceRepresentationUP SmoothCompactSet SmoothFunctionSpaceUP SmoothFunctionSupport SmoothFunctionDerivativesUP
  SmoothFunctionTopology SmoothTestSpaces SmoothTestTopology SmoothingKernelUP SmoothingDilationUP
  SmoothSmoothingFamilyUP SmoothSmoothingSupport SmoothSmoothingConvergence
  SmoothSupportedPositiveLimit TestSmoothingFamilyUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section TestSmoothingConvergence.
Variable R:realType.
Variable n:nat.
Local Notation X := (R_n R n).
Local Notation N := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hN := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Variable Y:lmodType R.
Variable NY:Y->R.
Hypothesis hNY:is_real_norm NY.
Hypothesis hY:is_complete_metric_space (real_norm_metric_space hNY).
Hypothesis hSep:is_separable_normed_space hNY.
Variable E:lmodType R.
Variable ev:E->X->Y.
Hypothesis hE:is_smooth_function_space hN hNY (fun _=>True) ev.
Local Notation Z := (fun j=>@ContinuousMultilinear.space R j X Y N NY hN hNY).
Variable D:forall j,X->Hom E (Z j).
Hypothesis hD:@is_smooth_function_derivatives R X Y N NY hN hNY (fun _=>True) E ev D.
Local Notation DT := (smooth_test_space hE).
Local Notation inc := (smooth_test_inclusion hE).
Local Notation support := (@smooth_function_support R X Y N hN (fun _=>True) E ev).
Local Notation SO := (smooth_test_opens hE hD).
Local Notation nu := (smooth_function_derivative_seminorm hD).
Variable phi:X->R.
Hypothesis hPhi:is_smoothing_kernel phi.
Variable family:R->X->R.
Hypothesis hFamily:is_smoothing_dilation phi family.
Variable P:R->Hom E E.
Hypothesis hP:is_smooth_smoothing_family hNY ev family P.
Variable Q:R->Hom DT DT.
Hypothesis hQ:@is_test_smoothing_family R X Y N NY hN hNY (fun _=>True) E ev hE P Q.

(** Source for [test_smoothing_neighbourhood_limit]: the original
    Phi_epsilon*f tends to f in D(R^n,Y),
    Federer 4.1.2, p. 347, with
    its literal final topology and one common
    compact support. No joint vector continuity is assumed. *)
Theorem test_smoothing_neighbourhood_limit f:
  forall A,SO A ->A f ->exists d:R,0<d /\
    forall e:R,0<e ->e<d ->A (Q e f).
Proof.
have [K hK]:=subspace_representation_member (smooth_test_space_laws hE) f.
have [C [hKC hC]]:=@smooth_smoothing_support_bound R n Y NY hNY E ev hE
  phi hPhi family hFamily P hP K 1 ler01.
have hBase:support (inc f) `<=` smooth_compact_carrier C.
  move=>x hx; exact:(hKC x (hK x hx)).
have hFamilySupport e:0<e ->e<1 ->support (inc (Q e f)) `<=` smooth_compact_carrier C.
  move=>he hSmall; rewrite (@hQ e he f).
  exact:(@hC e he (ltW hSmall) (inc f) hK).
apply:(@smooth_supported_positive_limit R X Y N NY hN hNY (fun _=>True)
  E ev hE D hD (fun e=>Q e f) f C 1 ltr01 hBase hFamilySupport).
move=>L i eta hEta.
have [d [hd hUniform]]:=@smooth_smoothing_seminorm_uniform R n Y NY hNY hY hSep E ev hE D hD
  phi hPhi family hFamily P hP (inc f) L i (nu L i)
  (smooth_function_derivative_seminorm_laws hD L i) eta hEta.
exists d; split=>// e he hSmall.
rewrite (@hQ e he f); exact:(hUniform e he hSmall).
Qed.
End TestSmoothingConvergence.
