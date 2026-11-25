(** Federer (1969), 4.1.5, p. 349: the compact
    continuous field w admits the original smooth
    convolutions Phi_e*w as tests for all sufficiently small
    positive e. Their supports have one compact bound in
    U and their convergence is uniform on the whole source.
    The proof reuses 4.1.2 and the compact interior margin. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP CompleteMetricUP NormClassOneUP NormRegularity
  GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerNorm HilbertFormCompactness
  SmoothCompactSet SmoothCompactInteriorThickening SmoothCompactDomainInclusion
  SmoothFunctionSpaceUP SmoothFunctionSupport SmoothTestSpaces SmoothTestEvaluation SmoothTestCompactRepresentation
  SmoothingKernelUP SmoothingDilationUP SmoothingDilationSmooth SmoothingDilationNonzeroRadius
  SmoothingConvolutionUP ContinuousCompactConvolution ContinuousSmoothingSmoothness
  ContinuousSmoothingLocallyUniform CompactSmoothingSupport SmoothClassOpenRestriction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CompactContinuousSmoothingTests.
Variable R:realType.
Variable n:nat.
Local Notation X := (R_n R n).
Local Notation N := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hN := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Variable Y:lmodType R.
Variable NY:Y->R.
Hypothesis hNY:is_real_norm NY.
Hypothesis hY:is_complete_metric_space (real_norm_metric_space hNY).
Variable U:set X.
Hypothesis hU:forall x,U x ->norm_domain_interior N U x.
Variable E:lmodType R.
Variable ev:E->X->Y.
Hypothesis hE:is_smooth_function_space hN hNY U ev.
Local Notation DT := (smooth_test_space hE).
Local Notation value := (smooth_test_value hE).
Local Notation support := (@smooth_function_support R X Y N hN U DT value).
Variable phi:X->R.
Hypothesis hPhi:is_smoothing_kernel phi.
Variable family:R->X->R.
Hypothesis hFamily:is_smoothing_dilation phi family.

(** Source for [compact_continuous_smoothing_tests]: actual
    compactly supported smooth convolutions and the uniform
    convergence used to define T(w) in Federer 4.1.5,
    p. 349. No separability of the whole dual is assumed,
    and the original arbitrary open domain is retained. *)
Theorem compact_continuous_smoothing_tests
    (K:smooth_compact_set hN U) (w:X->Y):
  norm_class_zero N NY (fun _=>True) w ->
  (forall x,~smooth_compact_carrier K x ->w x=0) ->
  exists r:R,0<r /\ exists C:smooth_compact_set hN U,exists P:R->DT,
    (forall e:R,0<e ->e<r ->
      is_smoothing_convolution hNY (family e) w (value (P e)) /\
      support (P e) `<=` smooth_compact_carrier C) /\
    (forall eta:R,0<eta ->exists d:R,0<d /\ d<=r /\
      forall e:R,0<e ->e<d ->forall x,NY (value (P e) x-w x)<eta).
Proof.
move=>hContinuous hOff.
have[r [hr [C [hKC hThick]]]]:=@smooth_compact_interior_thickening R X N hN n
  (@coordinate_basis R n) (@coordinate_basisP R n) U hU K.
have hGlobal e:exists g:X->Y,0<e ->is_smoothing_convolution hNY (family e) w g.
  case:(pselect (0<e))=>he.
  - have[g hg]:=@continuous_compact_convolution_exists R n Y NY hNY hY w hContinuous
      (family e) (@smoothing_dilation_smooth R n phi hPhi family hFamily e he) e
      (@smoothing_dilation_zero_beyond_radius R n phi family hPhi hFamily e he).
    by exists g.
  - exists (fun _=>0)=>h; exfalso; exact:he h.
have[g hg]:=choice hGlobal.
have hSupport e:0<e ->e<r ->forall x,~smooth_compact_carrier C x ->g e x=0.
  move=>he her.
  exact:(@compact_smoothing_support_bound R n Y NY hNY phi hPhi family hFamily
    (smooth_compact_carrier K) (smooth_compact_carrier C) r e w (g e)
    hThick he (ltW her) hOff (hg e he)).
have hTests e:exists f:DT,0<e ->e<r ->
    (forall x,value f x=g e x) /\ support f `<=` smooth_compact_carrier C.
  case:(pselect (0<e /\ e<r))=>[hSmall|hNo].
  - have[he her]:=hSmall.
    have hSmooth:=@continuous_smooth_convolution_smooth R n Y NY hNY hY w hContinuous
      (family e) e (g e) (@smoothing_dilation_smooth R n phi hPhi family hFamily e he)
      (@smoothing_dilation_zero_beyond_radius R n phi family hPhi hFamily e he) (hg e he).
    have hClass:=@smooth_class_open_restriction R X Y N NY hN hNY
      (fun _=>True) U (g e) (fun _ _=>Logic.I) hU hSmooth.
    have[f [hValue hBound]]:=@smooth_test_represents_with_support R X Y N NY hN hNY U
      E ev hE C (g e) hClass (hSupport e he her).
    exists f=>_ _; split; last exact hBound.
    move=>x; case:(pselect (U x))=>[hx|hx]; first exact:hValue x hx.
    rewrite (smooth_test_value_outside hE f hx).
    symmetry; apply:(hSupport e he her)=>hCx; exact:hx (smooth_compact_in_domain C x hCx).
  - exists (0:DT)=>he her; exfalso; apply:hNo; by split.
have[P hP]:=choice hTests.
exists r; split=>//; exists C,P; split.
- move=>e he her; have[hValue hBound]:=hP e he her.
  split; last exact hBound.
  have hEq:value (P e)=g e by apply:funext.
  rewrite hEq; exact:hg e he.
- move=>eta hEta.
  pose CG:=@smooth_compact_domain_inclusion R X N hN U (fun _=>True) (fun _ _=>Logic.I) C.
  have[d [hd hApprox]]:=@continuous_smoothing_locally_uniform R n Y NY hNY hY
    phi hPhi family hFamily w g hg hContinuous CG eta hEta.
  exists (Num.min r d); split; first by rewrite lt_min hr hd.
  split; first by rewrite ge_min lexx.
  move=>e he hSmall x.
  have /andP [her hed]:(e<r)&&(e<d) by rewrite -lt_min.
  have[hValue hBound]:=hP e he her.
  rewrite hValue.
  case:(pselect (smooth_compact_carrier C x))=>hx.
  + exact:hApprox e he hed x hx.
  + rewrite (hSupport e he her x hx).
    have hw:w x=0.
      apply:hOff=>hKx; exact:hx (hKC x hKx).
    by rewrite hw subrr (real_seminorm_zero hNY.1).
Qed.
End CompactContinuousSmoothingTests.
