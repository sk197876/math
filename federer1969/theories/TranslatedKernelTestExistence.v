(** Federer (1969), 4.1.2, p. 347: existence
    of the actual translated kernel tests defining the
    smooth dual density. Smoothness and compact support
    are proved before selecting their linear realizations. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormRegularity NormRegularityLinearMaps NormHigherCurveDerivativeUP
  NormAffineDilationDifferentials ContinuousMultilinearSealed
  GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerNorm HilbertFormCompactness
  FiniteNormEquivalence SmoothCompactSet SmoothFunctionSpaceUP SmoothTestSpaces SmoothTestEvaluation SmoothTestRepresentation
  TranslatedKernelTestUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section TranslatedKernelTestExistence.
Variable R:realType.
Variable n:nat.
Local Notation X := (R_n R n).
Local Notation N := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hN := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation hR := (@scalar_absolute_value_norm R).
Variable Y:lmodType R.
Variable NY:Y->R.
Hypothesis hNY:is_real_norm NY.
Variable E:lmodType R.
Variable ev:E->X->Y.
Hypothesis hE:is_smooth_function_space hN hNY (fun _=>True) ev.
Local Notation DT := (smooth_test_space hE).
Variable psi:X->R.
Hypothesis hPsi:norm_class_all_orders hN hR (fun _=>True) psi.
Variable r:R.
Hypothesis hOff:forall x,r<N x ->psi x=0.

(** Source for [translated_scalar_kernel_smooth]: translations
    of the original kernel remain smooth, as used
    to define g_epsilon in Federer 4.1.2, p. 347. *)
Theorem translated_scalar_kernel_smooth z:
  norm_class_all_orders hN hR (fun _=>True) (fun x=>psi (x-z)).
Proof.
pose Z:=fun j=>@ContinuousMultilinear.space R j X R^o N (fun t:R^o=>`|t|) hN hR.
pose ez:=fun j=>@ContinuousMultilinear.evaluation R j X R^o N (fun t:R^o=>`|t|) hN hR.
pose ZN:=fun j=>@ContinuousMultilinear.norm R j X R^o N (fun t:R^o=>`|t|) hN hR.
pose hZ:=fun j=>@ContinuousMultilinear.laws R j X R^o N (fun t:R^o=>`|t|) hN hR.
have h:=@norm_class_infinity_affine_dilation R X R^o N (fun t:R^o=>`|t|) hN hR
  Z ez ZN hZ psi 1 (-z) hPsi.
have he:(fun x:X=>psi ((1:R)*:x+-z))=(fun x=>psi (x-z)).
  apply:funext=>x; by rewrite scale1r.
by rewrite he in h.
Qed.

(** Source for [translated_kernel_test_exists]: the displayed
    test in Federer 4.1.2, p. 347, belongs
    to the original D space for every centre and vector. *)
Theorem translated_kernel_test_exists z y:
  exists f:DT,forall x,smooth_test_value hE f x=psi (x-z)*:y.
Proof.
pose L:=@scalar_coefficient_linear_map R Y y.
have hL:norm_bounded_linear (fun t:R^o=>`|t|) NY L.
  exists (NY y); split; first exact:real_seminorm_nonnegative hNY.1 y.
  by move=>t; rewrite (real_seminorm_scale hNY.1) mulrC.
have hClass:norm_class_all_orders hN hNY (fun _=>True) (fun x=>psi (x-z)*:y).
  move=>k.
  exact:(@norm_class_postcompose_linear R X R^o Y N (fun t:R^o=>`|t|) NY hN hR hNY
    (fun _=>True) (fun x=>psi (x-z)) L k hL (translated_scalar_kernel_smooth z k)).
pose K:=@Build_smooth_compact_set R X N hN (fun _=>True) [set x|N (x-z)<=r]
  (fun _ _=>Logic.I)
  (@finite_norm_closed_ball_compact R X n (@coordinate_basis R n) (@coordinate_basisP R n) N hN z r).
have hZero x:~smooth_compact_carrier K x ->psi (x-z)*:y=0.
  move=>hx.
  have hLarge:r<N (x-z) by rewrite ltNge; apply/negP=>hSmall; apply:hx.
  by rewrite (@hOff (x-z) hLarge) scale0r.
have[f hf]:=@smooth_test_represents_compact_function R X Y N NY hN hNY
  (fun _=>True) E ev hE K _ hClass hZero.
exists f=>x; exact:hf x Logic.I.
Qed.

(** Source for [translated_kernel_tests_exists]: the tests defining
    g_epsilon in Federer 4.1.2, p. 347, form
    actual linear maps from Y into D for every centre. *)
Theorem translated_kernel_tests_exists:
  exists B:X->Hom Y DT,@is_translated_kernel_tests R X Y N NY hN hNY E ev hE psi B.
Proof.
have hFor z:exists B:Hom Y DT,forall y x,smooth_test_value hE (B y) x=psi (x-z)*:y.
  have[b hb]:=choice (translated_kernel_test_exists z).
  have hLinear:linear b.
    move=>c y v; apply:(smooth_test_values_extensional hE)=>x _.
    rewrite (smooth_test_values_linear hE c (b y) (b v)).
    change (smooth_test_value hE (b (c*:y+v)) x=
      c*:smooth_test_value hE (b y) x+smooth_test_value hE (b v) x).
    rewrite !hb; by rewrite scalerDr !scalerA mulrC.
  pose B:=@HomMap R Y DT b (introT (asboolP _) hLinear).
  exists B; exact hb.
have[B hB]:=choice hFor.
exists B; exact hB.
Qed.
End TranslatedKernelTestExistence.
