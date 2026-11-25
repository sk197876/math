(** Federer (1969), 4.1.2, p. 347: the
    actual smoothing family exists on E(R^n,Y).
    Banach convolution and its smoothness precede
    realization in the abstract smooth space;
    linearity follows from the actual integral laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals constructive_ereal topology.
From Federer Require Import MeasureVectorIntegralUP Hom RealNormUP NormMetric CompleteMetricUP VectorDaniellHypotheses NormRegularity
  GrassmannAbbreviations EuclideanInnerProduct InnerNorm HilbertFormCompactness
  SmoothFunctionSpaceUP SmoothFunctionSpaceLaws SmoothingKernelUP SmoothingDilationUP SmoothingDilationSmooth
  SmoothingDilationNonzeroRadius SmoothingConvolutionUP SmoothingConvolutionExistence CompactSmoothConvolutionSmoothness
  ContinuousFieldLocalIntegrability TotalVectorIntegralArithmetic SmoothSmoothingFamilyUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section SmoothSmoothingFamilyExistence.
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
Variable phi:X->R.
Hypothesis hPhi:is_smoothing_kernel phi.
Variable family:R->X->R.
Hypothesis hFamily:is_smoothing_dilation phi family.

(** Source for [smooth_smoothing_member_exists]: every actual
    convolution of a member of E(R^n,Y)
    is represented there, supporting Federer 4.1.2,
    p. 347. No extra local
    integrability or derivative-existence premise is added. *)
Lemma smooth_smoothing_member_exists e (he:0<e) f:
  exists g:E,is_smoothing_convolution hNY (family e) (ev f) (ev g).
Proof.
have hLocal:=@continuous_field_locally_norm_integrable R n Y NY hNY (ev f)
  (norm_class_continuous (smooth_function_evaluation_smooth hE f 0%N)).
have [g hConv]:=@smoothing_convolution_exists R n Y NY hNY hY hSep phi hPhi family hFamily e he (ev f) hLocal.
have hSmooth:=@compact_smooth_convolution_smooth R n Y NY hNY hY hSep (ev f) hLocal (family e) e g
  (@smoothing_dilation_smooth R n phi hPhi family hFamily e he)
  (fun z=>@smoothing_dilation_zero_beyond_radius R n phi family hPhi hFamily e he z) hConv.
have [gE hValue]:=smooth_function_evaluation_surjective hE hSmooth.
exists gE=>x; by rewrite (@hValue x Logic.I); exact:hConv x.
Qed.

(** Source for [smooth_smoothing_operator_exists]: the original
    integral map f |-> Phi_epsilon*f is
    an actual linear endomorphism of E(R^n,Y),
    supporting Federer 4.1.2, p. 347. *)
Theorem smooth_smoothing_operator_exists e (he:0<e):
  exists P:Hom E E,is_smooth_smoothing_operator hNY ev (family e) P.
Proof.
have [G hG]:=choice (@smooth_smoothing_member_exists e he).
have hLinear:linear G.
  move=>c f g; apply:(smooth_function_extensional hE)=>x _.
  rewrite (smooth_function_add_value hE) (smooth_function_scale_value hE).
  have hScale:=@total_vector_integral_scale R X Y NY hNY
    (@EuclideanLebesgueDimensions.euclidean_lebesgue_measure R n)
    (EuclideanLebesgueDimensions.euclidean_lebesgue_is_measure R n)
    (fun z=>family e (x-z)*:ev f z) (ev (G f) x) c (hG f x).
  have hSum:=@total_vector_integral_add R X Y NY hNY
    (@EuclideanLebesgueDimensions.euclidean_lebesgue_measure R n)
    (EuclideanLebesgueDimensions.euclidean_lebesgue_is_measure R n)
    (fun z=>c*:(family e (x-z)*:ev f z)) (fun z=>family e (x-z)*:ev g z)
    (c*:ev (G f) x) (ev (G g) x) hScale (hG g x).
  have hEq:(fun z:X=>(c*:(family e (x-z)*:ev f z)+family e (x-z)*:ev g z:real_norm_metric_space hNY))=
      (fun z=>(family e (x-z)*:ev (c*:f+g) z:real_norm_metric_space hNY)).
    apply:funext=>z.
    by rewrite (smooth_function_evaluation_linear hE) scalerDr !scalerA (mulrC c (family e (x-z))).
  rewrite hEq in hSum.
  exact:(measure_vector_integral_unique (hG (c*:f+g) x) hSum).
exists (@HomMap R E E G (introT (asboolP _) hLinear)); exact hG.
Qed.

(** Source for [smooth_smoothing_family_exists]: the original
    positive-scale smoothing operators form a family
    on E(R^n,Y), Federer 4.1.2, p. 347.
    The proof specifies no nonpositive-scale value. *)
Theorem smooth_smoothing_family_exists:
  exists P:R->Hom E E,is_smooth_smoothing_family hNY ev family P.
Proof.
have hFor e:exists P:Hom E E,0<e ->is_smooth_smoothing_operator hNY ev (family e) P.
  case:(pselect (0<e))=>he.
  - have [P hP]:=@smooth_smoothing_operator_exists e he.
    exists P; by move=>_.
  - exists 0; by move=>/he.
have [P hP]:=choice hFor.
exists P; exact hP.
Qed.
End SmoothSmoothingFamilyExistence.
