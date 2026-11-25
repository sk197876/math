(** Federer (1969), 4.1.2, p. 347: for
    a class-one input, the directional derivative
    commutes with convolution by the original smoothing
    kernel. The alternate convolution formula and the
    compact-uniform quotient theorem give the printed calculation. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals constructive_ereal topology lra.
From Federer Require Import Hom RealNormUP NormMetric NormRegularity NormDifferentialUP NormedCurveDerivativeUP
  GrassmannAbbreviations EuclideanInnerProduct InnerNorm HilbertFormCompactness
  MetricClosedBalls EuclideanNormClosedBalls NormCompactDirectionalQuotient EuclideanLebesgueDimensions
  SmoothingKernelUP SmoothingDilationUP SmoothingDilationSmooth SmoothingDilationIntegral SmoothingDilationNonzeroRadius
  VectorDaniellHypotheses SmoothingConvolutionUP SmoothingConvolutionSubstitution
  TotalVectorIntegralArithmetic UnitKernelVectorDifference EuclideanReflectionTranslation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section SmoothingInputDirectional.
Variable R:realType.
Variable n:nat.
Local Notation X := (R_n R n).
Local Notation N := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hN := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation T := (real_norm_metric_space hN).
Local Notation mu := (@euclidean_lebesgue_measure R n).
Local Notation hm := (euclidean_lebesgue_is_measure R n).
Variable Y:lmodType R.
Variable NY:Y->R.
Hypothesis hNY:is_real_norm NY.
Hypothesis hSep:is_separable_normed_space hNY.
Variable phi:X->R.
Hypothesis hPhi:is_smoothing_kernel phi.
Variable family:R->X->R.
Hypothesis hFamily:is_smoothing_dilation phi family.
Variable e:R.
Hypothesis he:0<e.
Variables f xi g q:X->Y.
Hypothesis hF:norm_class hN hNY (fun _=>True) f 1%N.
Variable D:X->Hom X Y.
Hypothesis hD:forall a,has_norm_differential N NY (fun _=>True) f a (D a).
Variable v:X.
Hypothesis hXi:forall a,D a v=xi a.
Hypothesis hConv:is_smoothing_convolution hNY (family e) f g.
Hypothesis hConvXi:is_smoothing_convolution hNY (family e) xi q.

(** Source for [smoothing_input_directional_derivative]: the original
    identity D_j(Phi*f)=Phi*D_j f for class-one
    f, Federer 4.1.2, p. 347. Arbitrary
    directions, including zero, are retained. *)
Theorem smoothing_input_directional_derivative (a:T):
  punctured_norm_limit NY (fun t=>t^-1*:(g (a+t*:v)-g a)) (q a).
Proof.
move=>eta hEta.
have hEta2:0<eta/2 by rewrite divr_gt0 // ltr0n.
have [d [hd hUniform]]:=@norm_compact_directional_quotient R X Y N NY hN hNY
  (fun _=>True) (metric_closed_ball a e) f hF (@euclidean_norm_closed_ball_compact R n a e)
  (fun _ _=>Logic.I) v (eta/2) hEta2.
exists d; split=>// t ht.
have hAlternate:=@smoothing_convolution_alternate_integral R n Y NY hNY (family e) f g hSep hConv.
have hAlternateXi:=@smoothing_convolution_alternate_integral R n Y NY hNY (family e) xi q hSep hConvXi.
have hDiff:=@total_vector_integral_subtract R X Y NY hNY mu hm
  (fun z=>family e z*:f (a+t*:v-z)) (fun z=>family e z*:f (a-z))
  (g (a+t*:v)) (g a) (hAlternate (a+t*:v)) (hAlternate a).
have hScale:=@total_vector_integral_scale R X Y NY hNY mu hm
  (fun z=>family e z*:f (a+t*:v-z)-family e z*:f (a-z))
  (g (a+t*:v)-g a) t^-1 hDiff.
have hEq:(fun z:X=>(t^-1*:(family e z*:f (a+t*:v-z)-family e z*:f (a-z)):real_norm_metric_space hNY))=
    (fun z=>(family e z*:(t^-1*:(f (a+t*:v-z)-f (a-z))):real_norm_metric_space hNY)).
  apply:funext=>z; by rewrite -scalerBr !scalerA (mulrC t^-1 (family e z)).
rewrite hEq in hScale.
have hBound z:family e z!=0 ->
    NY (t^-1*:(f (a+t*:v-z)-f (a-z))-xi (a-z))<=eta/2.
  move=>hz.
  have hRadius:=@smoothing_dilation_nonzero_radius R n phi family hPhi hFamily e he z hz.
  have hBase:metric_closed_ball a e (a-z).
    change (is_true (N (a-(a-z))<=e)).
    rewrite (@euclidean_reflection_translation_involutive R n a z); exact:ltW hRadius.
  have hPoint:=hUniform (a-z) hBase t ht (D (a-z)) (hD (a-z)).
  have hShift:a+t*:v-z=(a-z)+t*:v by rewrite addrAC.
  rewrite hShift -hXi; exact:ltW hPoint.
have hNonneg:=@smoothing_dilation_nonnegative R n phi hPhi family hFamily e he.
have hMass:=@smoothing_dilation_integral_one R n phi family hPhi hFamily e he.
have hError:=@unit_weight_vector_difference_bound R X Y NY hNY mu hm (family e)
  (fun z=>t^-1*:(f (a+t*:v-z)-f (a-z))) (fun z=>xi (a-z))
  (t^-1*:(g (a+t*:v)-g a)) (q a) (eta/2)
  hNonneg hMass hScale (hAlternateXi a) hBound.
apply:le_lt_trans hError _; lra.
Qed.
End SmoothingInputDirectional.
