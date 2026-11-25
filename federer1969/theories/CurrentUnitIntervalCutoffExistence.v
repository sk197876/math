(** Federer (1969), 4.1.12, p. 369: prove
    the unit-scale smooth cutoff by the original
    positive regularisation of 4.1.2, p. 347.
    The existing one-Lipschitz interval bump is
    smoothed at radius 1/4. Kernel symmetry is
    unnecessary; its original support and mass suffice. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions
  classical_sets reals topology lra.
From Federer Require Import RealNormUP NormMetric NormClassOneUP NormRegularity
  GrassmannAbbreviations EuclideanInnerProduct EuclideanOneCoordinate EuclideanOneNormDifferential
  InnerNorm HilbertFormCompactness ScalarNormMetricCompleteness SmoothingKernelUP SmoothingKernelSealed
  SmoothingDilationUP SmoothingDilationSealed SmoothingDilationSmooth SmoothingDilationNonzeroRadius
  SmoothingConvolutionUP ContinuousCompactConvolution ContinuousSmoothingSmoothness CompactSmoothingSupport
  SmoothingLipschitzBound SmoothingPointwiseOscillation CurrentTrapezoidInput CurrentUnitIntervalCutoffUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [current_unit_interval_cutoff_exists]:
    the independently specified smooth cutoff for the
    original phi_k exists, supporting Federer 4.1.12,
    p. 369. The construction supplies a witness
    only; its consumers use the stated laws. *)
Theorem current_unit_interval_cutoff_exists (R:realType):
  exists f:R_n R 1%N->R^o,is_current_unit_interval_cutoff f.
Proof.
pose X:=R_n R 1%N.
pose N:=inner_norm (@euclidean_inner_productP R 1%N).
pose hN:=inner_norm_real_norm (@euclidean_inner_productP R 1%N).
pose hR:=@scalar_absolute_value_norm R.
pose phi:=@SmoothingKernel.value R 1%N.
pose hPhi:=@SmoothingKernel.laws R 1%N.
pose family:=@SmoothingDilation.value R 1%N phi.
pose hFamily:=@SmoothingDilation.laws R 1%N phi.
pose e:R:=1/4.
have he:0<e by rewrite /e;lra.
have hSmooth:=@smoothing_dilation_smooth R 1%N phi hPhi family hFamily e he.
have hOff:=@smoothing_dilation_zero_beyond_radius R 1%N phi family hPhi hFamily e he.
pose u:=@current_trapezoid_input R.
have hU:=@current_trapezoid_input_continuous R.
have[g hG]:=@continuous_compact_convolution_exists R 1%N R^o (fun t:R^o=>`|t|)
  hR (@scalar_norm_metric_complete R) u hU (family e) hSmooth e hOff.
exists g;split.
- exact:(@continuous_smooth_convolution_smooth R 1%N R^o (fun t:R^o=>`|t|)
    hR (@scalar_norm_metric_complete R) u hU (family e) e g hSmooth hOff hG).
- split.
  + exact:(@smoothing_scalar_unit_range R 1%N phi hPhi family hFamily e u g he hG
      (@current_trapezoid_input_range R)).
  + split.
    * have hInput x y:`|u x-u y|<=1*N (x-y).
        rewrite mul1r;exact:(@current_trapezoid_input_lipschitz R x y).
      have hBound:=@smoothing_lipschitz_bound R 1%N R^o (fun t:R^o=>`|t|)
        hR phi hPhi family hFamily e u g 1 he hG hInput.
      move=>x y;have h:=hBound x y;by rewrite mul1r in h.
    * split.
      -- apply:(@smoothing_pointwise_plateau R 1%N R^o (fun t:R^o=>`|t|)
           hR (@scalar_norm_metric_complete R) phi hPhi family hFamily e u g he hG
           (euclidean_one_embed 2) 1)=>z hz.
         apply:(@current_trapezoid_input_plateau R).
         have hRadius:=@smoothing_dilation_nonzero_radius R 1%N phi family hPhi hFamily e he z hz.
         rewrite euclidean_one_norm_coordinate /e in hRadius.
         have hSmall:`|z ord0|<1/4:=hRadius.
         rewrite ltr_norml in hSmall.
         have[hLow hHigh]:=andP hSmall.
         rewrite /euclidean_one_project /euclidean_one_embed !ffunE.
         apply/andP;split;lra.
      -- apply:(@compact_smoothing_support_bound R 1%N R^o (fun t:R^o=>`|t|)
           hR phi hPhi family hFamily
           [set x|1/2<=euclidean_one_project x<=7/2]
           [set x|1/4<=euclidean_one_project x<=15/4] e e u g).
         ++ move=>x z /andP[hLow hHigh] hDistance.
            rewrite euclidean_one_norm_coordinate /e ler_norml in hDistance.
            have[hDLow hDHigh]:=andP hDistance.
            rewrite /euclidean_one_project !ffunE in hDLow hDHigh hLow hHigh *.
            apply/andP;split;lra.
         ++ exact:he.
         ++ exact:lexx.
         ++ move=>z hz;apply:(@current_trapezoid_input_zero R).
            apply/negP=>/andP[hLow hHigh];apply:hz.
            apply/andP;split;exact:ltW.
         ++ exact:hG.
Qed.
