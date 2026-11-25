(** Federer (1969), 4.1.14, p. 371: the original
    all-set variation bound for a finite-mass flat input.
    Finite mass supplies the source representation; the
    approximation law supplies the image representation.
    The resulting inequality holds for all original
    representation witnesses on both sides. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions
  classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric NormDifferentialUP NormClassOneUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  LipschitzUP SmoothCompactSet CurrentDomain CurrentSpaces CurrentMassSealed
  CurrentIntegrationCriterion CurrentFiniteMassRepresentation NormalisedCurrentSealed
  CurrentProperSupportDomain FlatCurrentsUP CurrentCompactLipschitzPushforwardUP
  CurrentCompactMajorantApproximationUP CurrentLipschitzMajorantVariation
  MeasureDensity MeasurePushforward SummableRealFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [current_finite_mass_lipschitz_image_majorant_variation]:
    the original ||f#T|| <= f#(||T|| sigma^m) in
    Federer 4.1.14, p. 371, with finite M(T), original
    flatness and the continuous Lebesgue-AE actual-derivative
    majorant as the only mathematical premises. Normality and
    a source-variation-AE derivative bound are not required. *)
Theorem current_finite_mass_lipschitz_image_majorant_variation
    (R:realType) (h2:(1+1:R)!=0) n nu m
    (U:set (R_n R n)) (V:set (R_n R nu))
    (hU:forall x,U x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) U x)
    (hV:forall y,V y->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R nu)) V y)
    (f:R_n R n->R_n R nu) (hImage:forall x,U x->V (f x))
    (hLocal:@is_locally_metric_lipschitz R
      (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n)))
      (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R nu))) U f)
    (K:smooth_compact_set
      (inner_norm_real_norm (@euclidean_inner_productP R n)) U)
    (T:@current_space R h2 n U hU m)
    (Q:@current_space R h2 nu V hV m)
    (sigma:R_n R n->R^o):
  @is_flat_current_supported_in R h2 n m U hU K T->
  (@CurrentMass.value R h2 n m U hU T< +oo)%E->
  @is_current_compact_lipschitz_image R h2 n nu m U V hU hV
    f hImage hLocal K T Q->
  norm_class_zero (inner_norm (@euclidean_inner_productP R n))
    (fun t:R^o=>`|t|) U sigma->
  @is_current_ae_differential_majorant R n nu U f sigma->
  @is_integration_representable_current R h2 nu m V hV Q /\
  forall hSource:@is_integration_representable_current R h2 n m U hU T,
    forall hTarget:@is_integration_representable_current R h2 nu m V hV Q,
      forall B,(@NormalisedCurrent.measure R h2 nu m V hV Q hTarget B<=
        measure_pushforward (@current_map_on_domain R n nu U V f hImage)
          (measure_with_density (@NormalisedCurrent.measure R h2 n m U hU T hSource)
            (real_total_integrand (fun x:current_domain R n U=>
              ((sigma (set_val x))^+m)%R))) B)%E.
Proof.
move=>hFlat hFinite hPoint hSigma hMajorant.
have hSource:=@current_finite_mass_representation R h2 n m U hU T hFinite.
have[hRepresented _]:=@current_lipschitz_image_majorant_variation R h2 n nu m
  U V hU hV f hImage hLocal K T hSource hFlat hFinite Q hPoint sigma hSigma hMajorant.
split;first exact:hRepresented.
move=>hActualSource hActualTarget B.
have[_ hBound]:=@current_lipschitz_image_majorant_variation R h2 n nu m
  U V hU hV f hImage hLocal K T hActualSource hFlat hFinite Q hPoint
  sigma hSigma hMajorant.
exact:hBound hActualTarget B.
Qed.
