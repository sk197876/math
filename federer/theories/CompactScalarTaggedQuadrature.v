(** Federer (1969), 4.1.2, p. 348: a
    continuous compactly supported scalar field is approximated
    by the same actual tagged Borel sums as the
    test kernels. This supplies the scalar side of
    the original integral/distribution interchange. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric NormClassOneUP ScalarNormMetricCompleteness
  GrassmannAbbreviations EuclideanInnerProduct InnerNorm HilbertFormCompactness
  SmoothCompactSet PartialFunctionUP PartialFunctionBasic MeasureUP MeasureIntegralUP SummableRealFunctionUP
  EuclideanLebesgueDimensions EuclideanDistributionMeasureContext TopologicalBorel CompactNearbyUniformContinuity
  ContinuousCompactFieldIntegral ScalarVectorIntegralIdentification FiniteTaggedBorelPartitionUP FiniteTaggedVectorIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CompactScalarTaggedQuadrature.
Variable R:realType.
Variable n:nat.
Local Notation X := (R_n R n).
Local Notation N := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hN := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation hNS := (@scalar_absolute_value_norm R).
Local Notation mu := (@euclidean_lebesgue_measure R n).
Local Notation hm := (euclidean_lebesgue_is_measure R n).
Variable K:smooth_compact_set hN (fun _=>True).
Variable b:R.
Hypothesis hMass:mu (smooth_compact_carrier K)=b%:E.
Variable F:X->R.
Hypothesis hF:norm_class_zero N (fun t:R^o=>`|t|) (fun _=>True) F.
Hypothesis hOff:forall x,~smooth_compact_carrier K x ->F x=0.

(** Source for [compact_scalar_tagged_quadrature]: the actual scalar
    integral and arbitrarily accurate tagged Borel sums used
    in Federer 4.1.2, p. 348. The
    finite-mass compact may be empty or have measure zero. *)
Theorem compact_scalar_tagged_quadrature:
  exists c:R,is_measure_integral mu (real_total_integrand F) c%:E /\
    forall eta:R,0<eta ->exists d:R,0<d /\
      forall (I:finType) (A:I->set X) (tag:I->X) (mesh:R),
        @is_finite_tagged_borel_partition R (real_norm_metric_space hN)
          (smooth_compact_carrier K) mesh I A tag ->mesh<d ->
        `|c-\sum_i fine (mu (A i))*F (tag i)|<=eta*b.
Proof.
have[c hIntegral]:=@continuous_compact_field_integral_exists R n R^o (fun t:R^o=>`|t|)
  hNS (@scalar_norm_metric_complete R) F K hF hOff.
exists c; split.
- exact:(@scalar_vector_integral_identification R X mu F c hIntegral).
- move=>eta hEta.
  have[d [hd hNear]]:=@norm_class_zero_compact_uniform_nearby R X R^o N (fun t:R^o=>`|t|) hN hNS
    (fun _=>True) (smooth_compact_carrier K) F (smooth_compact_is_compact K)
    (fun _ _=>Logic.I) hF eta hEta.
  exists d; split=>// I A tag mesh hPart hMesh.
  have hKMeas:=@euclidean_distribution_measure_borel R n (smooth_compact_carrier K)
    (closed_borel_set (compact_closed (@metric_hausdorff R (real_norm_metric_space hN))
      (smooth_compact_is_compact K))).
  have hAMeas i:=@euclidean_distribution_measure_borel R n (A i)
    (@finite_tagged_partition_borel R (real_norm_metric_space hN) (smooth_compact_carrier K)
      mesh I A tag hPart i).
  have hOsc i x:A i x ->`|F x-F (tag i)|<=eta.
    move=>hx; apply:ltW.
    have hTag:=@finite_tagged_partition_tag R (real_norm_metric_space hN)
      (smooth_compact_carrier K) mesh I A tag hPart i (ex_intro _ x hx).
    apply:(hNear (tag i) x
      (@finite_tagged_partition_inside R (real_norm_metric_space hN)
        (smooth_compact_carrier K) mesh I A tag hPart i (tag i) hTag) Logic.I).
    have h:=@finite_tagged_partition_mesh R (real_norm_metric_space hN)
      (smooth_compact_carrier K) mesh I A tag hPart i x hx.
    exact:le_lt_trans h hMesh.
  exact:(@finite_tagged_vector_quadrature_bound R (real_norm_metric_space hN) R^o (fun t:R^o=>`|t|)
    hNS mu hm (smooth_compact_carrier K) b hMass hKMeas mesh I A tag hPart hAMeas
    F c eta hIntegral hOff hOsc).
Qed.
End CompactScalarTaggedQuadrature.
