(** Federer (1969), 4.1.8, p. 362: the
    original explicit segment-slice integral. Reuse the
    independently specified actual slice, original segment
    current, and right-interior pairing law. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets
  reals constructive_ereal topology normedtype.
From Federer Require Import Hom GradedComponents RealNormUP NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct EuclideanBlockCoordinates EuclideanCartesianMap
  ExteriorGrading ExteriorPowers AlternatingForms AlternatingPairing CurrentSpaces
  CurrentCartesianDomain CurrentCartesianSliceUP CurrentCartesianSliceSealed
  CurrentCartesianSliceTestSealed CurrentCartesianSliceTestPairing CurrentCartesianVectorProduct
  CurrentSegmentMapUP OrientedSegmentCurrentUP OrientedSegmentCurrentSealed ConvexMetricSegment
  RealMetricBackground ExtendedRealOrderTopology LebesgueScalarMeasure PartialFunctionUP PartialZeroExtension
  MeasureIntegralUP MeasureSubsetIntegral MeasureIntegralGraphEquivalence SummableRealFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section OrientedSegmentSliceIntegral.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables m n j:nat.
Local Notation X := (R_n R m).
Local Notation Y := (R_n R n).
Variables (A:set X) (B:set Y).
Hypothesis hA:forall a,A a->norm_domain_interior (inner_norm (@euclidean_inner_productP R m)) A a.
Hypothesis hB:forall b,B b->norm_domain_interior (inner_norm (@euclidean_inner_productP R n)) B b.
Local Notation AB := (@euclidean_cartesian_set R m n A B).
Local Notation hAB := (@current_cartesian_domain_open R m n A B hA hB).
Variables u v:X.
Hypothesis hSegment:@is_current_segment_domain R m A u v.
Local Notation S := (@OrientedSegmentCurrent.value R h2 m A hA u v hSegment).
Local Notation H := (@CartesianSlice.value R h2 m n 1%N j A B hA hB S).
Local Notation G := (fun b hb=>@CartesianSliceTest.value R h2 m n A B hA hB 1%N j b hb).
Local Notation velocity := (exterior_first_inclusion X (v-u)).
Local Notation F := (@current_cartesian_vector_product R m n 1%N j).
Local Notation ta := (@current_test_value R h2 m A hA 1%N).
Local Notation tb := (@current_test_value R h2 n B hB j).
Local Notation tc := (@current_test_value R h2 (m+n) AB hAB (1+j)).
Local Notation I := (`[0,1]:set (real_line_metric R)).

(** Source for [oriented_segment_slice_integral]: the
    printed eta pairing with phi_[u,v](b) is the
    original integral of the full form paired with
    P(v-u) wedge Lambda_j Q eta, Federer 4.1.8,
    p. 362. The original b, eta and every actual
    test phi are retained. *)
Theorem oriented_segment_slice_integral phi b (hb:B b) (eta:exterior_power Y j):
  is_measure_subset_integral (@lebesgue_scalar_measure R) I
    (real_total_integrand (fun t=>pairing (F velocity eta)
      (tc phi (euclidean_block_join (metric_segment_point u v t,b)))))
    (pairing eta (tb (H phi) b))%:E.
Proof.
have hSlice:=@CartesianSlice.laws R h2 m n 1%N j A B hA hB S phi b hb eta.
have hAction:=@OrientedSegmentCurrent.laws R h2 m A hA u v hSegment (G b hb eta phi).
rewrite -hSlice in hAction.
pose f t:=pairing velocity (ta (G b hb eta phi) (metric_segment_point u v t)).
pose g t:=pairing (F velocity eta) (tc phi (euclidean_block_join (metric_segment_point u v t,b))).
have hPoint t:I t->f t=g t.
  move=>ht.
  exact:(@current_cartesian_slice_test_pairing R h2 m n 1%N j A B hA hB
    b hb eta phi (metric_segment_point u v t) (@hSegment t ht) velocity).
apply:(@measure_integral_graph_equivalent R (real_line_metric R) (@lebesgue_scalar_measure R)
  _ _ _ _ hAction)=>t z.
change (partial_function_graph (partial_function_zero_extension (0:extended_real_line R) I
    (real_total_integrand f)) t z <->
  partial_function_graph (partial_function_zero_extension (0:extended_real_line R) I
    (real_total_integrand g)) t z).
rewrite !partial_function_zero_extension_graph.
split;move=>[[ht hv]|[hn hz]].
- left;split=>//;move:hv;by rewrite !real_total_integrand_graph (hPoint t ht).
- right;by split.
- left;split=>//;move:hv;by rewrite !real_total_integrand_graph (hPoint t ht).
- right;by split.
Qed.
End OrientedSegmentSliceIntegral.
