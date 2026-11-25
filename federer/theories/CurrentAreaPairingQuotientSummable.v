(** Federer (1969), 4.1.25, p. 383: the
    auxiliary scalar quotient is summable with no
    inverse-Jacobian loss. The actual normalized image
    mass equals the original top-source field's mass;
    its fixed-covector pairing is therefore dominated by
    an integrable multiple of that mass. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  NormOpenDomainLaws InnerNorm HilbertFormCompactness GrassmannAbbreviations
  EuclideanInnerProduct InnerMetric ExteriorGrading AlternatingForms
  CurrentCoefficientNorms CompactSummableMultivectors CompactSummableMultivectorAmbient
  EuclideanLebesgueDimensions LipschitzUP Rademacher
  PartialFunctionUP PartialAbsolutePartsGraph PartialExtendedOrderLoci
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasureIntegralUP
  MeasureAbsoluteSummability SummableRealFunctionUP SummableRealArithmetic
  CurrentAreaPairingQuotientUP CurrentAreaPairingQuotientSealed
  CurrentAreaPairingQuotientLaws CurrentAreaPairingQuotientNumerator
  CurrentAreaPairingQuotientMeasurable.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section AreaPairingSummable.
Variable R : realType.
Hypothesis h2 : (1+1:R)!=0.
Variables m n : nat.
Local Notation X := (R_n R m).
Local Notation Y := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R m)).
Local Notation Full := (fun _:X=>True).
Local Notation hFull := (fun (x:X) (_:True)=>norm_full_domain_interior NX x).
Local Notation mu := (@euclidean_lebesgue_measure R m).
Local Notation hm := (euclidean_lebesgue_is_measure R m).
Local Notation M := (@current_vector_mass R h2 m m).
Variable f : inner_metric_space (@euclidean_inner_productP R m)->
  inner_metric_space (@euclidean_inner_productP R n).
Hypothesis hLip : is_metric_lipschitz setT f.
Variable xi : @compact_summable_multivector_space R h2 m m Full hFull.
Local Notation raw := (@compact_summable_multivector_ambient_value R h2 m m Full hFull xi).
Variable a : A_m Y R^o m.
Local Notation q := (@CurrentAreaPairingQuotient.value R m n f raw a).

(** Source for [current_area_pairing_quotient_summable]:
    summability of the auxiliary quotient used with
    3.2.3(2) in 4.1.25, p. 383. Its
    measurability and the finite mass integral are
    both derived from the original Omega field. *)
Theorem current_area_pairing_quotient_summable : is_measure_summable mu q.
Proof.
have [b hNumerator]:=@current_area_pairing_numerator_summable R h2 m n f hLip xi a.
have hMeasurable:=@current_area_pairing_quotient_measurable R m n f raw a
  hLip hNumerator.1.
pose N:=@current_form_comass R h2 n m a.
pose H:=real_total_integrand (fun x:X=>N*M (raw x)).
have hH:is_measure_summable mu H.
  exists (N*@compact_summable_multivector_size R h2 m m Full hFull xi).
  exact:(@real_total_integral_scale R X mu hm (fun x=>M (raw x))
    (@compact_summable_multivector_size R h2 m m Full hFull xi) N
    (@compact_summable_multivector_ambient_integral R h2 m m Full hFull xi)).
have hDifferentiable:=@federer_3_1_6 R m n f hLip.
have hBound:measure_almost_everywhere mu
    (partial_extended_le_locus (partial_extended_function_absolute_value q) H).
  apply:(@measure_almost_everywhere_mono R X mu hm _ _ _ hDifferentiable)=>x [D hD].
  pose r:=@current_area_pairing_quotient_coefficient R m n raw a x D.
  exists (`|r|)%:E,(N*M (raw x))%:E.
  split.
  - exists r%:E;split.
    + exact:(@current_area_pairing_quotient_at_differential R m n f raw a x D hD).
    + by rewrite abse_EFin.
  - split;first by apply/real_total_integrand_graph.
    rewrite lee_fin mulrC.
    exact:(@current_area_pairing_quotient_coefficient_bound R m n f raw a h2 x D hD).
exact:(@measure_dominated_summable R X mu hm q H hMeasurable hH hBound).1.
Qed.
End AreaPairingSummable.
