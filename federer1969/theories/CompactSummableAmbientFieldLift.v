(** Federer (1969), 4.1.23, p. 379: ambient
    compact L1 step fields give the original
    Omega representatives on the full current domain.
    Both actual values and the exact original
    integral cost are preserved. No quotient
    by null fields is introduced. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric NormDifferentialUP
  NormOpenDomainLaws InnerNorm HilbertFormCompactness GrassmannAbbreviations
  EuclideanInnerProduct ExteriorGrading CurrentDomain CurrentCoefficientNorms
  CurrentVectorCompleteness CompactSummableFieldSealed CompactSummableFieldLaws
  CompactSummableFieldIntegral CompactSummableFieldRepresentation
  CompactSummableMultivectors CompactSummableMultivectorAmbient
  EuclideanLebesgueDimensions EuclideanOpenDomainMeasure EuclideanFullDomainMeasure
  OpenSubspaceExtension IsotropyGroupTopology MeasurableFunctionUP
  PushforwardMeasurableFunctions PartialFunctionUP
  PartialFunctionBasic PartialFunctionPrecomposition TotalVectorNormIntegrability
  TotalVectorIntegralDomination MeasureUP MeasureIntegralUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section AmbientLift.
Variable R : realType.
Hypothesis h2 : (1+1:R)!=0.
Variables n m : nat.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation XT := (real_norm_metric_space hNX).
Local Notation Full := (fun _ : X => True).
Local Notation hFull := (fun (x : X) (_ : True) => norm_full_domain_interior NX x).
Local Notation FT := (current_domain R n Full).
Local Notation V := (exterior_power X m).
Local Notation VN := (@current_vector_mass R h2 n m).
Local Notation hVN := (@current_vector_mass_real_norm R h2 n m).
Local Notation Leb := (@euclidean_lebesgue_measure R n).
Local Notation hLeb := (euclidean_lebesgue_is_measure R n).
Local Notation alpha := (@euclidean_open_domain_measure R n Full).
Local Notation hAlpha := (@euclidean_open_domain_measure_laws R n Full hFull).1.
Local Notation WA := (@CompactSummableField.space R XT V VN hVN Leb hLeb).
Local Notation WF := (@compact_summable_multivector_space R h2 n m Full hFull).
Local Notation value := (@compact_summable_field_value R XT V VN hVN Leb hLeb).
Local Notation size := (@compact_summable_field_size R XT V VN hVN Leb hLeb).
Local Notation raw := (@compact_summable_multivector_ambient_value R h2 n m Full hFull).

(** Source for [compact_summable_ambient_field_lift]:
    the step fields used in Federer
    4.1.23, p. 379, retain their
    original ambient values and exact mass
    integral when placed in Omega_m(R^n).
    Compactness and finite summability follow
    from the original actual field's laws. *)
Theorem compact_summable_ambient_field_lift (f : WA) :
  exists xi : WF, raw xi=value f /\
    @compact_summable_multivector_size R h2 n m Full hFull xi=size f.
Proof.
pose g := fun x : FT => (value f (set_val x):real_norm_metric_space hVN).
have hFMeas := @compact_summable_field_measurable R XT V VN hVN Leb hLeb f.
have hPull : is_measure_measurable_function Leb
    (partial_function_precompose (@euclidean_full_domain_point R n)
      (partial_function_total g)).
  exact: hFMeas.1.
have hGMeas := @pushforward_function_measurable_from_composition R X FT
  (real_norm_metric_space hVN) Leb (@euclidean_full_domain_point R n) _ hPull.
rewrite -euclidean_full_domain_measure_image in hGMeas.
have hNorm := @euclidean_full_domain_real_integral R n
  (fun x => VN (value f x)) (size f)%:E
  (@compact_summable_field_size_integral R XT V VN hVN Leb hLeb f).
have hLone := @total_vector_lone_from_norm_integral R FT V VN hVN alpha hAlpha
  g (size f) (@current_multivector_mass_separable R h2 n m) hGMeas hNorm.
have [K [hK hOff]] := @compact_summable_field_compact R XT V VN hVN Leb hLeb f.
pose C : set FT := set_val @^-1` K.
have hC : compact C := @set_type_compact_preimage XT Full K hK (fun _ _ => Logic.I).
have hGOff : forall x y,
    partial_function_graph (partial_function_total g) x y -> ~C x -> y=0.
  move=> x y hValue hx; change (g x=y) in hValue.
  rewrite -hValue; exact: (@hOff (set_val x) hx).
have [xi [hExtend [_ [_ [_ hSize]]]]] :=
  @compact_summable_partial_field_representative R FT V VN hVN alpha hAlpha
    (partial_function_total g) hLone.2.1 hLone.2.2.1 C hC hGOff.
have hValue : @compact_summable_multivector_value R h2 n m Full hFull xi=
    (fun x : FT => value f (set_val x)).
  apply: funext=> x; exact: (@hExtend x (g x) (erefl (g x))).
exists xi; split.
- apply: funext=> x; pose p := @euclidean_full_domain_point R n x.
  change (raw xi (set_val p)=value f (set_val p)).
  by rewrite compact_summable_multivector_ambient_inside hValue.
- have hNormValue := @total_vector_lone_norm_value R FT V VN hVN alpha hAlpha
    g (size f) hGMeas hNorm.
  rewrite hNormValue in hSize.
  exact: esym (EFin_inj hSize).
Qed.
End AmbientLift.
