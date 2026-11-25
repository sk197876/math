(** Federer (1969), 4.1.5, p. 350:
    common compact support turns a uniform norm
    error into an L1 error. The original Radon
    compact finiteness and Chapter 2 characteristic
    comparison give the quantitative bound. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric FunctionLatticeUP CompactSupportFunctionUP CompactContinuousVectorFields
  MeasureUP MeasureBasic RadonMeasureUP RadonBorelRegularity RealIntegralFunctionalUP
  SummableRealFunctionUP MeasureIntegralUP RealTotalCharacteristicBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [compact_field_uniform_integral_bound]:
    the uniform-to-L1 estimate for the original
    compact test approximation in Federer 4.1.5,
    p. 350. Zero compact masses are retained. *)
Theorem compact_field_uniform_integral_bound (R:realType) (X:topologicalType)
    (Y:lmodType R) (NY:Y->R) (hNY:is_real_norm NY)
    (mu:set X->\bar R) (hm:is_measure mu) (hr:is_radon_measure mu)
    (F:(X->R)->R)
    (hF:is_real_integral_functional mu
      (positive_function_lattice (@compactly_supported_continuous_functions R X)) F)
    (u:X->Y) (C:set X) delta:
  compact_continuous_vector_fields hNY u ->compact C ->0<delta ->
  (forall x,NY (u x)<=delta) ->(forall x,~C x ->u x=0) ->
  exists a:R,is_measure_integral mu (real_total_integrand (fun x=>NY (u x))) a%:E /\
    a<=delta*fine (mu C).
Proof.
move=>hu hC hDelta hBound hOff.
have hPositive:positive_function_lattice (@compactly_supported_continuous_functions R X) (fun x=>NY (u x)).
  split; first exact:(@compact_continuous_vector_field_norm R X Y NY hNY u hu).
  move=>x; exact:real_seminorm_nonnegative hNY.1 (u x).
pose a:=F (fun x=>NY (u x)).
have hI:is_measure_integral mu (real_total_integrand (fun x=>NY (u x))) a%:E:=hF _ hPositive.
have hNormOff:forall x,~C x ->NY (u x)=0.
  move=>x hx; by rewrite (hOff x hx) (real_seminorm_zero hNY.1).
have hEstimate:=@real_total_integral_supported_upper_bound R X mu hm C (fun x=>NY (u x)) a%:E delta
  (radon_compact_measurable hm hr hC) hDelta hI (fun x _=>hBound x)
  hNormOff.
have hFinite:mu C \is a fin_num by rewrite (ge0_fin_numE (measure_nonnegative hm C)); exact:(@radon_compact_finite R X mu hr C hC).
rewrite -(fineK hFinite) -EFinM lee_fin in hEstimate.
by exists a.
Qed.
