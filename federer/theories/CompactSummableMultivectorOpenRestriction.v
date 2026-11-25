(** Federer (1969), 4.1.18, pp. 375–377:
    a compact summable ambient field whose literal
    carrier lies in U restricts to the original
    Omega_m(U). All pointwise values, the actual
    support, the L1 size and its density-current
    restriction are preserved exactly. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals constructive_ereal topology.
From Federer Require Import PartialFunctionUP NormBoundedLinearTopology Hom RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct ExteriorGrading
  CurrentDomain CurrentSpaces CurrentCoefficientNorms CurrentVectorCompleteness CurrentOpenRestriction
  CompactSummableFieldRepresentation CompactSummableMultivectors CompactSummableMultivectorDensity
  CompactSummableMultivectorAmbient CompactSummableCurrentZeroExtension
  OpenSubspaceMeasurablePullback OpenSubspaceSupportedIntegral EuclideanOpenDomainMeasure
  EuclideanLebesgueDimensions EuclideanDistributionMeasureContext IsotropyGroupTopology
  PartialFunctionBasic PartialFunctionExtensionUP MeasureLpMembershipUP
  TotalVectorNormIntegrability TotalVectorIntegralDomination MeasureIntegralUP SummableRealFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section OpenRestriction.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X:=(R_n R n).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation XT:=(real_norm_metric_space hNX).
Local Notation Full:=(fun _:X=>True).
Local Notation hFull:=(fun (x:X) (_:True)=>norm_full_domain_interior NX x).
Local Notation FT:=(current_domain R n Full).
Local Notation WF:=(@compact_summable_multivector_space R h2 n m Full hFull).
Local Notation valueF:=(@compact_summable_multivector_value R h2 n m Full hFull).
Local Notation rawF:=(@compact_summable_multivector_ambient_value R h2 n m Full hFull).
Local Notation sizeF:=(@compact_summable_multivector_size R h2 n m Full hFull).
Local Notation AF:=(@compact_summable_multivector_current R h2 n m Full hFull).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Local Notation UT:=(current_domain R n U).
Local Notation WU:=(@compact_summable_multivector_space R h2 n m U hU).
Local Notation valueU:=(@compact_summable_multivector_value R h2 n m U hU).
Local Notation rawU:=(@compact_summable_multivector_ambient_value R h2 n m U hU).
Local Notation sizeU:=(@compact_summable_multivector_size R h2 n m U hU).
Local Notation AU:=(@compact_summable_multivector_current R h2 n m U hU).
Local Notation V:=(exterior_power X m).
Local Notation VN:=(@current_vector_mass R h2 n m).
Local Notation hVN:=(@current_vector_mass_real_norm R h2 n m).
Local Notation mu:=(@euclidean_open_domain_measure R n U).
Local Notation hm:=(@euclidean_open_domain_measure_laws R n U hU).1.

(** Source for [compact_summable_multivector_open_restriction]:
    the original open-U field representation follows
    from the ambient compact representation without
    changing the support or the cost, supporting
    both propositions of 4.1.18, pp. 375–376.
    The current being represented need not have
    finite mass; only each Omega field is summable. *)
Theorem compact_summable_multivector_open_restriction
    (zeta:WF) (K:set XT) (hK:compact K) (hKU:K `<=` U)
    (hOff:forall x,~K x->rawF zeta x=0):
  exists xi:WU,
    valueU xi=(fun x:UT=>rawF zeta (set_val x)) /\
    rawU xi=rawF zeta /\sizeU xi=sizeF zeta /\
    @compact_summable_multivector_ambient_support R h2 n m U hU xi=
      @compact_summable_multivector_ambient_support R h2 n m Full hFull zeta /\
    (forall x:UT,~K (set_val x)->valueU xi x=0) /\
    AU xi=@current_open_restriction R h2 n m U Full hU hFull
      (fun _ _=>Logic.I) (AF zeta).
Proof.
pose f:=fun x:UT=>(rawF zeta (set_val x):real_norm_metric_space hVN).
have hFMeas:=@open_subspace_total_measurable_pullback R XT U
  (@euclidean_lebesgue_measure R n) (euclidean_lebesgue_is_measure R n)
  (real_norm_metric_space hVN) (rawF zeta)
  (@compact_summable_multivector_ambient_measurable R h2 n m Full hFull zeta).
have hOpen:@open XT U.
  rewrite openE=>x hx.
  exact:(@norm_domain_interior_neighbourhood R X NX hNX U x).1 (@hU x hx).
have hMeas:=@euclidean_distribution_measure_open R n U hOpen.
have hOffU:forall x,~U x->rawF zeta x=0.
  move=>x hx;apply:hOff=>hKx;exact:(hx (hKU x hKx)).
have hNormOff:forall x,~U x->VN (rawF zeta x)=0.
  by move=>x hx;rewrite (hOffU x hx) (real_seminorm_zero hVN.1).
have hIntegral:=@open_subspace_supported_total_integral R XT U
  (@euclidean_lebesgue_measure R n) (euclidean_lebesgue_is_measure R n) hMeas
  (fun x=>VN (rawF zeta x)) (sizeF zeta)%:E hNormOff
  (@compact_summable_multivector_ambient_integral R h2 n m Full hFull zeta).
have hLone:=@total_vector_lone_from_norm_integral R UT V VN hVN mu hm f (sizeF zeta)
  (@current_multivector_mass_separable R h2 n m) hFMeas hIntegral.
pose C:set UT:=set_val @^-1` K.
have hC:compact C:=@set_type_compact_preimage XT U K hK hKU.
have hFOff:forall x y,partial_function_graph (partial_function_total f) x y->~C x->y=0.
  move=>x y hValue hx;change (f x=y) in hValue.
  rewrite -hValue;exact:(@hOff (set_val x) hx).
have[xi [hExtend [_ [hCarrier [_ hSize]]]]]:=
  @compact_summable_partial_field_representative R UT V VN hVN mu hm
    (partial_function_total f) hLone.2.1 hLone.2.2.1 C hC hFOff.
have hValue:valueU xi=f.
  apply:funext=>x;exact:(@hExtend x (f x) (erefl (f x))).
have hRaw:rawU xi=rawF zeta.
  apply:funext=>x;case:(pselect (U x))=>hx.
  - pose x':UT:=exist _ x (mem_set hx).
    change (rawU xi (set_val x')=rawF zeta (set_val x')).
    by rewrite compact_summable_multivector_ambient_inside hValue.
  - rewrite (@compact_summable_multivector_ambient_outside R h2 n m U hU xi x hx).
    exact:esym (@hOffU x hx).
have hSizeExact:sizeU xi=sizeF zeta.
  have hNormValue:=@total_vector_lone_norm_value R UT V VN hVN mu hm f
    (sizeF zeta) hFMeas hIntegral.
  rewrite hNormValue in hSize.
  exact:esym (EFin_inj hSize).
have hFullValue:valueF zeta=(fun x:FT=>rawU xi (set_val x)).
  apply:funext=>x;rewrite hRaw.
  exact:esym (@compact_summable_multivector_ambient_inside R h2 n m Full hFull zeta x).
exists xi;split;first exact:hValue.
split;first exact:hRaw.
split;first exact:hSizeExact.
split;first by rewrite /compact_summable_multivector_ambient_support hRaw.
split;first exact:hCarrier.
exact:(@compact_summable_current_zero_extension R h2 n m U hU xi zeta hFullValue).
Qed.
End OpenRestriction.
