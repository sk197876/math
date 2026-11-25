(** Federer (1969), 4.1.18, pp. 375–376: the
    original compact summable field on U has its
    literal zero extension to R^n. Values, the
    mass integral and compact support inside U are
    preserved. This supplies the original ordinary
    field convolutions without assuming U is inhabited. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws NormBoundedLinearTopology
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct ExteriorGrading
  CurrentDomain CurrentCoefficientNorms CurrentVectorCompleteness SmoothCompactSet
  CompactSummableFieldSealed CompactSummableFieldLaws CompactSummableFieldIntegral
  CompactSummableFieldRepresentation CompactSummableMultivectors EuclideanOpenDomainMeasure
  EuclideanFullDomainMeasure EuclideanFullDomainCompactFunctions EuclideanLebesgueDimensions
  EuclideanDistributionMeasureContext CompactContinuousVectorZeroExtension
  OpenSubspaceExtension OpenSubspaceTotalZeroExtension IsotropyGroupTopology
  MeasureUP MeasurePushforward MeasureIntegralUP MeasureIntegralGraphEquivalence MeasureIntegralUniqueness
  MeasurableFunctionUP MeasurableGraphEquivalence PushforwardMeasurableFunctions
  PartialFunctionUP PartialFunctionBasic PartialFunctionPrecomposition PartialFunctionExtensionUP MeasureLpMembershipUP
  SummableRealFunctionUP TotalVectorNormIntegrability TotalVectorIntegralDomination
  FunctionLatticeUP CompactSupportFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CompactSummableMultivectorAmbient.
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
Local Notation V:=(exterior_power X m).
Local Notation VN:=(@current_vector_mass R h2 n m).
Local Notation hVN:=(@current_vector_mass_real_norm R h2 n m).
Local Notation Leb:=(@euclidean_lebesgue_measure R n).
Local Notation hLeb:=(euclidean_lebesgue_is_measure R n).
Local Notation alpha:=(@euclidean_open_domain_measure R n Full).
Local Notation hAlpha:=(@euclidean_open_domain_measure_laws R n Full hFull).1.
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Local Notation UT:=(current_domain R n U).
Local Notation mu:=(@euclidean_open_domain_measure R n U).
Local Notation hm:=(@euclidean_open_domain_measure_laws R n U hU).1.
Local Notation W:=(@compact_summable_multivector_space R h2 n m U hU).
Local Notation value:=(@compact_summable_multivector_value R h2 n m U hU).
Local Notation size:=(@compact_summable_multivector_size R h2 n m U hU).
Variable xi:W.

(** Source for [compact_summable_multivector_ambient_value]:
    the original field extended by zero before
    Phi_epsilon*xi in Federer 4.1.18, p. 375. *)
Definition compact_summable_multivector_ambient_value:X->V:=
  @compact_vector_open_extension R XT U V (value xi).
Local Notation f:=compact_summable_multivector_ambient_value.

(** Source for [compact_summable_multivector_ambient_inside]:
    every original U-value is retained exactly in
    the ambient extension, supporting 4.1.18, p. 375. *)
Lemma compact_summable_multivector_ambient_inside (x:UT):f (set_val x)=value xi x.
Proof. exact:compact_vector_open_extension_value. Qed.

(** Source for [compact_summable_multivector_ambient_outside]:
    zero is used outside U in the original
    field convolution of Federer 4.1.18, p. 375. *)
Lemma compact_summable_multivector_ambient_outside x:~U x->f x=0.
Proof. exact:compact_vector_open_extension_outside. Qed.

(** Source for [compact_summable_multivector_ambient_measurable]:
    the original measurable Omega field stays measurable
    under zero extension, supporting 4.1.18, p. 375. *)
Theorem compact_summable_multivector_ambient_measurable:
  is_measure_measurable_function Leb
    (partial_function_total (fun x=>(f x:real_norm_metric_space hVN))).
Proof.
have hOpen:@open XT U.
  rewrite openE=>x hx;exact:(norm_domain_interior_neighbourhood hNX U x).1 (@hU x hx).
have hMeas:=@compact_summable_field_measurable R UT V VN hVN mu hm xi.
exact:(@open_subspace_total_zero_extension_measurable R XT U Leb hLeb
  (@euclidean_distribution_measure_open R n U hOpen) V VN hVN (value xi) hMeas.1).
Qed.

(** Source for [compact_summable_multivector_ambient_integral]:
    the ambient mass integral is precisely the original
    U integral used in J, Federer 4.1.18, p. 375. *)
Theorem compact_summable_multivector_ambient_integral:
  is_measure_integral Leb (real_total_integrand (fun x=>VN (f x))) (size xi)%:E.
Proof.
have hOpen:@open XT U.
  rewrite openE=>x hx;exact:(norm_domain_interior_neighbourhood hNX U x).1 (@hU x hx).
have hOriginal:=@compact_summable_field_size_integral R UT V VN hVN mu hm xi.
have hNorm:(fun x:XT=>VN (f x))=@open_extension R XT U (fun x:UT=>VN (value xi x)).
  exact:(@compact_vector_open_extension_norm R XT U V VN hVN (value xi)).
rewrite hNorm.
exact:(@open_subspace_total_zero_extension_integral R XT U Leb hLeb
  (@euclidean_distribution_measure_open R n U hOpen)
  (fun x:UT=>VN (value xi x)) (size xi)%:E hOriginal).
Qed.

(** Source for [compact_summable_multivector_ambient_lone]:
    the actual zero extension has its original
    L1 membership, supporting ordinary convolution
    in Federer 4.1.18, p. 375. *)
Theorem compact_summable_multivector_ambient_lone:
  is_measure_lp_function Leb 1
    (partial_function_total (fun x=>(f x:real_norm_metric_space hVN))).
Proof.
exact:(@total_vector_lone_from_norm_integral R X V VN hVN Leb hLeb f (size xi)
  (@current_multivector_mass_separable R h2 n m)
  compact_summable_multivector_ambient_measurable compact_summable_multivector_ambient_integral).
Qed.

(** Source for [compact_summable_multivector_ambient_carrier]:
    zero extension has an actual compact carrier inside
    the original U, supporting the exact support tubes
    in Federer 4.1.18, pp. 375–376. *)
Theorem compact_summable_multivector_ambient_carrier:
  exists K:set XT,compact K /\K `<=` U /\forall x,~K x->f x=0.
Proof.
have[C [hC hOff]]:=@compact_summable_field_compact R UT V VN hVN mu hm xi.
pose K:set XT:=set_val @` C.
have hK:compact K.
  exact:continuous_compact (continuous_subspaceT (@set_type_val_continuous XT U)) hC.
exists K;split;first exact:hK.
split;first by move=>x [y _ <-];exact:set_valP y.
move=>x hx;case:(pselect (U x))=>hUx;last exact:compact_summable_multivector_ambient_outside hUx.
pose y:UT:=exist _ x (mem_set hUx).
change (f (set_val y)=0);rewrite compact_summable_multivector_ambient_inside.
apply:hOff=>hy;apply:hx;exists y;by [].
Qed.

(** Source for [compact_summable_multivector_ambient_support]:
    the original support is compact inside U,
    including representatives with null nonzero values,
    supporting the literal delta tube in 4.1.18, p. 375. *)
Definition compact_summable_multivector_ambient_support:set XT:=
  real_function_support (fun x:XT=>VN (f x)).

(** Source for [compact_summable_multivector_ambient_support_laws]:
    the actual support, rather than an arbitrary larger
    carrier, is compact and lies in U in the
    first proposition of Federer 4.1.18, p. 375. *)
Theorem compact_summable_multivector_ambient_support_laws:
  compact compact_summable_multivector_ambient_support /\
  compact_summable_multivector_ambient_support `<=` U /\
  forall x,~compact_summable_multivector_ambient_support x->f x=0.
Proof.
have[K [hK [hKU hOff]]]:=compact_summable_multivector_ambient_carrier.
have hClosed:closed K:=compact_closed (@metric_hausdorff R XT) hK.
have hSupport:compact_summable_multivector_ambient_support `<=` K.
  apply:(@real_function_support_in_closed_set R XT (fun x:XT=>VN (f x)) K hClosed)=>x hx.
  by rewrite (hOff x hx) (real_seminorm_zero hVN.1).
split.
- exact:(@subclosed_compact XT compact_summable_multivector_ambient_support K
    (@real_function_support_closed R XT (fun x:XT=>VN (f x))) hK hSupport).
- split;first exact:subset_trans hSupport hKU.
  move=>x hx;apply:hVN.2.
  exact:(@real_function_zero_off_support R XT (fun x:XT=>VN (f x)) x hx).
Qed.

(** Source for [compact_summable_multivector_ambient_representative]:
    the zero extension is represented in the same
    opaque Omega space on R^n, with every value
    and its original L1 size unchanged, supporting
    Federer 4.1.18, pp. 375–376. *)
Theorem compact_summable_multivector_ambient_representative:
  exists zeta:@compact_summable_multivector_space R h2 n m Full hFull,
    @compact_summable_multivector_value R h2 n m Full hFull zeta=
      (fun x:FT=>f (set_val x)) /\
    @compact_summable_multivector_size R h2 n m Full hFull zeta=size xi.
Proof.
pose g:=fun x:FT=>(f (set_val x):real_norm_metric_space hVN).
have hFMeas:=compact_summable_multivector_ambient_measurable.
have hPull:is_measure_measurable_function Leb
    (partial_function_precompose (@euclidean_full_domain_point R n) (partial_function_total g)).
  exact:hFMeas.
have hGMeas:=@pushforward_function_measurable_from_composition R X FT
  (real_norm_metric_space hVN) Leb (@euclidean_full_domain_point R n) _ hPull.
rewrite -euclidean_full_domain_measure_image in hGMeas.
have hNorm:=@euclidean_full_domain_real_integral R n (fun x=>VN (f x))
  (size xi)%:E compact_summable_multivector_ambient_integral.
have hLone:=@total_vector_lone_from_norm_integral R FT V VN hVN alpha hAlpha g (size xi)
  (@current_multivector_mass_separable R h2 n m) hGMeas hNorm.
have[K [hK [_ hOff]]]:=compact_summable_multivector_ambient_carrier.
pose C:set FT:=set_val @^-1` K.
have hC:compact C:=@set_type_compact_preimage XT Full K hK (fun _ _=>Logic.I).
have hGOff:forall x y,partial_function_graph (partial_function_total g) x y->~C x->y=0.
  move=>x y hValue hx;change (g x=y) in hValue.
  rewrite -hValue;exact:hOff (set_val x) hx.
have[zeta [hExtend [_ [_ [_ hSize]]]]]:=@compact_summable_partial_field_representative R FT V VN hVN
  alpha hAlpha (partial_function_total g) hLone.2.1 hLone.2.2.1 C hC hGOff.
exists zeta;split.
- apply:funext=>x;exact:(@hExtend x (g x) (erefl (g x))).
- have hNormValue:=@total_vector_lone_norm_value R FT V VN hVN alpha hAlpha g
    (size xi) hGMeas hNorm.
  rewrite hNormValue in hSize.
  exact:esym (EFin_inj hSize).
Qed.
End CompactSummableMultivectorAmbient.
