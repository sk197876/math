(** Federer (1969), 4.1.18, p. 375: a compact
    carrier for xi is also a support bound for the
    actual current Lebesgue^n wedge xi. The old support
    criterion and literal integral action suffice; no
    flatness or smoothness is assumed in this support step. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals constructive_ereal topology.
From Federer Require Import Hom TensorUP Bilinear RealNormUP NormMetric
  NormDifferentialUP InnerNorm HilbertFormCompactness GrassmannAbbreviations
  EuclideanInnerProduct ExteriorGrading AlternatingForms AlternatingPairing
  CurrentDomain CurrentSpaces CurrentCoefficientNorms CurrentSupportGeometry SmoothCompactSet
  SmoothFunctionSupport CompactSummableFieldLaws CompactSummableMultivectors
  CompactSummableMultivectorDensity CompactSummableMultivectorLinear
  EuclideanOpenDomainMeasure MeasureUP MeasureIntegralUP MeasureIntegralUniqueness
  SummableRealFunctionUP LatticeL1ApproximationLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Support.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X:=(R_n R n).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation XT:=(real_norm_metric_space hNX).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Local Notation UT:=(current_domain R n U).
Local Notation W:=(@compact_summable_multivector_space R h2 n m U hU).
Local Notation value:=(@compact_summable_multivector_value R h2 n m U hU).
Local Notation image:=(@compact_summable_multivector_current R h2 n m U hU).
Local Notation support:=(@current_support R h2 n U hU m).
Local Notation ev:=(@current_test_value R h2 n U hU m).
Local Notation mu:=(@euclidean_open_domain_measure R n U).
Local Notation hm:=(proj1 (@euclidean_open_domain_measure_laws R n U hU)).

(** Source for [compact_summable_multivector_current_support]:
    the support bound used in the first proposition
    of Federer 4.1.18, p. 375. Every original
    compact carrier and every summable field are allowed. *)
Theorem compact_summable_multivector_current_support
    (xi:W) (K:smooth_compact_set hNX U)
    (hOff:forall x:UT,~smooth_compact_carrier K (set_val x)->value xi x=0):
  support (image xi) `<=` smooth_compact_carrier K.
Proof.
apply:(@current_support_compact_criterion R h2 n m U hU K (image xi)).2
  =>psi hPsi.
have hPoint:(fun x:UT=>pairing (value xi x) (ev psi (set_val x)))=
    (fun _:UT=>0:R).
  apply:funext=>x.
  case:(pselect (smooth_compact_carrier K (set_val x)))=>hK.
  - have hZero:ev psi (set_val x)=0.
      apply:contrapT=>hNonzero.
      have hTest:@current_test_support R h2 n m U hU psi (set_val x).
        split;first exact:set_valP x.
        exact:(@subset_closure XT _ (set_val x) hNonzero).
      exact:((@hPsi (set_val x) hTest).2 hK).
    rewrite hZero.
    exact:(lin0 ((@pairing_bilinear R X R^o m).2 (value xi x))).
  - rewrite (hOff x hK).
    exact:(lin0 ((@pairing_bilinear R X R^o m).1 (ev psi (set_val x)))).
have hAction:=@compact_summable_multivector_current_action R h2 n m U hU xi psi.
rewrite hPoint in hAction.
exact:(congr1 (@fine R) (measure_integral_unique hAction
  (@real_total_zero_integral R UT mu hm))).
Qed.

(** Source for [compact_summable_multivector_compact_index]:
    Omega_m's compact support gives an actual compact
    index inside the original U, Federer 4.1.18,
    p. 375. It also bounds the resulting current.
    Empty U requires no selected point. *)
Theorem compact_summable_multivector_compact_index (xi:W):
  exists K:smooth_compact_set hNX U,
    (forall x:UT,~smooth_compact_carrier K (set_val x)->value xi x=0) /\
    support (image xi) `<=` smooth_compact_carrier K.
Proof.
have[C [hC hOff]]:=@compact_summable_field_compact R UT
  (exterior_power X m) (@current_vector_mass R h2 n m)
  (@current_vector_mass_real_norm R h2 n m) mu hm xi.
pose K0:set X:=set_val @` C.
have hInclusion:continuous (set_val:UT->XT) by exact:initial_continuous.
have hK0:@compact XT K0.
  exact:(continuous_compact (continuous_subspaceT hInclusion) hC).
have hKU:K0 `<=` U.
  move=>y [x hx <-];exact:set_valP x.
pose K:=@Build_smooth_compact_set R X NX hNX U K0 hKU hK0.
have hField:forall x:UT,~smooth_compact_carrier K (set_val x)->value xi x=0.
  move=>x hx;apply:(hOff x)=>hCx.
  apply:hx;by exists x.
exists K;split;first exact:hField.
exact:compact_summable_multivector_current_support hField.
Qed.
End Support.
