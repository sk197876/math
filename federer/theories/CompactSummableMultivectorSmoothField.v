(** Federer (1969), 4.1.18, pp. 375–376: compact
    smooth multivector fields on the original open U
    lie in Omega_m(U). The actual values are unchanged.
    Reuse the earlier compact continuous L1 membership,
    the original relative topology and the opaque
    compact-field carrier. Empty U is allowed. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric NormDifferentialUP NormRegularity
  NormClassZeroTopology InnerNorm HilbertFormCompactness GrassmannAbbreviations
  EuclideanInnerProduct ExteriorGrading CurrentDomain CurrentVectorSpaces
  CurrentCoefficientNorms CurrentVectorCompleteness SmoothFunctionSpaceUP
  SmoothCompactSet CompactSupportFunctionUP CompactContinuousVectorFields
  IsotropyGroupTopology SubtypeCompactHausdorff EuclideanOpenDomainMeasure
  CompactSummableFieldContinuous CompactSummableMultivectors.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section SmoothField.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X:=(R_n R n).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation XT:=(real_norm_metric_space hNX).
Local Notation V:=(exterior_power X m).
Local Notation N:=(@current_vector_mass R h2 n m).
Local Notation hN:=(@current_vector_mass_real_norm R h2 n m).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Local Notation UT:=(current_domain R n U).
Local Notation E:=(@current_vector_smooth_space R h2 n U hU m).
Local Notation ev:=(@current_vector_smooth_value R h2 n U hU m).
Local Notation hE:=(@current_vector_smooth_space_laws R h2 n U hU m).
Local Notation mu:=(@euclidean_open_domain_measure R n U).
Local Notation hm:=(@euclidean_open_domain_measure_laws R n U hU).1.
Local Notation hr:=(@euclidean_open_domain_measure_laws R n U hU).2.
Local Notation W:=(@compact_summable_multivector_space R h2 n m U hU).
Local Notation value:=(@compact_summable_multivector_value R h2 n m U hU).

(** Source for [compact_summable_multivector_smooth_field]:
    actual compact smooth coefficient fields in the
    first proposition and the representation iteration
    of Federer 4.1.18, pp. 375–376. Their
    original pointwise U-values are preserved exactly,
    including the empty domain and every exterior degree. *)
Theorem compact_summable_multivector_smooth_field (f:E)
    (K:smooth_compact_set hNX U):
  (forall x,U x->~smooth_compact_carrier K x->ev f x=0)->
  exists xi:W,value xi=(fun x:UT=>ev f (set_val x)).
Proof.
move=>hOff.
pose w:=fun x:UT=>ev f (set_val x).
have hContinuous:continuous (fun x:UT=>(w x:real_norm_metric_space hN)).
  exact:(@norm_class_zero_restriction_continuous R X V NX N hNX hN U (ev f)
    (norm_class_continuous (smooth_function_evaluation_smooth hE f 0%N))).
pose C:set UT:=set_val @^-1` smooth_compact_carrier K.
have hCompact:compact C.
  exact:(@set_type_compact_preimage XT U (smooth_compact_carrier K)
    (smooth_compact_is_compact K) (smooth_compact_in_domain K)).
have hClosed:closed C.
  exact:(compact_closed (@set_type_hausdorff XT U (@metric_hausdorff R XT)) hCompact).
have hNormOff:forall x,~C x->N (w x)=0.
  move=>x hx;rewrite /w (hOff (set_val x) (set_valP x) hx).
  exact:(real_seminorm_zero hN.1).
have hW:compact_continuous_vector_fields hN w.
  split;first exact:hContinuous.
  exact:(@real_function_compact_support_in_closed_set R UT (fun x=>N (w x)) C
    hCompact hClosed hNormOff).
exact:(@compact_summable_continuous_field_representative R UT V N hN
  (@current_multivector_mass_separable R h2 n m) mu hm hr w hW).
Qed.
End SmoothField.
