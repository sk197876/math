(** Federer (1969), 4.1.11, p. 365: first-projection
    evaluations for the original join boundary calculation.
    Compact cutoffs and the earlier mixed-degree product laws
    suffice; no measure representation is assumed. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom Bilinear RealNormUP NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct EuclideanCartesianMap CurrentSpaces
  CurrentCartesianDomain CurrentCartesianTestProductSealed CurrentDegreeTransport
  CurrentDegreeTransportIdentity CurrentDegreeTransportComposition CurrentEvaluation
  CurrentPointEvaluation CurrentCartesianMixedAnnihilator CurrentCartesianProductSealed
  NormMetric SmoothCompactSet FiniteCoordinates EuclideanBlockLinearMaps CurrentScalarCutoffs
  AlternatingZero CurrentCartesianProjections CurrentCartesianCompactCurrents CurrentCompactMapProper CurrentCartesianFirstCutoffReplacement CurrentCartesianFirstProjection NormClassOneUP NormRegularity
  CurrentPushforwardSealed CurrentCompactSmoothValue CurrentCompactSmoothAgreement.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section CurrentCartesianFirstProjectionZero.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables m n:nat.
Variables (A:set (R_n R m)) (B:set (R_n R n)).
Hypothesis hA:forall a,A a->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R m)) A a.
Hypothesis hB:forall b,B b->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) B b.
Local Notation AB := (@euclidean_cartesian_set R m n A B).
Local Notation hAB := (@current_cartesian_domain_open R m n A B hA hB).
Local Notation DA := (fun k=>@current_test_space R h2 m A hA k).
Local Notation DB := (fun k=>@current_test_space R h2 n B hB k).
Local Notation CC := (fun r=>@current_space R h2 (m+n) AB hAB r).
Local Notation CA := (fun r=>@current_space R h2 m A hA r).
Local Notation CB := (fun r=>@current_space R h2 n B hB r).
Local Notation ec := (fun r=>@current_value R h2 (m+n) AB hAB r).
Local Notation ea := (fun r=>@current_value R h2 m A hA r).
Local Notation eb := (fun r=>@current_value R h2 n B hB r).
Local Notation Tr := (fun a b (e:a=b)=>@current_test_degree_transport R h2 (m+n) AB hAB a b e).
Local Notation CTr := (fun a b (e:a=b)=>@current_degree_transport R h2 (m+n) AB hAB a b e).
Local Notation Pure := (fun k l=>@CartesianTestProduct.value R h2 m n A B hA hB k l).
Local Notation Product := (fun i j=>@CartesianCurrentProduct.value R h2 m n i j A B hA hB).


Local Notation X := (R_n R m).
Local Notation Y := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R m)).
Local Notation NY := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R m)).
Local Notation hNY := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation p := (@euclidean_first_block_map R m n).
Local Notation Image := (fun z (hz:AB z)=>hz.1).
Local Notation hSmooth := (@current_cartesian_first_projection_smooth R m n A B hA hB).
Local Notation ATr := (fun a b (e:a=b)=>@current_degree_transport R h2 m A hA a b e).
Local Open Scope classical_set_scope.
Variable i:nat.
Variable S:CA i.
Variable T:CB 0%N.
Hypothesis hS:@compact (real_norm_metric_space hNX) (@current_support R h2 m A hA i S).
Hypothesis hT:@compact (real_norm_metric_space hNY) (@current_support R h2 n B hB 0%N T).

(** Source for [current_cartesian_first_projection_zero]:
    the original first-projection image is T(1)S when j=0,
    giving the endpoint term in Federer 4.1.11, p. 365.
    T(1) is the actual compact smooth-dual total. *)
Theorem current_cartesian_first_projection_zero:
  @current_cartesian_compact_first_projection R h2 m n A B hA hB
    i 0%N S T hS hT i (addn0 i)=
    (@current_compact_total R h2 n B hB T hT)*:S.
Proof.
pose KT:=@Build_smooth_compact_set R Y NY hNY B
  (@current_support R h2 n B hB 0%N T) (fun y hy=>hy.1) hT.
have[gamma [W [hW [hTW [hWB hGamma]]]]]:=@current_compact_scalar_cutoff R h2 n B hB KT.
have hScalar:=@current_compact_total_cutoff R h2 n B hB T hT gamma W hW hTW hWB hGamma.
apply:(@current_values_extensional R h2 m i A hA)=>alpha.
have hAction:=@current_cartesian_first_projection_cutoff_action R h2 m n A B hA hB
  i 0%N S T hS hT i (addn0 i) gamma W hW hTW hGamma alpha.
rewrite current_test_degree_transport_identity
  ((@CartesianCurrentProduct.laws R h2 m n i 0%N A B hA hB S T).1 alpha gamma)
  hScalar in hAction.
have hRight:ea i ((@current_compact_total R h2 n B hB T hT)*:S) alpha=
    (@current_compact_total R h2 n B hB T hT)*ea i S alpha.
  change (@current_point_evaluation R h2 m i A hA alpha
    ((@current_compact_total R h2 n B hB T hT)*:S)=
    (@current_compact_total R h2 n B hB T hT)*:
      @current_point_evaluation R h2 m i A hA alpha S).
  exact:(linZ (hom_linear (@current_point_evaluation R h2 m i A hA alpha))
    (@current_compact_total R h2 n B hB T hT) S).
by rewrite hAction hRight mulrC.
Qed.
End CurrentCartesianFirstProjectionZero.
