(** Federer (1969), 4.1.11, p. 365: reduce the
    original two-point join to the unit-interval image.
    The right point-product law follows from the already
    proved point product and signed swap of 4.1.8,
    pp. 361–362. No product action is reproved. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormRegularity
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  EuclideanBlockLinearMaps EuclideanCartesianMap EuclideanCartesianSwapLinear
  CurrentSpaces CurrentDirac CurrentCartesianDomain CurrentCartesianProductSealed
  CurrentCartesianPointInclusion CurrentCartesianSwapDomain CurrentCartesianCompactCurrents
  CurrentCompactPointProduct CurrentCompactElementaryPushforwards CurrentCartesianCompactIdentities
  CurrentCompactPushforwardAlgebra CurrentCompactPushforwardImages SmoothFormPullbackComposition
  CurrentDegreeTransport CurrentDegreeTransportIdentity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section CurrentCompactRightPointProduct.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables m n j:nat.
Variables (A:set (R_n R m)) (B:set (R_n R n)).
Hypothesis hA:forall x,A x->norm_domain_interior (inner_norm (@euclidean_inner_productP R m)) A x.
Hypothesis hB:forall y,B y->norm_domain_interior (inner_norm (@euclidean_inner_productP R n)) B y.
Local Notation AB := (@euclidean_cartesian_set R m n A B).
Local Notation BA := (@euclidean_cartesian_set R n m B A).
Local Notation hAB := (@current_cartesian_domain_open R m n A B hA hB).
Local Notation hBA := (@current_cartesian_domain_open R n m B A hB hA).
Variable b:R_n R n.
Hypothesis hb:B b.
Local Notation inclusion := (@current_cartesian_point_inclusion R n m b).
Local Notation InclusionImage := (fun x hx=>@current_cartesian_point_inclusion_image R n m B A b hb x hx).
Local Notation InclusionClass := (@current_cartesian_point_inclusion_smooth R n m A hA b).
Local Notation swap := (@euclidean_cartesian_swap_map R n m).
Local Notation SwapImage := (fun z hz=>@current_cartesian_swap_image R n m B A z hz).
Local Notation SwapClass := (@euclidean_cartesian_swap_smooth R n m BA hBA).

(** Source for [current_cartesian_right_point_inclusion]:
    the original inclusion x mapped to (x,b), supporting
    the segment comparison in Federer 4.1.11, p. 365.
    This aliases the preceding point inclusion and swap. *)
Definition current_cartesian_right_point_inclusion (x:R_n R m):R_n R (m+n)%N:=
  swap (inclusion x).

(** Source for [current_cartesian_right_point_image]: the
    original right inclusion maps A into A times B,
    supporting Federer 4.1.11, p. 365. *)
Definition current_cartesian_right_point_image:
    forall x,A x->AB (current_cartesian_right_point_inclusion x):=
  @current_smooth_composite_image R m (n+m)%N (m+n)%N A BA AB
    inclusion swap InclusionImage SwapImage.

(** Source for [current_cartesian_right_point_smooth]: the
    original inclusion is smooth on the given open A,
    supporting Federer 4.1.11, p. 365. *)
Definition current_cartesian_right_point_smooth:
    norm_class_all_orders (inner_norm_real_norm (@euclidean_inner_productP R m))
      (inner_norm_real_norm (@euclidean_inner_productP R (m+n)%N)) A
      current_cartesian_right_point_inclusion:=
  @current_smooth_composite_class R m (n+m)%N (m+n)%N A BA
    inclusion swap InclusionImage InclusionClass SwapClass.

Variable T:@current_space R h2 m A hA j.
Hypothesis hT:@compact (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R m)))
  (@current_support R h2 m A hA j T).
Local Notation Point := (@dirac_current R h2 n B hB b).
Local Notation hPoint := (@current_compact_dirac_support R h2 n B hB b hb).
Local Notation Left := (@CartesianCurrentProduct.value R h2 n m 0%N j B A hB hA Point T).
Local Notation hLeft := (@current_cartesian_compact_currents R h2 n m 0%N j
  B A hB hA Point T hPoint hT).
Local Notation Included := (@current_compact_map_pushforward R h2 m (n+m)%N A BA hA hBA
  inclusion InclusionImage InclusionClass j T hT).
Local Notation hIncluded := (@current_compact_map_image_compact R h2 m (n+m)%N A BA hA hBA
  inclusion InclusionImage InclusionClass j T hT).

(** Source for [current_compact_right_point_product]: the
    original T times delta_b is the right-inclusion image
    of T, after the harmless identification j+0=j,
    supporting Federer 4.1.11, p. 365. Every compact
    actual T is allowed without a mass hypothesis. *)
Theorem current_compact_right_point_product:
  @current_degree_transport R h2 (m+n)%N AB hAB (j+0)%N j (addn0 j)
    (@CartesianCurrentProduct.value R h2 m n j 0%N A B hA hB T Point)=
  @current_compact_map_pushforward R h2 m (m+n)%N A AB hA hAB
    current_cartesian_right_point_inclusion current_cartesian_right_point_image
    current_cartesian_right_point_smooth j T hT.
Proof.
have hSwap:=@current_cartesian_compact_swap R h2 n m B A hB hA 0%N j Point T
  hLeft SwapImage SwapClass.
rewrite mul0n expr0 scale1r in hSwap.
have hAligned:=congr1 (@current_degree_transport R h2 (m+n)%N AB hAB (j+0)%N j (addn0 j)) hSwap.
rewrite current_degree_transport_roundtrip in hAligned.
have hPointProduct:=@current_compact_point_product R h2 n m j B A hB hA b hb T hT.
have hReplace:=@current_compact_map_pushforward_congruence R h2 (n+m)%N (m+n)%N
  BA AB hBA hAB swap SwapImage SwapClass j Left Included hLeft hIncluded hPointProduct.
have hCompose:=@current_compact_map_images_compose R h2 m (n+m)%N (m+n)%N
  A BA AB hA hBA hAB inclusion swap InclusionImage SwapImage InclusionClass SwapClass j T hT hIncluded.
exact:(eq_trans (esym hAligned) (eq_trans hReplace (esym hCompose))).
Qed.
End CurrentCompactRightPointProduct.
