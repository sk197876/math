(** Federer (1969), 4.1.24, p. 382: integral
    currents are dense in the original integral-flat
    metric. Approximate both original rectifiable terms
    in mass by integral terms, keeping exactly K.
    The resulting integral current differs by a
    rectifiable pair of arbitrarily small total cost. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals constructive_ereal topology lra.
From Federer Require Import Hom Bilinear RealNormUP NormMetric NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  SmoothCompactSet CurrentSpaces CurrentBoundary CurrentMassSealed RectifiableCurrentApproximationUP
  RectifiableCurrentBasic RectifiableCurrentNegate RectifiableCurrentAlgebra
  RectifiableImageIntegral IntegralCurrentClassesUP IntegralCurrentInclusions
  IntegralCurrentAlgebra IntegralCurrentGroupSpaces AdditiveSubgroupRepresentationUP
  IntegralFlatSizeUP IntegralFlatSizeSealed IntegralFlatCurrentMetric.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Section IntegralCurrentFlatDensity.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Variable U:set (R_n R n).
Hypothesis hU:forall x,U x->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) U x.
Variable K:smooth_compact_set (inner_norm_real_norm (@euclidean_inner_productP R n)) U.
Local Notation C:=(@current_space R h2 n U hU m).
Local Notation M:=(fun d=>@CurrentMass.value R h2 n d U hU).
Local Notation bd:=(@current_boundary R h2 n m U hU).
Local Notation Rect:=(fun d=>@is_rectifiable_current_supported_in R h2 n d U hU K).
Local Notation Int:=(fun d=>@is_integral_current_supported_in R h2 n U hU d K).
Local Notation IF:=(@is_integral_flat_current_supported_in R h2 n U hU m K).
Local Notation Size:=(@IntegralFlatSize.value R h2 n m U hU K).

(** Source for [integral_current_dense_integral_flat_size]: the
    original density follows from mass density in both
    adjacent degrees, Federer 4.1.24, p. 382.
    The input itself may have infinite mass; only
    the original rectifiable decomposition terms are used. *)
Theorem integral_current_dense_integral_flat_size (T:C) (hT:IF T)
    (epsilon:R) (hEpsilon:0<epsilon):
  exists P:C,Int m P /\exists hDifference:IF (T-P),Size (T-P) hDifference<epsilon.
Proof.
have[A [B [hA [hB hEqual]]]]:=hT.
pose delta:=epsilon/3.
have hDelta:0<delta by rewrite /delta divr_gt0 //;lra.
have[P [hP hAP]]:=@integral_current_mass_dense_in_rectifiable
  R h2 n U hU K m A hA delta hDelta.
have[Q [hQ hBQ]]:=@integral_current_mass_dense_in_rectifiable
  R h2 n U hU K m.+1 B hB delta hDelta.
pose S:=P+bd Q.
have hS:Int m S.
  apply:integral_current_add_supported hP _.
  exact:(@integral_current_boundary_supported R h2 n U hU K m Q hQ).
have hResidA:Rect m (A-P).
  apply:rectifiable_current_add hA _;apply:rectifiable_current_negate.
  exact:integral_current_is_rectifiable_supported hP.
have hResidB:Rect m.+1 (B-Q).
  apply:rectifiable_current_add hB _;apply:rectifiable_current_negate.
  exact:integral_current_is_rectifiable_supported hQ.
have hDifferenceEqual:T-S=(A-P)+bd (B-Q).
  by rewrite /S hEqual (linB (hom_linear bd)) opprD addrACA.
have hDifference:IF (T-S).
  exists (A-P),(B-Q);split;first exact:hResidA.
  split;[exact:hResidB|exact:hDifferenceEqual].
have hLower:=@integral_flat_size_lower R h2 n m U hU K (T-S)
  (Size (T-S) hDifference) (@IntegralFlatSize.laws R h2 n m U hU K (T-S) hDifference)
  (A-P) (B-Q) hResidA hResidB hDifferenceEqual.
have hCost:(M m (A-P)%R+M m.+1 (B-Q)%R<epsilon%:E)%E.
  have hCaps:=leeD (ltW hAP) (ltW hBQ).
  apply:(le_lt_trans hCaps);rewrite -EFinD lte_fin /delta;lra.
exists S;split;first exact:hS.
exists hDifference;have h:=le_lt_trans hLower hCost;by rewrite lte_fin in h.
Qed.

Local Notation G:=(@integral_flat_current_metric R h2 n m U hU K).
Local Notation inc:=(@integral_flat_current_inclusion R h2 n m U hU K).
Local Notation hG:=(@integral_flat_current_group_laws R h2 n m U hU K).

(** Source for [integral_current_dense_integral_flat_metric]: the
    density conclusion holds on the actual original opaque
    integral-flat group and its exact metric, 4.1.24,
    p. 382, with no new choice of metric. *)
Theorem integral_current_dense_integral_flat_metric (z:G):
  forall epsilon:R,0<epsilon->exists w:G,Int m (inc w) /\mdist z w<epsilon.
Proof.
move=>epsilon hEpsilon.
have[P [hP [hDifference hSmall]]]:=integral_current_dense_integral_flat_size
  (additive_subgroup_representation_member hG z) hEpsilon.
have hPFlat:IF P.
  apply:rectifiable_current_is_integral_flat_supported.
  exact:integral_current_is_rectifiable_supported hP.
have[w hW]:=additive_subgroup_representation_full hG hPFlat.
exists w;split;first by rewrite hW.
have hDistance:=@integral_flat_current_distance_specification R h2 n m U hU K z w.
rewrite hW in hDistance.
have hValue:=integral_flat_size_unique hDistance
  (@IntegralFlatSize.laws R h2 n m U hU K (inc z-P) hDifference).
by rewrite hValue.
Qed.
End IntegralCurrentFlatDensity.
