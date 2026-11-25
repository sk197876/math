(** Federer (1969), 4.1.24, p. 380: addition
    preserves the complete original image-witness class.
    Put independent source dimensions in disjoint affine
    slices, glue their maps on open compact neighbourhoods,
    restrict each old source over its own piece,
    and add its integral polyhedral placements. All
    neighbourhoods and bounds are proved earlier; the
    original target may be nonconvex or empty. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions
  classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  NormBoundedLinearTopology InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct LipschitzUP LipschitzBasic
  SmoothCompactSet CurrentSpaces FlatCurrentsUP PolyhedralCurrentAlgebra PolyhedralCurrentFlat
  RectifiableCurrentApproximationUP RectifiableSourceEmbeddings RectifiableSourceImageGluing
  CompactLipschitzGluingUP LipschitzSourceCompactRestriction PolyhedralSourcePlacement
  RectifiableCommonSourceImages.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section RectifiableImageAdd.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Variable U:set (R_n R n).
Hypothesis hU:forall x,U x->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) U x.
Variable K:smooth_compact_set (inner_norm_real_norm (@euclidean_inner_productP R n)) U.
Local Notation C:=(@current_space R h2 n U hU m).
Local Notation Approx:=(@is_rectifiable_image_approximant R h2 n m U hU K).

(** Source for [rectifiable_image_approximant_add]: one original
    integral polyhedral Lipschitz image represents the sum
    of any two defining images, Federer 4.1.24,
    p. 380. The arbitrary source dimensions and the
    exact target K are retained. *)
Theorem rectifiable_image_approximant_add (T S:C):Approx T->Approx S->Approx (T+S).
Proof.
move=>[d0 [Z0 [hZ0 [C0 [f0 [hImage0 [hLip0 [P0 [hP0 [hC0K hValue0]]]]]]]]]]
  [d1 [Z1 [hZ1 [C1 [f1 [hImage1 [hLip1 [P1 [hP1 [hC1K hValue1]]]]]]]]]].
pose d:=(1+(d0+d1))%N.
pose X:=R_n R d.
pose NX:=inner_norm (@euclidean_inner_productP R d).
pose hNX:=inner_norm_real_norm (@euclidean_inner_productP R d).
pose E0:=@rectifiable_source_left R d0 d1.
pose E1:=@rectifiable_source_right R d0 d1.
pose J0:=@rectifiable_left_source_compact R d0 d1 Z0 C0.
pose J1:=@rectifiable_right_source_compact R d0 d1 Z1 C1.
have[W0 [W1 [F hGlue]]]:=@rectifiable_sources_image_gluing_exists
  R d0 d1 n Z0 Z1 U hZ0 hZ1 C0 C1 f0 f1
  hImage0 hImage1 hLip0 hLip1.
pose W:set X:=W0 `|` W1.
have hWOpen:@open (real_norm_metric_space hNX) W.
  exact:openU (compact_lipschitz_gluing_open0 hGlue)
    (compact_lipschitz_gluing_open1 hGlue).
have hW:forall x,W x->norm_domain_interior NX W x.
  move=>x hx;apply:(@norm_domain_interior_neighbourhood R X NX hNX W x).2.
  exact:open_nbhs_nbhs (conj hWOpen hx).
have hW0:forall x,W0 x->norm_domain_interior NX W0 x.
  move=>x hx;apply:(@norm_domain_interior_neighbourhood R X NX hNX W0 x).2.
  exact:open_nbhs_nbhs (conj (compact_lipschitz_gluing_open0 hGlue) hx).
have hW1:forall x,W1 x->norm_domain_interior NX W1 x.
  move=>x hx;apply:(@norm_domain_interior_neighbourhood R X NX hNX W1 x).2.
  exact:open_nbhs_nbhs (conj (compact_lipschitz_gluing_open1 hGlue) hx).
have hContains0:forall x,smooth_compact_carrier J0 x->W0 x.
  exact:compact_lipschitz_gluing_contains0 hGlue.
have hContains1:forall x,smooth_compact_carrier J1 x->W1 x.
  exact:compact_lipschitz_gluing_contains1 hGlue.
have hFImage:forall x,W x->U (F x).
  exact:compact_lipschitz_gluing_image hGlue.
have hFLip:@is_metric_lipschitz R (real_norm_metric_space hNX)
    (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n))) W F.
  exact:compact_lipschitz_gluing_bound hGlue.
have hFLip0:@is_metric_lipschitz R (real_norm_metric_space hNX)
    (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n))) W0 F.
  have[L [hL hBound]]:=hFLip;exists L;split;first exact:hL.
  exact:(@metric_lipschitz_bound_restrict R (real_norm_metric_space hNX)
    (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n))) W W0 F L (fun x hx=>or_introl hx) hBound).
have hFLip1:@is_metric_lipschitz R (real_norm_metric_space hNX)
    (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n))) W1 F.
  have[L [hL hBound]]:=hFLip;exists L;split;first exact:hL.
  exact:(@metric_lipschitz_bound_restrict R (real_norm_metric_space hNX)
    (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n))) W W1 F L (fun x hx=>or_intror hx) hBound).
have hE0Z:@is_metric_lipschitz R
    (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R d0)))
    (real_norm_metric_space hNX) Z0 E0.
  have[L [hL hBound]]:=@rectifiable_source_left_lipschitz R d0 d1.
  exists L;split;first exact:hL.
  exact:(@metric_lipschitz_bound_restrict R (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R d0)))
    (real_norm_metric_space hNX) setT Z0 E0 L (fun _ _=>Logic.I) hBound).
have hE1Z:@is_metric_lipschitz R
    (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R d1)))
    (real_norm_metric_space hNX) Z1 E1.
  have[L [hL hBound]]:=@rectifiable_source_right_lipschitz R d0 d1.
  exists L;split;first exact:hL.
  exact:(@metric_lipschitz_bound_restrict R (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R d1)))
    (real_norm_metric_space hNX) setT Z1 E1 L (fun _ _=>Logic.I) hBound).
have hC0W0:forall x,smooth_compact_carrier C0 x->W0 (E0 x).
  move=>x hx;apply:hContains0;change ((E0 @` smooth_compact_carrier C0) (E0 x)).
  by exists x.
have hC1W1:forall x,smooth_compact_carrier C1 x->W1 (E1 x).
  move=>x hx;apply:hContains1;change ((E1 @` smooth_compact_carrier C1) (E1 x)).
  by exists x.
have[A0 [hA0 [hC0A0 [hA0Z0 [hA0W0 hComposite0]]]]]:=
  @lipschitz_source_compact_neighbourhood_restriction R d0 d n
    Z0 hZ0 C0 W0 hW0 E0 F hE0Z hFLip0 hC0W0.
have[A1 [hA1 [hC1A1 [hA1Z1 [hA1W1 hComposite1]]]]]:=
  @lipschitz_source_compact_neighbourhood_restriction R d1 d n
    Z1 hZ1 C1 W1 hW1 E1 F hE1Z hFLip1 hC1W1.
have hLW:smooth_compact_carrier J0 `|` smooth_compact_carrier J1 `<=` W.
  move=>x [hx|hx];[left;exact:@hContains0 x hx|right;exact:@hContains1 x hx].
pose L:=@Build_smooth_compact_set R X NX hNX W
  (smooth_compact_carrier J0 `|` smooth_compact_carrier J1) hLW
  (@compactU (real_norm_metric_space hNX) _ _
    (smooth_compact_is_compact J0) (smooth_compact_is_compact J1)).
have hC0L:forall x,smooth_compact_carrier C0 x->smooth_compact_carrier L (E0 x).
  move=>x hx;left;change ((E0 @` smooth_compact_carrier C0) (E0 x));by exists x.
have hC1L:forall x,smooth_compact_carrier C1 x->smooth_compact_carrier L (E1 x).
  move=>x hx;right;change ((E1 @` smooth_compact_carrier C1) (E1 x));by exists x.
have hValues0:forall x,A0 x->F (E0 x)=f0 x.
  move=>x hx.
  have h:=compact_lipschitz_gluing_values0 hGlue (hA0W0 x hx).
  rewrite rectifiable_source_left_inverse in h;exact:h.
have hValues1:forall x,A1 x->F (E1 x)=f1 x.
  move=>x hx.
  have h:=compact_lipschitz_gluing_values1 hGlue (hA1W1 x hx).
  rewrite rectifiable_source_right_inverse in h;exact:h.
have hLK:forall x,smooth_compact_carrier L x->smooth_compact_carrier K (F x).
  move=>x [[z hz <-]|[z hz <-]].
  - have h:=compact_lipschitz_gluing_values0 hGlue (hC0W0 z hz).
    rewrite rectifiable_source_left_inverse in h;rewrite h;exact:hC0K z hz.
  - have h:=compact_lipschitz_gluing_values1 hGlue (hC1W1 z hz).
    rewrite rectifiable_source_right_inverse in h;rewrite h;exact:hC1K z hz.
have hE0A:@is_metric_lipschitz R
    (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R d0)))
    (real_norm_metric_space hNX) A0 E0.
  have[B [hB hBound]]:=hE0Z;exists B;split;first exact:hB.
  exact:(@metric_lipschitz_bound_restrict R (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R d0)))
    (real_norm_metric_space hNX) Z0 A0 E0 B hA0Z0 hBound).
have hE1A:@is_metric_lipschitz R
    (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R d1)))
    (real_norm_metric_space hNX) A1 E1.
  have[B [hB hBound]]:=hE1Z;exists B;split;first exact:hB.
  exact:(@metric_lipschitz_bound_restrict R (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R d1)))
    (real_norm_metric_space hNX) Z1 A1 E1 B hA1Z1 hBound).
have[Q0 [hQ0 hRecover0]]:=@polyhedral_source_placement_exists R h2 d0 d n m
  Z0 A0 W U hZ0 hA0 hW hU hA0Z0 C0 hC0A0 L f0 E0 F hImage0 hLip0
  (@rectifiable_source_left_affine R d0 d1) (fun x hx=>or_introl (hA0W0 x hx))
  hE0A hFImage hFLip hC0L hValues0 P0 hP0.
have[Q1 [hQ1 hRecover1]]:=@polyhedral_source_placement_exists R h2 d1 d n m
  Z1 A1 W U hZ1 hA1 hW hU hA1Z1 C1 hC1A1 L f1 E1 F hImage1 hLip1
  (@rectifiable_source_right_affine R d0 d1) (fun x hx=>or_intror (hA1W1 x hx))
  hE1A hFImage hFLip hC1L hValues1 P1 hP1.
pose hQ0Flat:@is_flat_current R h2 d m W hW Q0:=ex_intro _ L
  (@integral_polyhedral_current_flat_supported R h2 d m W hW L Q0 hQ0).
pose hQ1Flat:@is_flat_current R h2 d m W hW Q1:=ex_intro _ L
  (@integral_polyhedral_current_flat_supported R h2 d m W hW L Q1 hQ1).
have hImage0Value:@polyhedral_lipschitz_image R h2 d n m W U hW hU
    L F hFImage hFLip Q0 hQ0=T.
  exact:eq_trans (hRecover0 hQ0Flat) hValue0.
have hImage1Value:@polyhedral_lipschitz_image R h2 d n m W U hW hU
    L F hFImage hFLip Q1 hQ1=S.
  exact:eq_trans (hRecover1 hQ1Flat) hValue1.
have hSum:=@rectifiable_common_source_image_sum R h2 d n m W U hW hU
  L K F hFImage hFLip hLK Q0 Q1 hQ0 hQ1.
by rewrite hImage0Value hImage1Value in hSum.
Qed.
End RectifiableImageAdd.
