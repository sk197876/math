(** Federer (1969), 4.1.9, p. 363: the original
    cylinder properness for T passes to its boundary.
    The boundary support is relatively closed in U
    and lies in spt T by 4.1.7, p. 356.
    Use exact compact preimages and the existing
    continuous spatial block projection. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct EuclideanBlockCoordinates EuclideanBlockLinearMaps
  EuclideanBlockNormTopology TopologicalProductMaps AlternatingForms CurrentSpaces CurrentBoundary
  CurrentBoundarySupport CurrentProperOnContainingSet CurrentProperContainingCriterion SmoothCompactSet
  FunctionalSupportRelativeClosed IsotropyGroupTopology CurrentHomotopyUP CurrentHomotopyCylinder.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentHomotopyBoundaryCylinder.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n nu j:nat.
Local Notation X := (R_n R n).
Local Notation Z := (R_n R (1+n)%N).
Local Notation Y := (R_n R nu).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation hNZ := (inner_norm_real_norm (@euclidean_inner_productP R (1+n)%N)).
Local Notation XT := (real_norm_metric_space hNX).
Local Notation ZT := (real_norm_metric_space hNZ).
Local Notation RT := (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R 1%N))).
Variable A:set R.
Variables (U:set X) (V:set Y).
Variables (f g:X->Y) (h:Z->Y).
Hypothesis hGeometry:@is_current_homotopy_geometry R n nu A U V f g h.
Local Notation hU := (@current_homotopy_source_open R n nu A U V f g h hGeometry).
Local Notation AU := (@current_homotopy_product_domain R n A U).
Local Notation image := (@current_homotopy_image R n nu A U V f g h hGeometry).
Variable T:@current_space R h2 n U hU j.+1.
Local Notation boundary := (@current_boundary R h2 n j U hU T).
Local Notation CT := (@current_homotopy_closed_cylinder R h2 n nu j.+1 A U V f g h hGeometry T).
Local Notation CB := (@current_homotopy_closed_cylinder R h2 n nu j A U V f g h hGeometry boundary).
Local Notation hCT := (@current_homotopy_cylinder_in_domain R h2 n nu j.+1 A U V f g h hGeometry T).
Local Notation hCB := (@current_homotopy_cylinder_in_domain R h2 n nu j A U V f g h hGeometry boundary).
Local Notation q := (@euclidean_last_block_map R 1%N n).

(** Source for [current_homotopy_boundary_cylinder_subset]:
    the original boundary cylinder lies in the
    original cylinder for T, supporting Federer
    4.1.9, p. 363, by the preceding boundary
    support inclusion. *)
Lemma current_homotopy_boundary_cylinder_subset:CB `<=` CT.
Proof.
move=>z hz;split;first exact:hz.1.
exact:(@current_boundary_support_subset R h2 n j U hU T _ hz.2).
Qed.

(** Source for [current_homotopy_boundary_cylinder_proper]:
    the single printed properness assumption also
    defines the deformation chain of boundary T,
    supporting the positive-degree homotopy formula
    in Federer 4.1.9, p. 363. No second
    properness or compact-support hypothesis is added. *)
Theorem current_homotopy_boundary_cylinder_proper:
  @is_current_homotopy_proper R h2 n nu j.+1 A U V f g h hGeometry T->
  @is_current_homotopy_proper R h2 n nu j A U V f g h hGeometry boundary.
Proof.
move=>hProper.
have[D [hClosed hBoundary]]:=@functional_support_relative_closed R X (A_m X R^o j) NX hNX U
  (@current_test_space R h2 n U hU j) (@current_test_value R h2 n U hU j)
  (@current_value R h2 n U hU j boundary).
have hBoundarySet:@current_support R h2 n U hU j boundary=U `&` D:=hBoundary.
have hQ:continuous (fun z:ZT=>(q z:XT)).
  move=>z.
  exact:(continuous_comp (@euclidean_block_split_norm_continuous R 1%N n z)
    (@second_projection_continuous RT XT (@euclidean_block_split R 1%N n z))).
have hClosedPullback:@closed ZT (q @^-1` D).
  exact:(@preimage_closed ZT XT q D (fun z _=>hQ z) hClosed).
apply:(@current_containing_proper_compact_loci R (1+n)%N nu AU V CB hCB h image).2=>K.
have hCompact:=@current_containing_proper_compact_preimage R (1+n)%N nu AU V CT hCT h image
  hProper K.
have hEqual:[set z|CB z /\ smooth_compact_carrier K (h z)]=
    [set z|CT z /\ smooth_compact_carrier K (h z)] `&` (q @^-1` D).
  apply:funext=>z;apply:propext;split.
  - move=>[hz hKz];split.
    + exact:conj (current_homotopy_boundary_cylinder_subset hz) hKz.
    + have hUD:(U `&` D) (q z) by rewrite -hBoundarySet;exact:hz.2.
      exact:hUD.2.
  - move=>[[hz hKz] hDz];split;last exact:hKz.
    split;first exact:hz.1.
    rewrite hBoundarySet;exact:conj hz.2.1 hDz.
rewrite hEqual;exact:compact_closedI hCompact hClosedPullback.
Qed.
End CurrentHomotopyBoundaryCylinder.
