(** Federer (1969), 3.2.33, p. 270: local analytic
    chart images of null root sets remain Hausdorff null,
    by 2.10.11 and 2.10.35, pp. 176,197. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets cardinality
  constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  HilbertFormCompactness NormClassOneUP ClassOneDomainLipschitzCover
  LipschitzUP KirszbraunExtensionUP KirszbraunExtension EuclideanLebesgueDimensions
  EuclideanHausdorffLebesgue HausdorffMeasure NullLipschitzArea MeasureUP MeasureAlmostBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [class_one_domain_hausdorff_null_image]: null root-set
    transport in the analytic-manifold rank argument of
    Federer 3.2.33, p. 270. Countably many local
    Lipschitz pieces suffice; opaque same-bound extensions
    are auxiliary to each piece and agree on its actual
    source. No source measurability or finite mass is assumed. *)
Theorem class_one_domain_hausdorff_null_image (R:realType) m n k
    (A E:set (R_n R m)) (f:R_n R m->R_n R n):
  norm_class_one (inner_norm (@euclidean_inner_productP R m))
    (inner_norm (@euclidean_inner_productP R n)) A f ->E `<=` A ->
  @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R m)) k E=0%E ->
  @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) k (f @` E)=0%E.
Proof.
move=>hf hEA hNull.
pose X:=inner_metric_space (@euclidean_inner_productP R m).
pose Y:=inner_metric_space (@euclidean_inner_productP R n).
pose H:=@hausdorff_measure R Y k.
pose hH:=@hausdorff_measure_is_measure R Y k.
have [C [hC [hCover hPieces]]]:=class_one_domain_countable_lipschitz_cover hf.
have hPiece U (hU:C U):H (f @` (E `&` U))=0%E.
  have [ho [hUA [M hLip]]]:=hPieces U hU.
  pose G:=@euclidean_lipschitz_extension R m n U f M hLip.
  have hG:=@euclidean_lipschitz_extension_specification R m n U f M hLip.
  have hSource:@hausdorff_measure R X k (E `&` U)=0%E.
    apply:(measure_null_subset (@hausdorff_measure_is_measure R X k) _ hNull).
    by move=>x hx; exact hx.1.
  have hGN:=null_hausdorff_lipschitz_image (kirszbraun_extension_bound_law hG) hSource.
  have hImage:f @` (E `&` U)=G @` (E `&` U).
    apply/seteqP; split=>y [x hx <-]; exists x=>//.
    - exact:(@kirszbraun_extension_agreement_law R m n U f G M hG x hx.2).
    - exact:(esym (@kirszbraun_extension_agreement_law R m n U f G M hG x hx.2)).
  by rewrite hImage.
have hUnion:=@measure_null_countable_union R Y [the choiceType of set X]
  H hH C (fun U=>f @` (E `&` U)) hC hPiece.
apply:(measure_null_subset hH _ hUnion)=>y [x hx <-].
have [U hU hxU]:=hCover x (hEA x hx).
exists U; first exact hU.
exists x; last reflexivity; by split.
Qed.

(** Source for [class_one_domain_null_image]: the natural
    coordinate degree in Federer 3.2.33, p. 270.
    The proved all-degree Hausdorff result and 2.10.35
    give null transport from Lebesgue parameter measure. *)
Corollary class_one_domain_null_image (R:realType) m n
    (A E:set (R_n R m)) (f:R_n R m->R_n R n):
  norm_class_one (inner_norm (@euclidean_inner_productP R m))
    (inner_norm (@euclidean_inner_productP R n)) A f ->E `<=` A ->
  euclidean_lebesgue_measure m E=0%E ->
  @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m (f @` E)=0%E.
Proof.
move=>hf hEA hNull.
apply:(class_one_domain_hausdorff_null_image hf hEA).
by rewrite (euclidean_hausdorff_spherical_lebesgue E).1.
Qed.
