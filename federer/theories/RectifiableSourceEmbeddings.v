(** Federer (1969), 4.1.24, p. 380: place two
    arbitrary Euclidean polyhedral sources in separate slices
    of R^(1+d0+d1). All maps below abbreviate existing
    Cartesian block maps. Their exact coordinates, affine
    laws, global Lipschitz bounds and disjoint compact
    images are proved, including empty source blocks. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions
  classical_sets reals topology.
From Federer Require Import Hom Bilinear AffineMaps RealNormUP NormMetric
  NormDifferentialUP InnerNorm HilbertFormCompactness GrassmannAbbreviations
  EuclideanInnerProduct EuclideanBlockCoordinates EuclideanBlockLinearMaps
  EuclideanOneCoordinate CurrentCartesianAffineSlice LipschitzUP LipschitzBasic
  MetricLipschitzCompactImage EuclideanAffineSourceLipschitz.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section RectifiableSourceEmbeddings.
Variable R:realType.
Variables d0 d1:nat.
Local Notation X0:=(R_n R d0).
Local Notation X1:=(R_n R d1).
Local Notation X:=(R_n R (1+(d0+d1))%N).
Local Notation LX:=(@euclidean_last_injection_map R 1%N (d0+d1)%N).
Local Notation PX:=(@euclidean_last_block_map R 1%N (d0+d1)%N).
Local Notation L0:=(hom_comp LX (@euclidean_first_injection_map R d0 d1)).
Local Notation L1:=(hom_comp LX (@euclidean_last_injection_map R d0 d1)).
Local Notation c:=(@euclidean_first_injection_map R 1%N (d0+d1)%N
  (@euclidean_one_embed R 1)).

(** Source for [rectifiable_source_left]: the first original
    source, in the zero tagged slice, supporting the
    subgroup assertion of 4.1.24, p. 380. *)
Definition rectifiable_source_left (x:X0):X:=L0 x.
(** Source for [rectifiable_source_right]: the second original
    source, in the unit tagged slice, supporting
    4.1.24, p. 380. *)
Definition rectifiable_source_right (x:X1):X:=c+L1 x.
(** Source for [rectifiable_source_left_projection]: the original
    first source coordinates, 4.1.24, p. 380. *)
Definition rectifiable_source_left_projection:Hom X X0:=
  hom_comp (@euclidean_first_block_map R d0 d1) PX.
(** Source for [rectifiable_source_right_projection]: the original
    second source coordinates, 4.1.24, p. 380. *)
Definition rectifiable_source_right_projection:Hom X X1:=
  hom_comp (@euclidean_last_block_map R d0 d1) PX.
(** Source for [rectifiable_source_tag]: the separating scalar
    coordinate of the two image pieces in the common
    source, supporting 4.1.24, p. 380. *)
Definition rectifiable_source_tag (x:X):R:=
  @euclidean_one_project R (@euclidean_first_block_map R 1%N (d0+d1)%N x).

(** Source for [rectifiable_source_left_coordinates]: exact original
    source coordinates in the auxiliary common source,
    4.1.24, p. 380. *)
Lemma rectifiable_source_left_coordinates x:
  rectifiable_source_left x=euclidean_block_join ((0:R_n R 1%N),
    @euclidean_block_join R d0 d1 (x,(0:X1))).
Proof. by rewrite /rectifiable_source_left hom_compE. Qed.

(** Source for [rectifiable_source_right_coordinates]: exact second
    source coordinates, with scalar tag one, 4.1.24, p. 380. *)
Lemma rectifiable_source_right_coordinates x:
  rectifiable_source_right x=euclidean_block_join (@euclidean_one_embed R 1,
    @euclidean_block_join R d0 d1 ((0:X0),x)).
Proof.
rewrite /rectifiable_source_right hom_compE.
symmetry;exact:current_cartesian_join_affine.
Qed.

(** Source for [rectifiable_source_left_inverse]: no original
    first source point is identified by the common
    source inclusion, 4.1.24, p. 380. *)
Lemma rectifiable_source_left_inverse:cancel rectifiable_source_left
    rectifiable_source_left_projection.
Proof.
move=>x;rewrite /rectifiable_source_left_projection hom_compE
  rectifiable_source_left_coordinates.
change (fst (@euclidean_block_split R d0 d1
  (snd (@euclidean_block_split R 1%N (d0+d1)%N
    (euclidean_block_join (0,euclidean_block_join (x,0))))))=x).
by rewrite !euclidean_block_joinK.
Qed.

(** Source for [rectifiable_source_right_inverse]: the second
    source projection recovers every original point,
    4.1.24, p. 380. *)
Lemma rectifiable_source_right_inverse:cancel rectifiable_source_right
    rectifiable_source_right_projection.
Proof.
move=>x;rewrite /rectifiable_source_right_projection hom_compE
  rectifiable_source_right_coordinates.
change (snd (@euclidean_block_split R d0 d1
  (snd (@euclidean_block_split R 1%N (d0+d1)%N
    (euclidean_block_join (@euclidean_one_embed R 1,euclidean_block_join (0,x))))))=x).
by rewrite !euclidean_block_joinK.
Qed.

(** Source for [rectifiable_source_left_tag]: the first
    source lies in scalar slice zero, 4.1.24, p. 380. *)
Lemma rectifiable_source_left_tag x:rectifiable_source_tag (rectifiable_source_left x)=0.
Proof.
rewrite /rectifiable_source_tag rectifiable_source_left_coordinates.
change (@euclidean_one_project R
  (fst (@euclidean_block_split R 1%N (d0+d1)%N
    (euclidean_block_join (0,euclidean_block_join (x,0)))))=0).
by rewrite euclidean_block_joinK /euclidean_one_project ffunE.
Qed.

(** Source for [rectifiable_source_right_tag]: the second
    source lies in scalar slice one, 4.1.24, p. 380. *)
Lemma rectifiable_source_right_tag x:rectifiable_source_tag (rectifiable_source_right x) = 1.
Proof.
rewrite /rectifiable_source_tag rectifiable_source_right_coordinates.
change (@euclidean_one_project R
  (fst (@euclidean_block_split R 1%N (d0+d1)%N
    (euclidean_block_join (@euclidean_one_embed R 1,euclidean_block_join (0,x))))) = 1).
by rewrite euclidean_block_joinK euclidean_one_embedK.
Qed.

(** Source for [rectifiable_source_images_disjoint]: the two
    original source sets have disjoint images, including
    arbitrary empty sets, 4.1.24, p. 380. *)
Theorem rectifiable_source_images_disjoint (A0:set X0) (A1:set X1):
  forall z,(rectifiable_source_left @` A0) z->
    (rectifiable_source_right @` A1) z->False.
Proof.
move=>z [x hx <-] [y hy hEqual].
have hTag:=congr1 rectifiable_source_tag hEqual.
rewrite rectifiable_source_left_tag rectifiable_source_right_tag in hTag.
have hPositive:=@ltr01 R;by rewrite hTag ltxx in hPositive.
Qed.

(** Source for [rectifiable_source_left_affine]: the first
    inclusion preserves every original simplex hull under
    the old affine-image law, 4.1.24, p. 380. *)
Theorem rectifiable_source_left_affine:is_affine_map rectifiable_source_left.
Proof. exact:(@linear_affine_map R X0 X (hom_as_linear L0)). Qed.

(** Source for [rectifiable_source_right_affine]: translation
    of the second linear inclusion is affine,
    so its integral polyhedral image remains integral,
    4.1.24, p. 380. *)
Theorem rectifiable_source_right_affine:is_affine_map rectifiable_source_right.
Proof.
case:(@affine_isomorphism R X1 X (hom_as_linear L1) c)=>hAffine _ _ _.
exact:hAffine.
Qed.

(** Source for [rectifiable_source_left_lipschitz]: a finite
    global source bound for the first inclusion,
    4.1.24, p. 380. *)
Theorem rectifiable_source_left_lipschitz:
  @is_metric_lipschitz R
    (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R d0)))
    (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R (1+(d0+d1))%N)))
    setT rectifiable_source_left.
Proof. exact:euclidean_linear_source_lipschitz. Qed.

(** Source for [rectifiable_source_right_lipschitz]: the translated
    second inclusion has a finite global bound,
    4.1.24, p. 380. *)
Theorem rectifiable_source_right_lipschitz:
  @is_metric_lipschitz R
    (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R d1)))
    (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R (1+(d0+d1))%N)))
    setT rectifiable_source_right.
Proof. exact:euclidean_affine_source_lipschitz. Qed.

(** Source for [rectifiable_source_images_compact]: compactness
    of both exact tagged compact images in the common
    source, 4.1.24, p. 380. This is a consequence
    of the preceding map laws, not an additional premise
    in the original approximation definition. *)
Theorem rectifiable_source_images_compact (A0:set X0) (A1:set X1):
  @compact (real_norm_metric_space
    (inner_norm_real_norm (@euclidean_inner_productP R d0))) A0->
  @compact (real_norm_metric_space
    (inner_norm_real_norm (@euclidean_inner_productP R d1))) A1->
  @compact (real_norm_metric_space
    (inner_norm_real_norm (@euclidean_inner_productP R (1+(d0+d1))%N)))
    (rectifiable_source_left @` A0) /\
  @compact (real_norm_metric_space
    (inner_norm_real_norm (@euclidean_inner_productP R (1+(d0+d1))%N)))
    (rectifiable_source_right @` A1).
Proof.
move=>hA0 hA1;split.
- apply:metric_lipschitz_compact_image hA0 _.
  have[L [hL hBound]]:=rectifiable_source_left_lipschitz.
  exists L;split;first exact:hL.
  exact:(@metric_lipschitz_bound_restrict R (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R d0)))
    (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R (1+(d0+d1))%N))) setT A0 rectifiable_source_left L
    (fun _ _=>Logic.I) hBound).
- apply:metric_lipschitz_compact_image hA1 _.
  have[L [hL hBound]]:=rectifiable_source_right_lipschitz.
  exists L;split;first exact:hL.
  exact:(@metric_lipschitz_bound_restrict R (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R d1)))
    (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R (1+(d0+d1))%N))) setT A1 rectifiable_source_right L
    (fun _ _=>Logic.I) hBound).
Qed.
End RectifiableSourceEmbeddings.
