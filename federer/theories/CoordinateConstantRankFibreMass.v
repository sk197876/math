(** Federer (1969), 3.2.33, p. 270: the actual
    positive-mass constant-rank fibre in coordinates gives
    positive mass in W, by 3.1.18 (corrected reference). *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric HilbertFormCompactness
  NormCoordinateSystemUP NormRegularity NormClassOneUP NormRankZero ConstantRankFibrePositiveMass
  ClassOneDomainNullImage HausdorffMeasure MeasureUP MeasureAlmostBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [coordinate_constant_rank_fibre_nonnull]:
    S is contained in f inverse(Y), Federer 3.2.33,
    p. 270, at a generic rank point in actual
    coordinates. Nullity of the original fibre would imply
    nullity of its coordinate fibre through the actual
    class-one forward chart, contradicting 3.1.18's
    nonnull product fibre. No global chart bound is needed. *)
Theorem coordinate_constant_rank_fibre_nonnull (R:realType) n mu l v
    (W T:set (R_n R n)) (V:set (R_n R (mu+l)))
    (phi:R_n R n->R_n R (mu+l)) (psi:R_n R (mu+l)->R_n R n)
    (F:R_n R n->R_n R v)
    (D:R_n R (mu+l)->Hom (R_n R (mu+l)) (R_n R v)) a:
  is_norm_coordinate_system (inner_norm_real_norm (@euclidean_inner_productP R n))
    (inner_norm_real_norm (@euclidean_inner_productP R (mu+l))) W T V phi psi 1%N ->
  W a ->T a ->
  is_norm_class_one_field (inner_norm (@euclidean_inner_productP R (mu+l)))
    (inner_norm (@euclidean_inner_productP R v)) V (fun u=>F (psi u)) D ->
  norm_generic_rank (inner_norm (@euclidean_inner_productP R (mu+l))) V D (phi a) mu ->
  @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) l
    [set x|W x /\F x=F a]<>0%E.
Proof.
move=>hc ha ht hD hGeneric hNull.
have hBase:=norm_coordinate_base_inverse hc ha ht.
have hCoordinateNonnull:=@constant_rank_fibre_nonnull R mu l v V (fun u=>F (psi u)) D (phi a) hD hGeneric.
rewrite hBase in hCoordinateNonnull.
pose E:set (R_n R n):=[set x|(W x /\T x) /\F x=F a].
have hENull:@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) l E=0%E.
  apply:(measure_null_subset (@hausdorff_measure_is_measure R
    (inner_metric_space (@euclidean_inner_productP R n)) l) _ hNull).
  by move=>x [[hx hxT] hxF]; split.
have hNullImage:=@class_one_domain_hausdorff_null_image R n (mu+l) l T E phi
  ((norm_class_firstP (inner_norm_real_norm (@euclidean_inner_productP R n))
    (inner_norm_real_norm (@euclidean_inner_productP R (mu+l))) T phi).1
    (norm_coordinate_class_forward hc)) (fun x hx=>hx.1.2) hENull.
apply:hCoordinateNonnull.
apply:(measure_null_subset (@hausdorff_measure_is_measure R
  (inner_metric_space (@euclidean_inner_productP R (mu+l))) l) _ hNullImage).
move=>u [hu hF]; exists (psi u).
- split; first exact:(@norm_coordinate_backward_membership R (R_n R n) (R_n R (mu+l))
    (inner_norm (@euclidean_inner_productP R n)) (inner_norm (@euclidean_inner_productP R (mu+l)))
    (inner_norm_real_norm (@euclidean_inner_productP R n))
    (inner_norm_real_norm (@euclidean_inner_productP R (mu+l))) W T V phi psi 1%N hc u hu).
  exact hF.
- exact:(@norm_coordinate_cancel R (R_n R n) (R_n R (mu+l))
  (inner_norm (@euclidean_inner_productP R n)) (inner_norm (@euclidean_inner_productP R (mu+l)))
  (inner_norm_real_norm (@euclidean_inner_productP R n))
  (inner_norm_real_norm (@euclidean_inner_productP R (mu+l))) W T V phi psi 1%N hc u hu).
Qed.
