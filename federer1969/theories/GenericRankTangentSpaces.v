(** Federer (1969), 3.1.21, p. 234: tangent spaces
    of the fibre and local image at a generic point. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerNorm HilbertFormCompactness
  NormDifferentialUP NormClassOneUP NormRegularity NormRankZero NormDiffeomorphismUP
  ConstantRankChartUP ConstantRankTheorem ConstantRankImageSubmanifold EuclideanSubmanifoldUP
  TangentConeUP ConstantRankFibreTangent ConstantRankImageTangent.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [federer_3_1_21_constant_rank]: both displayed
    tangent-space formulas at generic points in Federer 3.1.21,
    p. 234. Apply the proved class-one normal form to
    obtain an actual open neighbourhood U. Source dimension v+l
    covers every admissible rank v and its complementary dimension l,
    including rank zero and zero-dimensional source or target. *)
Theorem federer_3_1_21_constant_rank (R:realType) v l n
    (A:set (R_n R (v+l))) (f:R_n R (v+l)->R_n R n)
    (D:R_n R (v+l)->Hom (R_n R (v+l)) (R_n R n)) a :
  is_norm_class_one_field (inner_norm (@euclidean_inner_productP R (v+l)))
    (inner_norm (@euclidean_inner_productP R n)) A f D ->
  norm_generic_rank (inner_norm (@euclidean_inner_productP R (v+l))) A D a v ->
  exists U:set (R_n R (v+l)),
    norm_domain_interior (inner_norm (@euclidean_inner_productP R (v+l))) U a /\
    norm_tangent_cone (inner_norm (@euclidean_inner_productP R (v+l)))
      [set x|A x /\ f x=f a] a=[set w|D a w=0] /\
    norm_tangent_cone (inner_norm (@euclidean_inner_productP R n)) (f @` U) (f a)=range (D a) /\
    @is_euclidean_submanifold R n v 1 (f @` U).
Proof.
move=>hD hgen.
pose X:=R_n R (v+l).
pose Y:=R_n R n.
pose NX:=inner_norm (@euclidean_inner_productP R (v+l)).
pose NY:=inner_norm (@euclidean_inner_productP R n).
pose hNX:=inner_norm_real_norm (@euclidean_inner_productP R (v+l)).
pose hNY:=inner_norm_real_norm (@euclidean_inner_productP R n).
have hf:=(@norm_class_firstP R X Y NX NY hNX hNY A f).2 (ex_intro _ D hD).
have [U [e [p [j [g [G [psi hC]]]]]]]:=@federer_3_1_18 R v l n A f D a 1 (leqnn 1) hf hD hgen.
exists U; split.
- have hc:=norm_class_continuous (norm_diffeomorphism_forward_class (constant_rank_source_chart hC)).
  exact ((hc a (constant_rank_base_member hC)).1).
- split; first exact: constant_rank_fibre_tangent hC hD.
  split; first exact: constant_rank_image_tangent hC.
  exact: constant_rank_image_submanifold hC.
Qed.
