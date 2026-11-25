(** Federer (1969), 3.2.31, p. 269: supporting existence
    of the range idempotent before small symmetric rescaling.
    Use the already proved abstract range projection and its
    opaque adjoint; the witness stays local to an existence proof. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import TensorUP Hom GrassmannAbbreviations EuclideanInnerProduct InnerProductUP LinearBasis
  AdjointUP AdjointLaws LinearRankUP LinearRangeProjectionUP LinearRangeProjection LinearRangeProjectionLaws
  SymmetricRangeIdempotentUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [symmetric_range_idempotent_exists]: supporting
    the low-rank range split in Federer 3.2.31, p. 269.
    The range coordinates of 3.1.18, p. 229, give an orthogonal
    injection j and its adjoint p, with p j=identity. Their
    local composite proves the independent symmetric idempotent
    and exact-range laws. Only the target needs a finite basis;
    no dimension comparison with the source is assumed. *)
Theorem symmetric_range_idempotent_exists (R:realType) (X Y:lmodType R)
    (B:Y->Y->R) (hB:is_inner_product B) n (b:'I_n->Y) (hb:is_basis b)
    (D:Hom X Y):
  exists P:Hom Y Y,@is_symmetric_range_idempotent R X Y B D P.
Proof.
have [r [hr _]]:=linear_rank_exists D hb.
have [p [j hProjection]]:=linear_range_projection_exists hB hr.
pose P:Hom Y Y:=hom_of_linear (linear_comp j p).
have hAdj:=range_projection_adjoint hProjection.
have hReverse:=@adjoint_reverse R (R_n R r) Y (@euclidean_inner_product R r) B
  (@euclidean_inner_productP R r) hB j p hAdj.
exists P; constructor.
- move=>x y; change (B (j (p x)) y=B x (j (p y))).
  by rewrite -hAdj -hReverse.
- move=>y; change (j (p (j (p y)))=j (p y)).
  by rewrite (range_projection_cancel hProjection).
- move=>y; split.
  + move=>hy; apply:(range_projection_image hProjection y).1.
    exists (p y); exact hy.
  + move=>hy; exact (range_projection_reconstruct hProjection hy).
Qed.
