(** Supporting normal-frame wedges for Federer (1969), 2.10.16, p. 178. The
    adjoint of the stacked normal map sends each block of standard basis
    vectors to the corresponding projection's normal frame. Derive this
    solely from the coordinate laws and the adjoint equation of 1.7.4, p.
    30, using 2.6.5, p. 120, for blocks. *)
From mathcomp Require Import all_boot all_order all_algebra reals topology.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerMetric
  EuclideanProjectionSpace EuclideanProjectionMetric EuclideanBlockCoordinates StackedNormalFamily
  CoordinateProjection AdjointUP Adjoint AdjointLaws TensorUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [stacked_normal_family_leftE]: supporting first
    normal-coordinate block in 2.10.16, p. 178, from
    the abstract block laws of 2.6.5, p. 120. *)
Lemma stacked_normal_family_leftE (R : realType) (n a r : nat)
    (F : orthogonal_projection_metric_space R n a * orthogonal_projection_metric_space R n r ->
      {linear R_n R n -> R_n R (a+r)}) :
  is_stacked_normal_family F -> forall p q x i,
  F (p,q) x (lshift r i)=euclidean_projection_linear p x i.
Proof.
move=> hF p q x i.
have he := congr1 (fun z : R_n R a * R_n R r => z.1 i) (hF p q x).
by rewrite /euclidean_block_split ffunE in he.
Qed.

(** Source for [stacked_normal_family_rightE]: supporting second
    normal-coordinate block in 2.10.16, p. 178, from
    the abstract block laws of 2.6.5, p. 120. *)
Lemma stacked_normal_family_rightE (R : realType) (n a r : nat)
    (F : orthogonal_projection_metric_space R n a * orthogonal_projection_metric_space R n r ->
      {linear R_n R n -> R_n R (a+r)}) :
  is_stacked_normal_family F -> forall p q x i,
  F (p,q) x (rshift a i)=euclidean_projection_linear q x i.
Proof.
move=> hF p q x i.
have he := congr1 (fun z : R_n R a * R_n R r => z.2 i) (hF p q x).
by rewrite /euclidean_block_split ffunE in he.
Qed.

(** Source for [stacked_normal_adjoint_left_basis]: supporting
    first normal-frame block for 2.10.16, p. 178. Test
    the two vectors against arbitrary x using the adjoint
    equation in 1.7.4, p. 30, and the first coordinate law. *)
Lemma stacked_normal_adjoint_left_basis (R : realType) (n a r : nat)
    (F : orthogonal_projection_metric_space R n a * orthogonal_projection_metric_space R n r ->
      {linear R_n R n -> R_n R (a+r)}) :
  is_stacked_normal_family F -> forall p q i,
  inner_adjoint (@euclidean_inner_productP R n) (@euclidean_inner_productP R (a+r))
    (@coordinate_basisP R n) (F (p,q)) (@coordinate_basis R (a+r) (lshift r i))=
  inner_adjoint (@euclidean_inner_productP R n) (@euclidean_inner_productP R a)
    (@coordinate_basisP R n) (euclidean_projection_linear p) (@coordinate_basis R a i).
Proof.
move=> hF p q i; apply: (@inner_vectors_ext R (R_n R n) _ (@euclidean_inner_productP R n))=> x.
have h1 := @inner_adjointP R (R_n R n) (R_n R (a+r)) _ _
  (@euclidean_inner_productP R n) (@euclidean_inner_productP R (a+r))
  n (@coordinate_basis R n) (@coordinate_basisP R n) (F (p,q)) x (@coordinate_basis R (a+r) (lshift r i)).
have h2 := @inner_adjointP R (R_n R n) (R_n R a) _ _
  (@euclidean_inner_productP R n) (@euclidean_inner_productP R a)
  n (@coordinate_basis R n) (@coordinate_basisP R n) (euclidean_projection_linear p) x (@coordinate_basis R a i).
rewrite h1 h2 !euclidean_inner_basis.
exact (@stacked_normal_family_leftE R n a r F hF p q x i).
Qed.

(** Source for [stacked_normal_adjoint_right_basis]: supporting
    second normal-frame block for 2.10.16, p. 178.
    The same abstract adjoint equation identifies the last
    block with the second projection's adjoint frame. *)
Lemma stacked_normal_adjoint_right_basis (R : realType) (n a r : nat)
    (F : orthogonal_projection_metric_space R n a * orthogonal_projection_metric_space R n r ->
      {linear R_n R n -> R_n R (a+r)}) :
  is_stacked_normal_family F -> forall p q i,
  inner_adjoint (@euclidean_inner_productP R n) (@euclidean_inner_productP R (a+r))
    (@coordinate_basisP R n) (F (p,q)) (@coordinate_basis R (a+r) (rshift a i))=
  inner_adjoint (@euclidean_inner_productP R n) (@euclidean_inner_productP R r)
    (@coordinate_basisP R n) (euclidean_projection_linear q) (@coordinate_basis R r i).
Proof.
move=> hF p q i; apply: (@inner_vectors_ext R (R_n R n) _ (@euclidean_inner_productP R n))=> x.
have h1 := @inner_adjointP R (R_n R n) (R_n R (a+r)) _ _
  (@euclidean_inner_productP R n) (@euclidean_inner_productP R (a+r))
  n (@coordinate_basis R n) (@coordinate_basisP R n) (F (p,q)) x (@coordinate_basis R (a+r) (rshift a i)).
have h2 := @inner_adjointP R (R_n R n) (R_n R r) _ _
  (@euclidean_inner_productP R n) (@euclidean_inner_productP R r)
  n (@coordinate_basis R n) (@coordinate_basisP R n) (euclidean_projection_linear q) x (@coordinate_basis R r i).
rewrite h1 h2 !euclidean_inner_basis.
exact (@stacked_normal_family_rightE R n a r F hF p q x i).
Qed.
