(** Supporting the affine double-slicing formula of Federer (1969), 2.10.16,
    p. 178. Specify the stacked normal maps by their two coordinate
    projections. Prove evaluation continuity and existence separately, so
    all later arguments use the laws of the family. The block coordinates
    are the actual isomorphism of 2.6.5, p. 120, and include empty blocks. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals topology.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerMetric
  EuclideanProjectionSpace EuclideanProjectionMetric EuclideanBlockCoordinates EuclideanBlockLinear
  TopologicalProductMaps TensorUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [is_stacked_normal_family]: supporting abstract
    coordinate laws for 2.10.16, p. 178. The first a
    normal coordinates are p(x), the last r are q(x). *)
Definition is_stacked_normal_family (R : realType) (n a r : nat)
    (F : orthogonal_projection_metric_space R n a * orthogonal_projection_metric_space R n r ->
      {linear R_n R n -> R_n R (a+r)}) :=
  forall p q x, euclidean_block_split (F (p,q) x)=
    (euclidean_projection_linear p x,euclidean_projection_linear q x).

(** Source for [stacked_normal_familyE]: supporting evaluation
    consequence for the coordinate calculation in 2.10.16,
    p. 178. The block inverse determines every map uniquely. *)
Lemma stacked_normal_familyE (R : realType) (n a r : nat)
    (F : orthogonal_projection_metric_space R n a * orthogonal_projection_metric_space R n r ->
      {linear R_n R n -> R_n R (a+r)}) :
  is_stacked_normal_family F -> forall p q x,
  F (p,q) x=euclidean_block_join (euclidean_projection_linear p x,euclidean_projection_linear q x).
Proof.
move=> hF p q x.
rewrite -[LHS]euclidean_block_splitK (hF p q x); by [].
Qed.

(** Source for [stacked_normal_family_continuous]: supporting
    joint normal-coordinate continuity for 2.10.16, p. 178,
    from the family laws and continuous projection evaluation.
    No particular linear-map representation is unfolded. *)
Lemma stacked_normal_family_continuous (R : realType) (n a r : nat)
    (F : orthogonal_projection_metric_space R n a * orthogonal_projection_metric_space R n r ->
      {linear R_n R n -> R_n R (a+r)}) :
  is_stacked_normal_family F ->
  continuous (fun z : (orthogonal_projection_metric_space R n a * orthogonal_projection_metric_space R n r)*
    inner_metric_space (@euclidean_inner_productP R n) =>
    (F z.1 z.2 : inner_metric_space (@euclidean_inner_productP R (a+r)))).
Proof.
move=> hF.
pose P := euclidean_projection_space R n a.
pose Q := euclidean_projection_space R n r.
pose X := [the metricType R of inner_metric_space (@euclidean_inner_productP R n)].
pose Y := [the metricType R of inner_metric_space (@euclidean_inner_productP R a)].
pose Z := [the metricType R of inner_metric_space (@euclidean_inner_productP R r)].
change (continuous (fun z : (P*Q)*X =>
  (F z.1 z.2 : inner_metric_space (@euclidean_inner_productP R (a+r))))).
have hp : continuous (fun z : (P*Q)*X => (z.1.1,z.2)).
  apply (@topological_pair_continuous ((P*Q)*X)%type P X
    (fun z : (P*Q)*X => z.1.1) (@snd (P*Q)%type X));
    last exact (@second_projection_continuous (P*Q)%type X).
  move=> z; exact (continuous_comp (@first_projection_continuous (P*Q)%type X z)
    (@first_projection_continuous P Q z.1)).
have hq : continuous (fun z : (P*Q)*X => (z.1.2,z.2)).
  apply (@topological_pair_continuous ((P*Q)*X)%type Q X
    (fun z : (P*Q)*X => z.1.2) (@snd (P*Q)%type X));
    last exact (@second_projection_continuous (P*Q)%type X).
  move=> z; exact (continuous_comp (@first_projection_continuous (P*Q)%type X z)
    (@second_projection_continuous P Q z.1)).
have heval : continuous (fun z : (P*Q)*X =>
    ((euclidean_projection_linear z.1.1 z.2 : Y),(euclidean_projection_linear z.1.2 z.2 : Z))).
  apply (@topological_pair_continuous ((P*Q)*X)%type Y Z
    (fun z : (P*Q)*X => (euclidean_projection_linear z.1.1 z.2 : Y))
    (fun z : (P*Q)*X => (euclidean_projection_linear z.1.2 z.2 : Z))).
  - move=> z; exact (continuous_comp (hp z) (@euclidean_projection_evaluation_continuous R n a (z.1.1,z.2))).
  - move=> z; exact (continuous_comp (hq z) (@euclidean_projection_evaluation_continuous R n r (z.1.2,z.2))).
have he : (fun z : (P*Q)*X => (F z.1 z.2 : inner_metric_space (@euclidean_inner_productP R (a+r))))=
    (fun z => euclidean_block_join (euclidean_projection_linear z.1.1 z.2,euclidean_projection_linear z.1.2 z.2)).
  apply/funext=> -[[p q] x]; exact (@stacked_normal_familyE R n a r F hF p q x).
rewrite he; move=> z; exact (continuous_comp (heval z)
  (@euclidean_block_join_continuous R a r (euclidean_projection_linear z.1.1 z.2,euclidean_projection_linear z.1.2 z.2))).
Qed.

(** Source for [stacked_normal_family_exists]: proved existence
    supporting 2.10.16, p. 178. Compose the pair of
    linear normal projections with the existing block isomorphism.
    The implementation is only a witness of the abstract laws. *)
Theorem stacked_normal_family_exists (R : realType) (n a r : nat) :
  exists F, @is_stacked_normal_family R n a r F.
Proof.
have hlin (z : orthogonal_projection_metric_space R n a * orthogonal_projection_metric_space R n r) :
    linear (fun x => euclidean_block_join (euclidean_projection_linear z.1 x,euclidean_projection_linear z.2 x)).
  move=> t x y; rewrite !linearP.
  exact (@euclidean_block_join_linear R a r t
    (euclidean_projection_linear z.1 x,euclidean_projection_linear z.2 x)
    (euclidean_projection_linear z.1 y,euclidean_projection_linear z.2 y)).
pose f (z : orthogonal_projection_metric_space R n a * orthogonal_projection_metric_space R n r) x :=
  euclidean_block_join (euclidean_projection_linear z.1 x,euclidean_projection_linear z.2 x).
pose mix z := GRing.isLinear.Build R (R_n R n) (R_n R (a+r)) *:%R (f z) (hlin z).
pose F z : {linear R_n R n -> R_n R (a+r)} := HB.pack (f z) (mix z).
exists F=> p q x; exact: euclidean_block_joinK.
Qed.
