(** Orthogonal product coordinates supporting Federer (1969), 2.10.30, p.
    195. The chart is specified by its laws and sends the last scalar axis
    to an arbitrary unit normal. Its line sections are therefore the
    intrinsic normal sections of the book. Source context:
    EuclideanNormalChartUP.v *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerMetric
  EuclideanOneCoordinate EuclideanBlockCoordinates EuclideanNormalChartUP EuclideanLastAxisLine
  OrthonormalFamilies UnitNormalGeometry SteinerSymmetrisationUP ProductSections.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section NormalBlocks.
Variable R : realType.
Variable n : nat.
Local Notation E k := (inner_metric_space (@euclidean_inner_productP R k)).
Variable D : euclidean_normal_chart_data R (n+1).
Local Notation f := (normal_chart_forward_map D).
Local Notation g := (normal_chart_backward_map D).

(** Source for [euclidean_normal_block_join]: supporting
    product-to-normal coordinate map for Fubini in
    2.10.30, p. 195. The chart is used
    through its abstract data and laws. *)
Definition euclidean_normal_block_join (z : E n*E 1) : E (n+1) := f (euclidean_block_join z).

(** Source for [euclidean_normal_block_split]: supporting
    inverse normal-product coordinate map for the
    volume assertion in 2.10.30, p. 195. *)
Definition euclidean_normal_block_split (x : E (n+1)) : E n*E 1 := euclidean_block_split (g x).

Variable u : E (n+1).
Hypothesis hD : @is_euclidean_normal_chart R (n+1) (rshift n (ord0 : 'I_1)) u D.

(** Source for [euclidean_normal_block_joinK]: supporting
    product-coordinate cancellation in 2.10.30,
    p. 195. *)
Lemma euclidean_normal_block_joinK : cancel euclidean_normal_block_join euclidean_normal_block_split.
Proof.
move=> z; rewrite /euclidean_normal_block_split /euclidean_normal_block_join
  (normal_chart_forward_inverse_law hD) euclidean_block_joinK; reflexivity.
Qed.

(** Source for [euclidean_normal_block_splitK]: supporting
    ambient-coordinate cancellation in 2.10.30,
    p. 195. *)
Lemma euclidean_normal_block_splitK : cancel euclidean_normal_block_split euclidean_normal_block_join.
Proof.
move=> x; rewrite /euclidean_normal_block_split /euclidean_normal_block_join euclidean_block_splitK.
exact (normal_chart_backward_inverse_law hD x).
Qed.

(** Source for [euclidean_normal_block_base]: supporting
    orthogonality of the hyperplane foot in the
    normal chart for 2.10.30, p. 195. *)
Lemma euclidean_normal_block_base (p : E n) :
  inner_coordinate (@euclidean_inner_productP R (n+1)) u
    (euclidean_normal_block_join (p,0))=0.
Proof.
rewrite inner_coordinateE /euclidean_normal_block_join -(normal_chart_axis_law hD)
  (normal_chart_orthogonal_law hD).
exact (@euclidean_last_block_base_orthogonal R n p).
Qed.

(** Source for [euclidean_normal_block_line]: supporting normal-line
    identity in 2.10.30, p. 195 *)
Lemma euclidean_normal_block_line (p : E n) (t : R) :
  euclidean_normal_block_join (p,euclidean_one_embed t)=
    euclidean_normal_block_join (p,0)+t*:u.
Proof.
rewrite /euclidean_normal_block_join euclidean_last_block_line linearD linearZ
  (normal_chart_axis_law hD); reflexivity.
Qed.

(** Source for [euclidean_normal_block_scalar_section]: supporting scalar
    sections of the normal-product preimage in 2.10.30, p. 195 *)
Lemma euclidean_normal_block_scalar_section (S : set (E (n+1))) (p : E n) :
  (@euclidean_one_embed R) @^-1`
    product_vertical_section (euclidean_normal_block_join @^-1` S) p=
    normal_scalar_section u S (euclidean_normal_block_join (p,0)).
Proof.
apply/seteqP; split=> t;
  change (S (euclidean_normal_block_join (p,euclidean_one_embed t)) ->
    S (euclidean_normal_block_join (p,0)+t*:u)) ||
  change (S (euclidean_normal_block_join (p,0)+t*:u) ->
    S (euclidean_normal_block_join (p,euclidean_one_embed t)));
  by rewrite euclidean_normal_block_line.
Qed.
End NormalBlocks.
