(** Last-coordinate normal lines supporting Federer (1969), 2.10.30, p. 195,
    in the orthogonal product chart used for Fubini. The coordinate choice
    is auxiliary and is transported to an arbitrary unit normal. Source
    editions: EuclideanNormalChartUP.v *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerMetric
  EuclideanOneCoordinate EuclideanBlockCoordinates CoordinateProjection.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [euclidean_last_block_line]: supporting
    normal-line parametrisation in the product-coordinate
    proof of volume equality in 2.10.30,
    p. 195. Empty hyperplane blocks are allowed. *)
Lemma euclidean_last_block_line (R : realType) n
    (p : inner_metric_space (@euclidean_inner_productP R n)) (t : R) :
  euclidean_block_join (p,euclidean_one_embed t)=
    euclidean_block_join (p,(0 : inner_metric_space (@euclidean_inner_productP R 1)))+
      t*:(@coordinate_basis R (n+1) (rshift n (ord0 : 'I_1))).
Proof.
apply/ffunP=> i; case: (split_ordP i)=> [j ->|j ->].
- rewrite euclidean_block_join_left ffunE euclidean_block_join_left /coordinate_basis !ffunE eq_lrshift.
  change (p j=p j+t*0); by rewrite mulr0 addr0.
- rewrite (ord1 j) euclidean_block_join_right /euclidean_one_embed ffunE
    ffunE euclidean_block_join_right /coordinate_basis !ffunE eqxx.
  change (t=0+t*1); by rewrite mulr1 add0r.
Qed.

(** Source for [euclidean_last_block_base_orthogonal]: supporting
    hyperplane foot in the product chart for 2.10.30,
    p. 195. *)
Lemma euclidean_last_block_base_orthogonal (R : realType) n
    (p : inner_metric_space (@euclidean_inner_productP R n)) :
  euclidean_inner_product
    (euclidean_block_join (p,(0 : inner_metric_space (@euclidean_inner_productP R 1))))
    (@coordinate_basis R (n+1) (rshift n (ord0 : 'I_1)))=0.
Proof. by rewrite euclidean_inner_basis euclidean_block_join_right ffunE. Qed.
