(** Federer (1969), 3.3.5, p. 292: the sharp Lipschitz bound
    for the actual orthogonal graph, including empty coordinate blocks. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology lra.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  EuclideanBlockCoordinates EuclideanBlockLinear ConcatenatedFamilies LipschitzUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [structure_orthogonal_graph_sharp_lipschitz]: the final
    verification in Federer 3.3.5, p. 292. If the transverse graph map
    has bound C and C squared plus one equals L squared, its actual
    Euclidean graph has the sharp bound L. This retains the orthogonal
    sum of squares rather than using the weaker sum of norms. *)
Theorem structure_orthogonal_graph_sharp_lipschitz (R:realType) m k
    (g:inner_metric_space (@euclidean_inner_productP R m)->
      inner_metric_space (@euclidean_inner_productP R k)) (C L:R):
  is_metric_lipschitz_bound setT g C ->0<=L ->C^+2+1=L^+2 ->
  @is_metric_lipschitz_bound R
    (inner_metric_space (@euclidean_inner_productP R m))
    (inner_metric_space (@euclidean_inner_productP R (k+m))) setT
    (fun y=>@euclidean_block_join R k m (g y,y)) L.
Proof.
move=>hG hL hSquares; split=>// x y _ _.
rewrite !inner_metric_distanceE.
have hDiff:@euclidean_block_join R k m (g x,x)-@euclidean_block_join R k m (g y,y)=
    @euclidean_block_join R k m (g x-g y,x-y).
  apply:euclidean_block_vectors_ext.
  - move=>i; by rewrite euclidean_block_join_left !ffunE !concatenate_family_l.
  - move=>i; by rewrite euclidean_block_join_right !ffunE !concatenate_family_r.
rewrite hDiff.
have hEnergy:(inner_norm (@euclidean_inner_productP R (k+m))
    (@euclidean_block_join R k m (g x-g y,x-y)))^+2=
    (inner_norm (@euclidean_inner_productP R k) (g x-g y))^+2+
    (inner_norm (@euclidean_inner_productP R m) (x-y))^+2.
  by rewrite inner_norm_sqr euclidean_block_join_inner /=
    -(inner_norm_sqr (@euclidean_inner_productP R k))
    -(inner_norm_sqr (@euclidean_inner_productP R m)).
have hBound:=hG.2 x y I I; rewrite !inner_metric_distanceE in hBound.
have hN:0<=inner_norm (@euclidean_inner_productP R m) (x-y):=inner_norm_nonnegative _ _.
have hGN:0<=inner_norm (@euclidean_inner_productP R k) (g x-g y):=inner_norm_nonnegative _ _.
have hRight:0<=L*inner_norm (@euclidean_inner_productP R m) (x-y):=mulr_ge0 hL hN.
rewrite -(ler_sqr (inner_norm_nonnegative _ _) hRight) hEnergy exprMn.
have hSquareBound:(inner_norm (@euclidean_inner_productP R k) (g x-g y))^+2<=
    C^+2*(inner_norm (@euclidean_inner_productP R m) (x-y))^+2 by nra.
nra.
Qed.
