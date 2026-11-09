(** Federer (1969), 3.3.4, pp. 290–291:
    the actual active projection has precisely
    the distinguished normal coordinate and
    the first m original coordinates. Derive
    the formula from the abstract inclusion
    and public adjoint pairing alone. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct
  InnerProductUP InnerProductLaws AdjointUP AdjointLaws EuclideanRectangularAdjoint
  EuclideanBlockCoordinates EuclideanBlockLinearMaps StructureActiveCoordinatesUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [structure_active_projection_coordinates]:
    the coordinate description of the actual
    projection q onto X in Federer 3.3.4,
    pp. 290–291. The orthogonal coordinate
    copy orders g_j before g_1,...,g_m;
    it retains every original ambient coordinate. *)
Theorem structure_active_projection_coordinates (R:realType) m k (j:'I_k)
    (w:Hom (R_n R (1+m)) (R_n R (m+k))):
  is_structure_active_inclusion j w ->forall x,
    euclidean_rectangular_adjoint w x=
      @euclidean_block_join R 1 m
        ([ffun _: 'I_1=>x (rshift m j)],@euclidean_first_block R m k x).
Proof.
move=>hW x; apply:(inner_vectors_ext (@euclidean_inner_productP R (1+m)))=>u.
rewrite euclidean_rectangular_adjoint_pairing /euclidean_inner_product
  [LHS]big_split_ord [RHS]big_split_ord big_ord1.
have hFirst:(\sum_i (w u) (lshift k i)*x (lshift k i))=
    \sum_i u (rshift 1 i)*x (lshift k i).
  apply:eq_bigr=>i _.
  have h:=congr1 (fun z:R_n R m=>z i) (hW u).1.
  by rewrite /euclidean_first_block /euclidean_last_block !ffunE in h; rewrite h.
have hLast:(\sum_l (w u) (rshift m l)*x (rshift m l))=
    u (lshift m (ord0:'I_1))*x (rshift m j).
  have hU l:(w u) (rshift m l)=if l==j then u (lshift m (ord0:'I_1)) else 0.
    have h:=(hW u).2 l; by rewrite /euclidean_last_block ffunE in h.
  rewrite (bigD1 j)//= hU eqxx /=.
  rewrite big1 ?addr0=>// l hlj; by rewrite hU (negbTE hlj) mul0r.
rewrite hFirst hLast euclidean_block_join_left ffunE.
have hTail:(\sum_i u (rshift 1 i)*
    (@euclidean_block_join R 1 m
      ([ffun _: 'I_1=>x (rshift m j)],@euclidean_first_block R m k x)) (rshift 1 i))=
    \sum_i u (rshift 1 i)*x (lshift k i).
  apply:eq_bigr=>i _; by rewrite euclidean_block_join_right /euclidean_first_block ffunE.
rewrite hTail.
change ((\sum_i u (rshift 1 i)*x (lshift k i))+
    u (lshift m (ord0:'I_1))*x (rshift m j)=
    u (lshift m (ord0:'I_1))*x (rshift m j)+
    (\sum_i u (rshift 1 i)*x (lshift k i))).
exact:addrC.
Qed.
