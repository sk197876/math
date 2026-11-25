(** Federer (1969), 3.3.4, p. 290:
    the independently specified active inclusion
    preserves the actual Euclidean inner product.
    No implementation or selected completion
    of its orthonormal frame is used. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct
  EuclideanBlockLinearMaps OrthogonalMaps StructureActiveCoordinatesUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [structure_active_inclusion_orthogonal]:
    the coordinate inclusion onto the actual
    active span X is orthogonal, Federer
    3.3.4, p. 290. Its m original
    coordinates and distinguished normal coordinate
    give precisely the original inner product;
    all other normal coordinates vanish. *)
Theorem structure_active_inclusion_orthogonal (R:realType) m k (j:'I_k)
    (w:Hom (R_n R (1+m)) (R_n R (m+k))):
  is_structure_active_inclusion j w ->
  is_orthogonal_map (@euclidean_inner_product R (1+m))
    (@euclidean_inner_product R (m+k)) (hom_as_linear w).
Proof.
move=>hW u v.
change (euclidean_inner_product (w u) (w v)=euclidean_inner_product u v).
rewrite /euclidean_inner_product big_split_ord.
have hFirst:(\sum_i (w u) (lshift k i)*(w v) (lshift k i))=
    \sum_i u (rshift 1 i)*v (rshift 1 i).
  apply:eq_bigr=>i _.
  have hU:=congr1 (fun z:R_n R m=>z i) (hW u).1.
  have hV:=congr1 (fun z:R_n R m=>z i) (hW v).1.
  by move:hU hV; rewrite /euclidean_first_block /euclidean_last_block !ffunE=>-> ->.
have hLast:(\sum_l (w u) (rshift m l)*(w v) (rshift m l))=
    u (lshift m (ord0:'I_1))*v (lshift m (ord0:'I_1)).
  have hU l:(w u) (rshift m l)=if l==j then u (lshift m (ord0:'I_1)) else 0.
    have h:=(hW u).2 l; by rewrite /euclidean_last_block ffunE in h.
  have hV l:(w v) (rshift m l)=if l==j then v (lshift m (ord0:'I_1)) else 0.
    have h:=(hW v).2 l; by rewrite /euclidean_last_block ffunE in h.
  rewrite (bigD1 j)//= hU hV eqxx /=.
  rewrite big1 ?addr0=>// l hlj.
  by rewrite hU hV (negbTE hlj) mul0r.
rewrite hFirst hLast [RHS]big_split_ord big_ord1.
change ((\sum_i u (rshift 1 i)*v (rshift 1 i))+
  u (lshift m (ord0:'I_1))*v (lshift m (ord0:'I_1))=
  u (lshift m (ord0:'I_1))*v (lshift m (ord0:'I_1))+
  (\sum_i u (rshift 1 i)*v (rshift 1 i))).
exact:addrC.
Qed.
