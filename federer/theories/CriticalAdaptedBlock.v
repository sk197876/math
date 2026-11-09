(** Federer (1969), 3.4.2(8), p. 316: changing only
    the p(Z) coordinate block gives an original Z-fibre. *)
From mathcomp Require Import all_boot all_order all_algebra reals topology.
From Federer Require Import ModuleQuotient GrassmannAbbreviations EuclideanInnerProduct
  GrassmannSubspaces EuclideanBlockCoordinates EuclideanBlockLinear EuclideanMetricProduct ConcatenatedFamilies.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [critical_adapted_first_block_difference]: the
    intermediate point x=g(u+b) in 3.4.2(8), p. 316,
    differs from the centre only in its p(Z) coordinates.
    This supporting identity uses the actual adapted linear
    map and proves the subspace condition from its first-block law. *)
Lemma critical_adapted_first_block_difference (R:realType) a b
    (A:G (R_n R (a+b)) a) (H:{linear R_n R (a+b)->R_n R (a+b)}):
  (forall z:R_n R (a+b),(forall i:'I_(a+b),(a<=i)%N ->z i=0) ->
    grassmann_val A (H z)) ->
  forall (u v:R_n R a) (w:R_n R b),
    grassmann_val A (H (euclidean_block_join (u,w))-H (euclidean_block_join (v,w))).
Proof.
move=>hFirst u v w.
have hDifference:euclidean_block_join (u,w)-euclidean_block_join (v,w)=
    euclidean_block_join (u-v,(0:R_n R b)).
  rewrite -euclidean_block_join_difference.
  congr euclidean_block_join;change ((u-v,w-w)=(u-v,0));by rewrite subrr.
rewrite -linearB hDifference;apply:hFirst=>i hi.
rewrite -(splitK i) in hi *;case:(split i) hi=>j hi.
- have hSmall:(j<a)%N:=ltn_ord j.
  have hIndex:(a<=j)%N:=hi.
  by have:=leq_ltn_trans hIndex hSmall;rewrite ltnn.
- have hIndex:unsplit (inr j)=rshift a j by apply:val_inj.
  rewrite hIndex.
  by rewrite euclidean_block_join_right ffunE.
Qed.
