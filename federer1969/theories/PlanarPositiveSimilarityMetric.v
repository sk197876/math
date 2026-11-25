(** Federer (1969), 3.3.20, pp. 307–308: actual positive similarity and its inverse. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  constructive_ereal topology ring num_normedtype pseudometric_normed_Zmodule normed_module.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  InnerNormedTopology MetricDiameterUP MetricDiameter.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_positive_similarity_distance]: the actual
    original similarities scale Euclidean distances, supporting the
    diameter reduction of 3.3.20, pp. 307–308. *)
Lemma euclidean_positive_similarity_distance (R:realType) n (a:R_n R n) (r:R)
    (x y:inner_metric_space (@euclidean_inner_productP R n)):
  0<=r ->@mdist R [the metricType R of inner_metric_space (@euclidean_inner_productP R n)]
    (a+r*:x) (a+r*:y)=r * mdist x y.
Proof.
move=>hr;rewrite !inner_metric_distanceE.
have hDifference:(a+r*:x)-(a+r*:y)=r*:(x-y).
  by rewrite opprD addrACA subrr add0r -scalerBr.
by rewrite hDifference inner_normZ (ger0_norm hr).
Qed.

(** Source for [euclidean_positive_similarity_inverse]: both actual
    inverse identities for the original positive similarity in
    3.3.20, pp. 307–308. The inverse remains local. *)
Lemma euclidean_positive_similarity_inverse (R:realType) n (a:R_n R n) (r:R):
  0<r ->let F:=fun x:inner_metric_space (@euclidean_inner_productP R n)=>a+r*:x in
  let G:=fun x:inner_metric_space (@euclidean_inner_productP R n)=>r^-1*:(x-a) in
  cancel F G /\cancel G F.
Proof.
move=>hr F G;have hNZ:r!=0 by rewrite gt_eqF.
split=>x.
- by rewrite /G /F addrAC subrr add0r scalerA mulVf // scale1r.
- by rewrite /G /F scalerA mulfV // scale1r addrC subrK.
Qed.

(** Source for [euclidean_positive_similarity_preimage_diameter]: an
    arbitrary original test set pulls back with its diameter bound
    divided by the positive similarity scale, 3.3.20, pp. 307–308.
    This supporting bound retains empty and nonmeasurable test sets. *)
Lemma euclidean_positive_similarity_preimage_diameter (R:realType) n
    (a:R_n R n) (r d:R) (T:set (inner_metric_space (@euclidean_inner_productP R n))):
  0<r ->0<=d ->(extended_metric_diameter T<=d%:E)%E ->
  (extended_metric_diameter ((fun x:inner_metric_space (@euclidean_inner_productP R n)=>(a+r*:x)%R) @^-1` T)<=(d/r)%:E)%E.
Proof.
move=>hr hd hT;apply:(metric_diameter_least (extended_metric_diameter_specification _)).
- rewrite lee_fin;exact:divr_ge0 hd (ltW hr).
- move=>x y hx hy.
  have h:=le_trans (metric_diameter_upper (extended_metric_diameter_specification T) hx hy) hT.
  rewrite lee_fin (@euclidean_positive_similarity_distance R n a r x y (ltW hr)) in h.
  rewrite lee_fin ler_pdivlMr //;by rewrite mulrC.
Qed.
