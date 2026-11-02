(** Federer (1969), 3.2.11, p. 249: the
    prescribed map g(x,z)=f(x)+epsilon*z in the critical-rank
    case. Prove its global Lipschitz bound directly from
    the existing nonexpanding block-coordinate laws. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets topology lra.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerNormInequalities
  InnerMetric EuclideanBlockCoordinates EuclideanBlockLinearMaps EuclideanMetricProduct
  MetricCartesianProductUP LipschitzUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [coarea_perturbation_map]: the map g
    defined in Federer 3.2.11, p. 249. Its Cartesian
    source is represented by the existing isometric block coordinates. *)
Definition coarea_perturbation_map (R:realType) m n
    (f:R_n R m->R_n R n) (e:R) (w:R_n R (m+n)):R_n R n:=
  f (@euclidean_first_block R m n w)+e*:(@euclidean_last_block R m n w).

(** Source for [coarea_perturbation_map_pair]: the exact
    defining equality g(x,z)=f(x)+epsilon*z in Federer
    3.2.11, p. 249, on the actual block pairing. *)
Lemma coarea_perturbation_map_pair (R:realType) m n
    (f:R_n R m->R_n R n) e x z:
  coarea_perturbation_map f e (euclidean_block_join (x,z))=f x+e*:z.
Proof.
change (f ((euclidean_block_split (euclidean_block_join (x,z))).1)+
  e*:(euclidean_block_split (euclidean_block_join (x,z))).2=f x+e*:z).
by rewrite euclidean_block_joinK.
Qed.

(** Source for [coarea_perturbation_map_difference]: supporting
    difference identity for the Lipschitz estimate in Federer
    3.2.11, p. 249. It is purely the algebraic
    difference of the two prescribed map values. *)
Lemma coarea_perturbation_map_difference (R:realType) m n
    (f:R_n R m->R_n R n) e x y:
  coarea_perturbation_map f e x-coarea_perturbation_map f e y=
    (f (@euclidean_first_block R m n x)-f (@euclidean_first_block R m n y))+
    e*:(@euclidean_last_block R m n x-@euclidean_last_block R m n y).
Proof. by rewrite /coarea_perturbation_map opprD addrACA scalerBr. Qed.

(** Source for [coarea_perturbation_map_lipschitz]: the
    global Lipschitz perturbation used in Federer 3.2.11,
    p. 249. Any nonnegative epsilon is allowed for this
    supporting map bound; positive epsilon is used for full rank. *)
Lemma coarea_perturbation_map_lipschitz (R:realType) m n
    (f:inner_metric_space (@euclidean_inner_productP R m)->
      inner_metric_space (@euclidean_inner_productP R n)) e:
  is_metric_lipschitz setT f ->0<=e ->
  is_metric_lipschitz setT (fun w:inner_metric_space (@euclidean_inner_productP R (m+n))=>
    (coarea_perturbation_map f e w:inner_metric_space (@euclidean_inner_productP R n))).
Proof.
move=>[L [hL hBound]] he; exists (L+e); split; first by lra.
split; first by lra.
move=>x y _ _.
pose p:=@euclidean_first_block_map R m n.
pose q:=@euclidean_last_block_map R m n.
pose hN:=@euclidean_inner_productP R n.
have hP:mdist (p x:inner_metric_space (@euclidean_inner_productP R m))
    (p y:inner_metric_space (@euclidean_inner_productP R m))<=mdist x y.
  have h:=(metric_product_first_nonexpanding (@euclidean_blocks_are_metric_product R m n)).2 x y Logic.I Logic.I.
  by rewrite mul1r in h.
have hQ:mdist (q x:inner_metric_space (@euclidean_inner_productP R n))
    (q y:inner_metric_space (@euclidean_inner_productP R n))<=mdist x y.
  have h:=(metric_product_second_nonexpanding (@euclidean_blocks_are_metric_product R m n)).2 x y Logic.I Logic.I.
  by rewrite mul1r in h.
have hF:=hBound.2 (p x) (p y) Logic.I Logic.I.
have hLeft:inner_norm hN (f (p x)-f (p y))<=L*mdist x y.
  exact (le_trans hF (ler_wpM2l hBound.1 hP)).
have hRight:e*inner_norm hN (q x-q y)<=e*mdist x y.
  exact (ler_wpM2l he hQ).
change (is_true (inner_norm hN
  (coarea_perturbation_map f e x-coarea_perturbation_map f e y)<=(L+e)*mdist x y)).
rewrite coarea_perturbation_map_difference.
apply:le_trans (inner_norm_triangle hN _ _) _.
rewrite inner_normZ (ger0_norm he) mulrDl.
exact (lerD hLeft hRight).
Qed.
