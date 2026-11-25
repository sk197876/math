(** Federer (1969), 3.2.23, p. 260: the map f times g
    and its Cartesian domain, expressed through the existing orthogonal
    block identification of 2.6.5, p. 120. These coordinate formulas
    introduce no new selected object or replacement product metric. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  EuclideanBlockCoordinates EuclideanMetricProduct LipschitzUP LipschitzBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_cartesian_set]: the subset W times Z of
    R^n times R^v in Federer 3.2.23, p. 260, under the usual
    orthogonal identification with R^(n+v), 2.6.5, p. 120. *)
Definition euclidean_cartesian_set (R:realType) n v
    (W:set (R_n R n)) (Z:set (R_n R v)):set (R_n R (n+v)):=
  (@euclidean_block_split R n v) @^-1` (W `*` Z).

(** Source for [euclidean_cartesian_map]: the componentwise map
    f times g in the proof of Federer 3.2.23, p. 260.
    Both coordinate maps are the previously specified block isomorphism. *)
Definition euclidean_cartesian_map (R:realType) m mu n v
    (f:R_n R m->R_n R n) (g:R_n R mu->R_n R v)
    (p:R_n R (m+mu)):R_n R (n+v):=
  euclidean_block_join (f (euclidean_block_split p).1,g (euclidean_block_split p).2).

(** Source for [euclidean_cartesian_map_coordinates]: supporting
    exact coordinate evaluation for f times g in Federer 3.2.23,
    p. 260; the two blocks may be empty. *)
Lemma euclidean_cartesian_map_coordinates (R:realType) m mu n v
    (f:R_n R m->R_n R n) (g:R_n R mu->R_n R v) p:
  euclidean_block_split (euclidean_cartesian_map f g p)=
    (f (euclidean_block_split p).1,g (euclidean_block_split p).2).
Proof. exact:euclidean_block_joinK. Qed.

(** Source for [euclidean_cartesian_map_image]: the image of
    A times B under f times g is f(A) times g(B), supporting
    the displayed area calculation of Federer 3.2.23, p. 260.
    This exact set identity requires no measurability or injectivity. *)
Lemma euclidean_cartesian_map_image (R:realType) m mu n v
    (f:R_n R m->R_n R n) (g:R_n R mu->R_n R v)
    (A:set (R_n R m)) (B:set (R_n R mu)):
  euclidean_cartesian_map f g @` euclidean_cartesian_set A B=
    euclidean_cartesian_set (f @` A) (g @` B).
Proof.
apply/seteqP; split.
- move=>p [q [hA hB] <-].
  change ((f @` A) (euclidean_block_split (euclidean_cartesian_map f g q)).1 /\
    (g @` B) (euclidean_block_split (euclidean_cartesian_map f g q)).2).
  rewrite euclidean_cartesian_map_coordinates.
  split; [by exists (euclidean_block_split q).1|by exists (euclidean_block_split q).2].
- move=>p [[x hx hfx] [y hy hgy]].
  exists (euclidean_block_join (x,y)).
  + change (A (euclidean_block_split (euclidean_block_join (x,y))).1 /\
      B (euclidean_block_split (euclidean_block_join (x,y))).2).
    by rewrite euclidean_block_joinK; split.
  + rewrite /euclidean_cartesian_map euclidean_block_joinK /= hfx hgy.
    exact:euclidean_block_splitK.
Qed.

(** Source for [euclidean_cartesian_map_lipschitz_bound]: supporting
    Lipschitzness of f times g in Federer 3.2.23, p. 260.
    A common bound L for both factors is also a bound for their
    product in the orthogonal squared product metric. The actual
    factor domains and L=0 boundary are retained. *)
Lemma euclidean_cartesian_map_lipschitz_bound (R:realType) m mu n v
    (f:R_n R m->R_n R n) (g:R_n R mu->R_n R v)
    (A:set (R_n R m)) (B:set (R_n R mu)) (L:R):
  @is_metric_lipschitz_bound R
    (inner_metric_space (@euclidean_inner_productP R m))
    (inner_metric_space (@euclidean_inner_productP R n)) A f L ->
  @is_metric_lipschitz_bound R
    (inner_metric_space (@euclidean_inner_productP R mu))
    (inner_metric_space (@euclidean_inner_productP R v)) B g L ->
  @is_metric_lipschitz_bound R
    (inner_metric_space (@euclidean_inner_productP R (m+mu)))
    (inner_metric_space (@euclidean_inner_productP R (n+v)))
    (euclidean_cartesian_set A B) (euclidean_cartesian_map f g) L.
Proof.
move=>hf hg; have hL0:(0<=L)%R:=hf.1.
split; first exact hL0.
move=>p q [hpA hpB] [hqA hqB].
have hF:=hf.2 _ _ hpA hqA.
have hG:=hg.2 _ _ hpB hqB.
rewrite -ler_sqr ?nnegrE ?mdist_ge0 ?mulr_ge0 //; last exact:mdist_ge0.
rewrite exprMn !euclidean_block_squared_distance !euclidean_cartesian_map_coordinates /= mulrDr.
apply:lerD.
- rewrite -exprMn.
  rewrite ler_sqr ?nnegrE ?mdist_ge0 ?mulr_ge0 //; exact:mdist_ge0.
- rewrite -exprMn.
  rewrite ler_sqr ?nnegrE ?mdist_ge0 ?mulr_ge0 //; exact:mdist_ge0.
Qed.

(** Source for [euclidean_cartesian_map_lipschitz]: existence of
    a global Lipschitz bound for f times g in Federer 3.2.23,
    p. 260. The sum of positive factor bounds suffices. *)
Lemma euclidean_cartesian_map_lipschitz (R:realType) m mu n v
    (f:inner_metric_space (@euclidean_inner_productP R m)->
      inner_metric_space (@euclidean_inner_productP R n))
    (g:inner_metric_space (@euclidean_inner_productP R mu)->
      inner_metric_space (@euclidean_inner_productP R v)):
  is_metric_lipschitz setT f ->is_metric_lipschitz setT g ->
  @is_metric_lipschitz R
    (inner_metric_space (@euclidean_inner_productP R (m+mu)))
    (inner_metric_space (@euclidean_inner_productP R (n+v))) setT (euclidean_cartesian_map f g).
Proof.
move=>[L [hL hf]] [M [hM hg]].
have hF:is_metric_lipschitz_bound setT f (L+M).
  apply:(LipschitzBasic.metric_lipschitz_bound_increase hf).
  by rewrite lerDl; exact:ltW hM.
have hG:is_metric_lipschitz_bound setT g (L+M).
  apply:(LipschitzBasic.metric_lipschitz_bound_increase hg).
  by rewrite lerDr; exact:ltW hL.
have hProduct:=euclidean_cartesian_map_lipschitz_bound hF hG.
have hWhole:euclidean_cartesian_set (@setT (R_n R m)) (@setT (R_n R mu))=setT.
  by apply/seteqP; split=>p; [move=>_|move=>_; split].
rewrite hWhole in hProduct.
exists (L+M); split; first exact:addr_gt0 hL hM.
exact hProduct.
Qed.
