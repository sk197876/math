(** Federer (1969), 3.2.3, pp. 243–244: the
    graph map g(x)=(f(x),epsilon x) and its differential.
    Use the existing Euclidean block injections and exact
    differential calculus, including zero-dimensional blocks. *)
From mathcomp Require Import all_boot all_order all_algebra reals lra.
From Federer Require Import Hom TensorUP GrassmannAbbreviations EuclideanInnerProduct InnerProductUP
  InnerNorm InnerNormInequalities HilbertFormCompactness Bilinear RealNormUP
  EuclideanBlockCoordinates EuclideanBlockLinear EuclideanBlockLinearMaps EuclideanBlockNorms
  NormDifferentialUP NormDifferentialLinear NormDifferentialArithmetic NormDifferentialFiniteCalculus
  NormClassOneUP InnerMetric LipschitzUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section Graph.
Variable R:realType.
Variables m n:nat.
Let X:=R_n R m.
Let Y:=R_n R n.
Let Z:=R_n R (n+m).
Let I:=@euclidean_first_injection_map R n m.
Let K:=@euclidean_last_injection_map R n m.
Let P:=@euclidean_first_block_map R n m.
Let Q:=@euclidean_last_block_map R n m.
Let NX:=inner_norm (@euclidean_inner_productP R m).
Let NY:=inner_norm (@euclidean_inner_productP R n).
Let NZ:=inner_norm (@euclidean_inner_productP R (n+m)).

(** Source for [euclidean_graph_lift]: the map g in
    Federer 3.2.3, pp. 243–244, expressed through
    the already specified orthogonal block injections. *)
Definition euclidean_graph_lift (f:X->Y) (e:R) (x:X):Z:=I (f x)+e*:K x.

(** Source for [euclidean_linear_graph_lift]: the
    differential v |-> (Df(x)v,epsilon v) in
    Federer 3.2.3, p. 244. *)
Definition euclidean_linear_graph_lift (L:Hom X Y) (e:R):Hom X Z:=hom_comp I L+e*:K.

(** Source for [euclidean_linear_graph_liftE]: the
    displayed differential formula for the graph map,
    Federer 3.2.3, p. 244. *)
Lemma euclidean_linear_graph_liftE (L:Hom X Y) e v:
  euclidean_linear_graph_lift L e v=euclidean_graph_lift L e v.
Proof. by rewrite /euclidean_linear_graph_lift /euclidean_graph_lift hom_addE hom_compE hom_scaleE. Qed.

(** Source for [euclidean_graph_lift_first]: the
    projection p satisfies p composed with g=f,
    Federer 3.2.3, pp. 243–244. *)
Lemma euclidean_graph_lift_first (f:X->Y) e x:P (euclidean_graph_lift f e x)=f x.
Proof.
rewrite /euclidean_graph_lift linearD linearZ.
change (euclidean_first_block (@euclidean_first_injection R n m (f x))+
  e*:euclidean_first_block (@euclidean_last_injection R n m x)=f x).
by rewrite euclidean_first_block_injectionK euclidean_first_block_last_injection scaler0 addr0.
Qed.

(** Source for [euclidean_graph_lift_last]: the
    last coordinate of g is epsilon x in
    Federer 3.2.3, p. 244. *)
Lemma euclidean_graph_lift_last (f:X->Y) e x:Q (euclidean_graph_lift f e x)=e*:x.
Proof.
rewrite /euclidean_graph_lift linearD linearZ.
change (euclidean_last_block (@euclidean_first_injection R n m (f x))+
  e*:euclidean_last_block (@euclidean_last_injection R n m x)=e*:x).
by rewrite euclidean_last_block_first_injection euclidean_last_block_injectionK add0r.
Qed.

(** Source for [euclidean_graph_lift_join]: the
    printed Cartesian expression for g in
    Federer 3.2.3, pp. 243–244. *)
Lemma euclidean_graph_lift_join (f:X->Y) e x:
  euclidean_graph_lift f e x=euclidean_block_join (f x,e*:x).
Proof.
have hSplit:euclidean_block_split (euclidean_graph_lift f e x)=(f x,e*:x).
  apply:injective_projections; [exact:euclidean_graph_lift_first|exact:euclidean_graph_lift_last].
by rewrite -(euclidean_block_splitK (euclidean_graph_lift f e x)) hSplit.
Qed.

(** Source for [euclidean_graph_lift_injective]: the
    graph differential is univalent for positive epsilon,
    Federer 3.2.3, p. 244. In fact the graph
    map itself is injective for every nonzero epsilon. *)
Lemma euclidean_graph_lift_injective (f:X->Y) e:e!=0 -> injective (euclidean_graph_lift f e).
Proof.
move=>he x y hxy.
have hh:=congr1 (fun z:Z=>e^-1*:Q z) hxy.
by rewrite !euclidean_graph_lift_last !scalerA mulVf // !scale1r in hh.
Qed.

(** Source for [euclidean_graph_lift_norm_bound]: the
    estimate of the graph map by its two block norms,
    used for Lip(g)<=Lip(f)+epsilon in Federer 3.2.3,
    p. 244. *)
Lemma euclidean_graph_lift_norm_bound (f:X->Y) e x:
  NZ (euclidean_graph_lift f e x)<=NY (f x)+`|e|*NX x.
Proof.
apply:le_trans (inner_norm_triangle (@euclidean_inner_productP R (n+m)) _ _) _.
rewrite inner_normZ.
change (inner_norm (@euclidean_inner_productP R (n+m)) (@euclidean_first_injection R n m (f x))+
  `|e|*inner_norm (@euclidean_inner_productP R (n+m)) (@euclidean_last_injection R n m x)<=NY (f x)+`|e|*NX x).
by rewrite euclidean_first_injection_norm euclidean_last_injection_norm.
Qed.

(** Source for [euclidean_graph_lift_differential]: the
    actual differential of g displayed in Federer 3.2.3,
    p. 244, from linear postcomposition and addition. *)
Theorem euclidean_graph_lift_differential (f:X->Y) e a (L:Hom X Y):
  has_norm_differential NX NY (fun _=>True) f a L ->
  has_norm_differential NX NZ (fun _=>True) (euclidean_graph_lift f e) a
    (euclidean_linear_graph_lift L e).
Proof.
move=>hL.
pose hNX:=inner_norm_real_norm (@euclidean_inner_productP R m).
pose hNZ:=inner_norm_real_norm (@euclidean_inner_productP R (n+m)).
have hI:norm_bounded_linear NY NZ I.
  exists 1; split; first exact:ler01.
  move=>v; change (inner_norm (@euclidean_inner_productP R (n+m)) (@euclidean_first_injection R n m v)<=1*NY v).
  by rewrite euclidean_first_injection_norm mul1r.
have hK:norm_bounded_linear NX NZ (e*:K).
  exists `|e|; split; first exact:normr_ge0.
  move=>v; rewrite hom_scaleE.
  change (inner_norm (@euclidean_inner_productP R (n+m)) (e*:@euclidean_last_injection R n m v)<=`|e|*NX v).
  by rewrite inner_normZ euclidean_last_injection_norm.
have hFirst:=norm_differential_postcompose hNX hL hI.
have hSecond:=@norm_differential_linear R X Z NX NZ hNX hNZ (fun _=>True) a
  (e*:K) (norm_differential_interior hL) hK.
exact (norm_differential_add hNZ hFirst hSecond).
Qed.
End Graph.
