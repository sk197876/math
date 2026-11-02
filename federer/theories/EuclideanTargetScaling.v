(** Federer (1969), 2.10.43, printed p. 201: reduce a positive Lipschitz
    bound to one by scaling the target, then scale the extension back. These
    supporting homogeneity laws follow from the project's abstract
    inner-product norm. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets topology.
From Federer Require Import EuclideanInnerProduct InnerNorm InnerMetric LipschitzUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_scaled_distance]: supporting
    target scaling for the initial normalisation in
    2.10.43, p. 201. Distances are multiplied
    by the absolute value of the scalar. *)
Lemma euclidean_scaled_distance (R : realType) n (a : R)
    (x y : inner_metric_space (@euclidean_inner_productP R n)) :
  mdist (a*:x) (a*:y)=`|a|*mdist x y.
Proof. by rewrite !inner_metric_distanceE -scalerBr inner_normZ. Qed.

(** Source for [euclidean_scaled_lipschitz_bound]: supporting
    scaling of the original map and its extension
    in 2.10.43, p. 201. Zero scalar and
    zero bound are retained. *)
Lemma euclidean_scaled_lipschitz_bound (R : realType) m n
    (S : set (inner_metric_space (@euclidean_inner_productP R m)))
    (f : inner_metric_space (@euclidean_inner_productP R m) ->
      inner_metric_space (@euclidean_inner_productP R n)) (L a : R) :
  is_metric_lipschitz_bound S f L ->
  is_metric_lipschitz_bound S (fun x=>a*:f x) (`|a|*L).
Proof.
move=> [hL hf]; split; first exact: mulr_ge0 (normr_ge0 _) hL.
move=> x y hx hy; rewrite euclidean_scaled_distance -mulrA.
exact (ler_wpM2l (normr_ge0 a) (hf x y hx hy)).
Qed.
