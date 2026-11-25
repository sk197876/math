(** Federer (1969), 4.1.24, p. 380: affine
    coordinate inclusions and projections used to combine
    the original polyhedral source witnesses are globally
    Lipschitz. Reuse the finite-dimensional linear bound
    of 3.1.1(5), p. 210. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions
  classical_sets reals topology.
From Federer Require Import Hom Bilinear RealNormUP NormMetric NormDifferentialUP
  NormFiniteLinearBound InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct FiniteCoordinates
  LipschitzUP LipschitzBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_affine_source_lipschitz]: every affine
    source-coordinate map in the additive assertion of
    4.1.24, p. 380, has a finite global bound,
    including zero-dimensional source and target spaces. *)
Theorem euclidean_affine_source_lipschitz (R:realType) d n
    (L:Hom (R_n R d) (R_n R n)) (c:R_n R n):
  @is_metric_lipschitz R
    (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R d)))
    (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n)))
    setT (fun x=>c+L x).
Proof.
have[C [hC hBound]]:=@norm_finite_linear_bounded R (R_n R d) (R_n R n)
  (inner_norm (@euclidean_inner_productP R d))
  (inner_norm (@euclidean_inner_productP R n))
  (inner_norm_real_norm (@euclidean_inner_productP R d))
  (inner_norm_real_norm (@euclidean_inner_productP R n))
  d (@coordinate_basis R d) (@coordinate_basisP R d) L.
apply:(@metric_lipschitz_of_bound R
  (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R d)))
  (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n)))
  setT (fun x=>c+L x) C).
split;first exact:hC.
move=>x y _ _.
change (is_true (inner_norm (@euclidean_inner_productP R n)
  ((c+L x)-(c+L y))<=C*inner_norm (@euclidean_inner_productP R d) (x-y))).
have hDifference:(c+L x)-(c+L y)=L (x-y).
  by rewrite opprD addrACA subrr add0r (linB (hom_linear L)).
rewrite hDifference;exact:hBound.
Qed.

(** Source for [euclidean_linear_source_lipschitz]: the linear
    projection case of the source-coordinate bound used
    in 4.1.24, p. 380. *)
Corollary euclidean_linear_source_lipschitz (R:realType) d n
    (L:Hom (R_n R d) (R_n R n)):
  @is_metric_lipschitz R
    (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R d)))
    (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n))) setT L.
Proof.
have h:=euclidean_affine_source_lipschitz L (0:R_n R n).
have hMap:(fun x:R_n R d=>(0:R_n R n)+L x)=(L:R_n R d->R_n R n).
  apply:funext=>x;by rewrite add0r.
by rewrite hMap in h.
Qed.
