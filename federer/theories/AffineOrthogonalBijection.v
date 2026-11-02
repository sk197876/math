(** Federer (1969), 3.2.36, p. 273: a translated
    finite-dimensional orthogonal endomorphism is an actual metric bijection. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets topology.
From Federer Require Import RealMetricBackground GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  InnerMetric InnerNorm OrthogonalMaps OrthogonalFinite.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [affine_orthogonal_bijection_inverse]: the translated
    orthogonal ambient transformation in the isometry deduction of
    Federer 3.2.36, p. 273. The internal finite-dimensional
    inverse theorem of 1.7.2, p. 28, supplies a local inverse;
    its two cancellation and actual metric laws are proved directly.
    No packaged-group membership or preassigned inverse is assumed. *)
Lemma affine_orthogonal_bijection_inverse (R:realType) n
    (T:{linear R_n R n->R_n R n}) (a:inner_metric_space (@euclidean_inner_productP R n)):
  is_orthogonal_map (@euclidean_inner_product R n) (@euclidean_inner_product R n) T ->
  exists G:inner_metric_space (@euclidean_inner_productP R n)->inner_metric_space (@euclidean_inner_productP R n),
    cancel (fun z=>a+T z) G /\cancel G (fun z=>a+T z) /\
    forall x y,@mdist R (inner_metric_space (@euclidean_inner_productP R n)) (a+T x) (a+T y)=
      @mdist R (inner_metric_space (@euclidean_inner_productP R n)) x y.
Proof.
move=>hT.
have [U [hUT [hTU hU]]]:=@orthogonal_endomorphism_inverse_exists R (R_n R n)
  (@euclidean_inner_product R n) (@euclidean_inner_productP R n) n
  (@coordinate_basis R n) (@coordinate_basisP R n) T hT.
exists (fun z=>U (z-a)); split.
- move=>z; by rewrite [a+T z]addrC addrK hUT.
- split.
  + move=>z; by rewrite hTU addrC subrK.
  + move=>x y; rewrite !inner_metric_distanceE.
    have hDifference:(a+T x)-(a+T y)=T (x-y).
      by rewrite opprD addrACA subrr add0r linearB.
    rewrite hDifference; exact:(@orthogonal_map_norm R (R_n R n) (R_n R n)
      (@euclidean_inner_product R n) (@euclidean_inner_product R n)
      (@euclidean_inner_productP R n) (@euclidean_inner_productP R n) T hT (x-y)).
Qed.
