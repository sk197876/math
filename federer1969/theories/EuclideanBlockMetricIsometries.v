(** Federer (1969), 3.2.36, p. 273: actual canonical
    block injections preserve the existing Euclidean metric. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets topology.
From Federer Require Import RealMetricBackground GrassmannAbbreviations EuclideanInnerProduct InnerMetric Bilinear
  EuclideanBlockLinearMaps EuclideanBlockNorms.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [euclidean_first_injection_metric]: the first canonical
    isometric embedding used in Federer 3.2.36, p. 273. The
    already proved linear and norm laws identify actual distances,
    including zero-dimensional source or complementary block. *)
Lemma euclidean_first_injection_metric (R:realType) m n
    (x y:inner_metric_space (@euclidean_inner_productP R m)):
  @mdist R (inner_metric_space (@euclidean_inner_productP R (m+n)))
    (@euclidean_first_injection R m n x) (@euclidean_first_injection R m n y)=mdist x y.
Proof.
rewrite !inner_metric_distanceE
  -(@linB R (R_n R m) (R_n R (m+n)) (@euclidean_first_injection R m n)
    (@euclidean_first_injection_linear R m n) x y).
exact:euclidean_first_injection_norm.
Qed.

(** Source for [euclidean_last_injection_metric]: the complementary
    canonical isometric embedding used in Federer 3.2.36,
    p. 273, follows from its existing linear and norm laws.
    Both empty coordinate block cases are retained. *)
Lemma euclidean_last_injection_metric (R:realType) m n
    (x y:inner_metric_space (@euclidean_inner_productP R n)):
  @mdist R (inner_metric_space (@euclidean_inner_productP R (m+n)))
    (@euclidean_last_injection R m n x) (@euclidean_last_injection R m n y)=mdist x y.
Proof.
rewrite !inner_metric_distanceE
  -(@linB R (R_n R n) (R_n R (m+n)) (@euclidean_last_injection R m n)
    (@euclidean_last_injection_linear R m n) x y).
exact:euclidean_last_injection_norm.
Qed.
