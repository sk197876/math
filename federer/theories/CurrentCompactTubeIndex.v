(** Federer (1969), 4.1.18, pp. 375–376: the
    original closed support neighbourhoods are actual compact
    indices inside U whenever their carriers lie in U.
    Their carriers use the already specified opaque set
    sum and retain the empty-set case exactly. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct SmoothCompactSet
  EuclideanClosedSupportTube EuclideanClosedSupportTubeNorm.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CompactTube.
Variable R:realType.
Variable n:nat.
Local Notation X:=(R_n R n).
Local Notation hN:=(inner_norm_real_norm (@euclidean_inner_productP R n)).
Variable U:set X.
Variable K:smooth_compact_set hN U.
Variable r:R.
Hypothesis hInside:@euclidean_closed_support_tube R n (smooth_compact_carrier K) r `<=` U.

(** Source for [current_compact_closed_tube_index]:
    the exact compact K_i and E used in
    Federer 4.1.18, pp. 375–376. The
    carrier abbreviates the previously specified closed tube;
    compactness is proved from the original K. *)
Definition current_compact_closed_tube_index:smooth_compact_set hN U:=
  @Build_smooth_compact_set R X
    (inner_norm (@euclidean_inner_productP R n)) hN U
    (@euclidean_closed_support_tube R n (smooth_compact_carrier K) r)
    hInside (@euclidean_closed_support_tube_norm_compact R n
      (smooth_compact_carrier K) r (smooth_compact_is_compact K)).

(** Source for [current_compact_closed_tube_index_carrier]:
    exact recovery of the original neighbourhood carrier,
    supporting both propositions of Federer 4.1.18,
    pp. 375–376, including empty K. *)
Lemma current_compact_closed_tube_index_carrier:
  smooth_compact_carrier current_compact_closed_tube_index=
    @euclidean_closed_support_tube R n (smooth_compact_carrier K) r.
Proof. by []. Qed.

(** Source for [current_compact_closed_tube_index_includes]:
    every nonnegative-radius original neighbourhood contains
    its source compact index, supporting the nested
    K_i of Federer 4.1.18, p. 376. *)
Lemma current_compact_closed_tube_index_includes:
  0<=r->smooth_compact_carrier K `<=`
    smooth_compact_carrier current_compact_closed_tube_index.
Proof. exact:(@euclidean_closed_support_tube_includes R n (smooth_compact_carrier K) r). Qed.
End CompactTube.
