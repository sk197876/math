(** Federer (1969), 4.1.11, p. 366: the original
    Cartesian product of full-space currents, on the
    whole Euclidean product. Identify only equal domain
    presentations; retain the preceding opaque product. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom TensorUP Bilinear RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct EuclideanCartesianMap
  CurrentSpaces CurrentCartesianDomain CurrentCartesianProductSealed CurrentCartesianProductBilinear
  CurrentCartesianCompactCurrents CurrentDomainTransport.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [current_cartesian_full_domain]: the
    full Cartesian domain is the whole Euclidean space,
    supporting the prism formula in Federer 4.1.11,
    p. 366. Empty Euclidean blocks are included. *)
Theorem current_cartesian_full_domain (R:realType) m n:
  @euclidean_cartesian_set R m n (fun _=>True) (fun _=>True)=
    (fun _:R_n R (m+n)%N=>True).
Proof. apply:funext=>z;apply:propext;split=>_;by []. Qed.

Section CurrentAmbientCartesianProduct.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables m n:nat.
Local Notation Full := (fun d:nat=>fun _:R_n R d=>True).
Local Notation hFull := (fun (d:nat) (x:R_n R d) (_:True)=>
  @norm_full_domain_interior R (R_n R d) (inner_norm (@euclidean_inner_productP R d)) x).
Local Notation AB := (@euclidean_cartesian_set R m n (Full m) (Full n)).
Local Notation hAB := (@current_cartesian_domain_open R m n (Full m) (Full n) (hFull m) (hFull n)).
Local Notation CA := (fun k=>@current_space R h2 m (Full m) (hFull m) k).
Local Notation CB := (fun k=>@current_space R h2 n (Full n) (hFull n) k).
Local Notation CC := (fun k=>@current_space R h2 (m+n)%N (Full (m+n)%N) (hFull (m+n)%N) k).
Local Notation CTr := (fun k=>@current_domain_transport R h2 (m+n)%N AB hAB
  (Full (m+n)%N) (@current_cartesian_full_domain R m n) (hFull (m+n)%N) k).

(** Source for [current_ambient_cartesian_product]: the
    original Cartesian product on the whole Euclidean
    product space, supporting Federer 4.1.11, p. 366.
    Its only adapter transports equality of domains. *)
Definition current_ambient_cartesian_product i j (S:CA i) (T:CB j):CC (i+j)%N:=
  CTr (i+j)%N (@CartesianCurrentProduct.value R h2 m n i j
    (Full m) (Full n) (hFull m) (hFull n) S T).

(** Source for [current_ambient_cartesian_product_bilinear]:
    the original full-space product is bilinear, supporting
    Federer 4.1.11, p. 366, by the proved product
    law of 4.1.8, p. 361. *)
Theorem current_ambient_cartesian_product_bilinear i j:
  bilinear (@current_ambient_cartesian_product i j).
Proof.
split.
- move=>T c S U;rewrite /current_ambient_cartesian_product
    current_cartesian_product_first_linear.
  exact:(hom_linear (CTr (i+j)%N) c _ _).
- move=>S c T U;rewrite /current_ambient_cartesian_product
    current_cartesian_product_second_linear.
  exact:(hom_linear (CTr (i+j)%N) c _ _).
Qed.

(** Source for [current_ambient_cartesian_product_compact]:
    compact factors have compact original Cartesian product,
    supporting the top-degree prism proof in Federer
    4.1.11, p. 366. No measure representation is assumed. *)
Theorem current_ambient_cartesian_product_compact i j (S:CA i) (T:CB j):
  @compact (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R m)))
    (@current_support R h2 m (Full m) (hFull m) i S)->
  @compact (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n)))
    (@current_support R h2 n (Full n) (hFull n) j T)->
  @compact (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R (m+n)%N)))
    (@current_support R h2 (m+n)%N (Full (m+n)%N) (hFull (m+n)%N) (i+j)%N
      (current_ambient_cartesian_product S T)).
Proof.
move=>hS hT;rewrite /current_ambient_cartesian_product current_domain_transport_support.
exact:(@current_cartesian_compact_currents R h2 m n i j
  (Full m) (Full n) (hFull m) (hFull n) S T hS hT).
Qed.
End CurrentAmbientCartesianProduct.
