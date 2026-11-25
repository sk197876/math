(** Federer (1969), 4.1.11, p. 366: retain
    the preceding graded Cartesian interchange law on
    equal whole-space domains. No new product or
    representation hypothesis is introduced. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom TensorUP Bilinear RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws NormRegularity
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct EuclideanCartesianMap
  EuclideanCartesianSwapLinear CurrentSpaces CurrentCartesianDomain CurrentCartesianSwapDomain
  CurrentCartesianProductSealed CurrentCartesianCompactCurrents CurrentCartesianCompactIdentities
  CurrentCompactPushforwardAlgebra CurrentCompactMapDomainTransport CurrentDomainTransport
  CurrentDomainTransportDegree CurrentDegreeTransport CurrentAmbientCartesianProduct.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section CurrentAmbientProductSwap.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables m n i j:nat.
Local Notation Full := (fun d:nat=>fun _:R_n R d=>True).
Local Notation hFull := (fun (d:nat) (x:R_n R d) (_:True)=>
  @norm_full_domain_interior R (R_n R d) (inner_norm (@euclidean_inner_productP R d)) x).
Local Notation AB := (@euclidean_cartesian_set R m n (Full m) (Full n)).
Local Notation BA := (@euclidean_cartesian_set R n m (Full n) (Full m)).
Local Notation hAB := (@current_cartesian_domain_open R m n (Full m) (Full n) (hFull m) (hFull n)).
Local Notation hBA := (@current_cartesian_domain_open R n m (Full n) (Full m) (hFull n) (hFull m)).
Variables (S:@current_space R h2 m (Full m) (hFull m) i)
  (T:@current_space R h2 n (Full n) (hFull n) j).
Hypothesis hS:@compact (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R m)))
  (@current_support R h2 m (Full m) (hFull m) i S).
Hypothesis hT:@compact (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n)))
  (@current_support R h2 n (Full n) (hFull n) j T).
Local Notation Raw := (@CartesianCurrentProduct.value R h2 m n i j
  (Full m) (Full n) (hFull m) (hFull n) S T).
Local Notation hRaw := (@current_cartesian_compact_currents R h2 m n i j
  (Full m) (Full n) (hFull m) (hFull n) S T hS hT).
Local Notation Product := (@current_ambient_cartesian_product R h2 m n i j S T).
Local Notation hProduct := (@current_ambient_cartesian_product_compact R h2 m n i j S T hS hT).
Local Notation Swap := (@euclidean_cartesian_swap_map R m n).
Local Notation OldImage := (fun z hz=>@current_cartesian_swap_image R m n (Full m) (Full n) z hz).
Local Notation Image := (fun (z:R_n R (m+n)%N) (_:True)=>Logic.I).
Local Notation OldClass := (@euclidean_cartesian_swap_smooth R m n AB hAB).
Local Notation SwapClass := (@euclidean_cartesian_swap_smooth R m n (Full (m+n)%N) (hFull (m+n)%N)).
Local Notation Tr := (fun k=>@current_domain_transport R h2 (n+m)%N BA hBA
  (Full (n+m)%N) (@current_cartesian_full_domain R n m) (hFull (n+m)%N) k).

(** Source for [current_ambient_product_swap]: the exact
    original graded interchange sign (-1)^(ij) holds on
    the equal full Euclidean presentations, supporting
    the time-factor reorderings in Federer 4.1.11,
    p. 366. Zero degrees and empty Euclidean
    blocks retain the preceding product law. *)
Lemma current_ambient_product_swap:
  @current_degree_transport R h2 (n+m)%N (Full (n+m)%N) (hFull (n+m)%N)
    (i+j)%N (j+i)%N (addnC i j)
    (@current_compact_map_pushforward R h2 (m+n)%N (n+m)%N
      (Full (m+n)%N) (Full (n+m)%N) (hFull (m+n)%N) (hFull (n+m)%N)
      Swap Image SwapClass (i+j)%N Product hProduct)=
    (-1:R)^+(i*j)*:@current_ambient_cartesian_product R h2 n m j i T S.
Proof.
have hOld:=@current_cartesian_compact_swap R h2 m n (Full m) (Full n) (hFull m) (hFull n)
  i j S T hRaw OldImage OldClass.
have hDomains:=@current_compact_map_domain_transport R h2 (m+n)%N (n+m)%N
  AB (Full (m+n)%N) BA (Full (n+m)%N) hAB (hFull (m+n)%N) hBA (hFull (n+m)%N)
  (@current_cartesian_full_domain R m n) (@current_cartesian_full_domain R n m)
  Swap OldImage Image OldClass SwapClass (i+j)%N Raw hRaw hProduct.
have hTransport:=congr1 (Tr (j+i)%N) hOld.
rewrite current_domain_transport_degree -hDomains in hTransport.
rewrite (linZ (hom_linear (Tr (j+i)%N))) in hTransport.
exact:hTransport.
Qed.
End CurrentAmbientProductSwap.
