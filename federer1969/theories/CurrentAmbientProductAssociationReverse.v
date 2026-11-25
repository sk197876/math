(** Federer (1969), 4.1.11, p. 366: reverse
    the preceding natural Cartesian association by its
    original inverse coordinate identification. Reuse the
    forward current law and inverse-image equation. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws NormRegularity
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct EuclideanCoordinateLists
  EuclideanDimensionCastLinear CurrentSpaces CurrentDegreeTransport CurrentCompactPushforwardAlgebra
  CurrentCompactInverseImageEquation CurrentAmbientCartesianProduct CurrentAmbientProductAssociation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentAmbientProductAssociationReverse.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables m n v i j k:nat.
Local Notation Full := (fun d:nat=>fun _:R_n R d=>True).
Local Notation hFull := (fun (d:nat) (x:R_n R d) (_:True)=>
  @norm_full_domain_interior R (R_n R d) (inner_norm (@euclidean_inner_productP R d)) x).
Variables (S:@current_space R h2 m (Full m) (hFull m) i)
  (T:@current_space R h2 n (Full n) (hFull n) j)
  (U:@current_space R h2 v (Full v) (hFull v) k).
Hypothesis hS:@compact (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R m)))
  (@current_support R h2 m (Full m) (hFull m) i S).
Hypothesis hT:@compact (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n)))
  (@current_support R h2 n (Full n) (hFull n) j T).
Hypothesis hU:@compact (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R v)))
  (@current_support R h2 v (Full v) (hFull v) k U).
Local Notation ST := (@current_ambient_cartesian_product R h2 m n i j S T).
Local Notation TU := (@current_ambient_cartesian_product R h2 n v j k T U).
Local Notation hST := (@current_ambient_cartesian_product_compact R h2 m n i j S T hS hT).
Local Notation hTU := (@current_ambient_cartesian_product_compact R h2 n v j k T U hT hU).
Local Notation Left := (@current_ambient_cartesian_product R h2 (m+n)%N v (i+j)%N k ST U).
Local Notation Right := (@current_ambient_cartesian_product R h2 m (n+v)%N i (j+k)%N S TU).
Local Notation hLeft := (@current_ambient_cartesian_product_compact R h2 (m+n)%N v (i+j)%N k ST U hST hU).
Local Notation hRight := (@current_ambient_cartesian_product_compact R h2 m (n+v)%N i (j+k)%N S TU hS hTU).
Local Notation eDim := (esym (addnA m n v)).
Local Notation Assoc := (@euclidean_dimension_cast_map R ((m+n)+v)%N (m+(n+v))%N eDim).
Local Notation InverseMap := (@euclidean_dimension_cast_map R (m+(n+v))%N ((m+n)+v)%N (esym eDim)).
Local Notation AssocClass := (@euclidean_dimension_cast_smooth R ((m+n)+v)%N (m+(n+v))%N
  eDim (Full ((m+n)+v)%N) (hFull ((m+n)+v)%N)).
Local Notation InverseMapClass := (@euclidean_dimension_cast_smooth R (m+(n+v))%N ((m+n)+v)%N
  (esym eDim) (Full (m+(n+v))%N) (hFull (m+(n+v))%N)).
Local Notation Image := (fun (x:R_n R (m+(n+v))%N) (_:True)=>Logic.I).

(** Source for [current_ambient_product_association_reverse]: the
    inverse original coordinate map sends S times (T times U)
    back to (S times T) times U, with only
    the corresponding degree identification, supporting
    Federer 4.1.11, p. 366. *)
Lemma current_ambient_product_association_reverse:
  @current_degree_transport R h2 ((m+n)+v)%N (Full ((m+n)+v)%N) (hFull ((m+n)+v)%N)
    (i+(j+k))%N ((i+j)+k)%N (esym (esym (addnA i j k)))
    (@current_compact_map_pushforward R h2 (m+(n+v))%N ((m+n)+v)%N
      (Full (m+(n+v))%N) (Full ((m+n)+v)%N) (hFull (m+(n+v))%N) (hFull ((m+n)+v)%N)
      InverseMap Image InverseMapClass (i+(j+k))%N Right hRight)=Left.
Proof.
have hInverse:cancel Assoc InverseMap by move=>x;exact:(@euclidean_dimension_castK R ((m+n)+v)%N (m+(n+v))%N eDim x).
have hForward:=@current_ambient_product_association R h2 m n v i j k S T U hS hT hU.
exact:(@current_compact_inverse_image_equation R h2 ((m+n)+v)%N (m+(n+v))%N
  Assoc InverseMap AssocClass InverseMapClass hInverse ((i+j)+k)%N Left hLeft
  (i+(j+k))%N (esym (addnA i j k)) Right hRight hForward).
Qed.
End CurrentAmbientProductAssociationReverse.
