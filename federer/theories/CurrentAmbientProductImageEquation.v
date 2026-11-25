(** Federer (1969), 4.1.11, p. 366: an
    original signed image equation may be used beside
    another compact Cartesian factor. Reuse the full
    product naturality law, bilinearity and identity image. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom TensorUP Bilinear RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws NormRegularity
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct EuclideanCartesianMap
  CurrentSpaces CurrentDegreeTransport CurrentDegreeTransportIdentity CurrentCartesianMapClass
  CurrentCartesianMapPullback CurrentCompactMapProper CurrentCompactPushforwardAlgebra
  CurrentElementaryPushforwards CurrentAmbientCartesianProduct CurrentAmbientProductPushforward
  CurrentJoinSliceMapClass.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentAmbientProductImageEquation.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables m n p:nat.
Local Notation Full := (fun d:nat=>fun _:R_n R d=>True).
Local Notation hFull := (fun (d:nat) (x:R_n R d) (_:True)=>
  @norm_full_domain_interior R (R_n R d) (inner_norm (@euclidean_inner_productP R d)) x).
Variable f:R_n R n->R_n R p.
Hypothesis hf:norm_class_all_orders (inner_norm_real_norm (@euclidean_inner_productP R n))
  (inner_norm_real_norm (@euclidean_inner_productP R p)) (Full n) f.
Local Notation Id := (fun x:R_n R m=>x).
Local Notation IdGlobal := (@current_join_slice_identity_smooth R m).
Local Notation IdClass := (@current_cartesian_factor_open_class R m m (Full m) (hFull m) Id IdGlobal).
Local Notation FClass := (@current_cartesian_factor_open_class R n p (Full n) (hFull n) f hf).
Local Notation IdImage := (fun (x:R_n R m) (_:True)=>Logic.I).
Local Notation FImage := (fun (x:R_n R n) (_:True)=>Logic.I).
Local Notation Map := (@euclidean_cartesian_map R m n m p Id f).
Local Notation Image := (fun (x:R_n R (m+n)%N) (_:True)=>Logic.I).
Local Notation MapClass := (@current_cartesian_map_smooth R m n m p Id f IdGlobal hf).
Variables a k:nat.
Variable S:@current_space R h2 m (Full m) (hFull m) a.
Variable T:@current_space R h2 n (Full n) (hFull n) k.
Hypothesis hS:@compact (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R m)))
  (@current_support R h2 m (Full m) (hFull m) a S).
Hypothesis hT:@compact (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n)))
  (@current_support R h2 n (Full n) (hFull n) k T).
Local Notation Product := (@current_ambient_cartesian_product R h2 m n a k S T).
Local Notation hProduct := (@current_ambient_cartesian_product_compact R h2 m n a k S T hS hT).
Local Notation FT := (@current_compact_map_pushforward R h2 n p (Full n) (Full p)
  (hFull n) (hFull p) f FImage hf k T hT).

(** Source for [current_ambient_product_second_image_equation]:
    the preceding exact signed image in the second factor
    gives the corresponding original product image,
    supporting the time-factor reorderings in Federer
    4.1.11, p. 366. Equal natural degrees alone
    are transported, and both inputs are arbitrary compact currents. *)
Lemma current_ambient_product_second_image_equation l (e:k=l) c
    (W:@current_space R h2 p (Full p) (hFull p) l)
    (hW:@compact (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R p)))
      (@current_support R h2 p (Full p) (hFull p) l W)):
  @current_degree_transport R h2 p (Full p) (hFull p) k l e FT=c*:W->
  @current_degree_transport R h2 (m+p)%N (Full (m+p)%N) (hFull (m+p)%N)
    (a+k)%N (a+l)%N (congr2 addn (erefl a) e)
    (@current_compact_map_pushforward R h2 (m+n)%N (m+p)%N (Full (m+n)%N) (Full (m+p)%N)
      (hFull (m+n)%N) (hFull (m+p)%N) Map Image MapClass (a+k)%N Product hProduct)=
  c*:@current_ambient_cartesian_product R h2 m p a l S W.
Proof.
case:l /e in W hW *;rewrite !current_degree_transport_identity=>hEquation.
have hNatural:=@current_ambient_product_pushforward R h2 m n m p Id f IdGlobal hf a k S T hS hT.
have hId:=@current_compact_identity_pushforward R h2 m (Full m) (hFull m)
  a S hS IdImage IdClass (@current_compact_map_proper R h2 m m a
    (Full m) (Full m) (hFull m) S Id IdImage (norm_class_continuous (IdClass 0%N)) hS).
change (@current_compact_map_pushforward R h2 m m (Full m) (Full m) (hFull m) (hFull m)
  Id IdImage IdClass a S hS=S) in hId.
have hClass:FClass=hf:=Prop_irrelevance _ _.
rewrite hId hClass hEquation in hNatural.
rewrite (bilZr (@current_ambient_cartesian_product_bilinear R h2 m p a k)) in hNatural.
exact:hNatural.
Qed.
End CurrentAmbientProductImageEquation.
