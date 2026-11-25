(** Federer (1969), 4.1.11, p. 366: an
    original signed image equation in the first factor
    gives the corresponding compact Cartesian product
    image. Reuse full product naturality and bilinearity. *)
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
Section CurrentAmbientFirstImageEquation.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables m n p:nat.
Local Notation Full := (fun d:nat=>fun _:R_n R d=>True).
Local Notation hFull := (fun (d:nat) (x:R_n R d) (_:True)=>
  @norm_full_domain_interior R (R_n R d) (inner_norm (@euclidean_inner_productP R d)) x).
Variable f:R_n R m->R_n R n.
Hypothesis hf:norm_class_all_orders (inner_norm_real_norm (@euclidean_inner_productP R m))
  (inner_norm_real_norm (@euclidean_inner_productP R n)) (Full m) f.
Local Notation Id := (fun x:R_n R p=>x).
Local Notation IdGlobal := (@current_join_slice_identity_smooth R p).
Local Notation IdClass := (@current_cartesian_factor_open_class R p p (Full p) (hFull p) Id IdGlobal).
Local Notation FClass := (@current_cartesian_factor_open_class R m n (Full m) (hFull m) f hf).
Local Notation IdImage := (fun (x:R_n R p) (_:True)=>Logic.I).
Local Notation FImage := (fun (x:R_n R m) (_:True)=>Logic.I).
Local Notation Map := (@euclidean_cartesian_map R m p n p f Id).
Local Notation Image := (fun (x:R_n R (m+p)%N) (_:True)=>Logic.I).
Local Notation MapClass := (@current_cartesian_map_smooth R m p n p f Id hf IdGlobal).
Variables k a:nat.
Variable S:@current_space R h2 m (Full m) (hFull m) k.
Variable T:@current_space R h2 p (Full p) (hFull p) a.
Hypothesis hS:@compact (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R m)))
  (@current_support R h2 m (Full m) (hFull m) k S).
Hypothesis hT:@compact (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R p)))
  (@current_support R h2 p (Full p) (hFull p) a T).
Local Notation Product := (@current_ambient_cartesian_product R h2 m p k a S T).
Local Notation hProduct := (@current_ambient_cartesian_product_compact R h2 m p k a S T hS hT).
Local Notation FS := (@current_compact_map_pushforward R h2 m n (Full m) (Full n)
  (hFull m) (hFull n) f FImage hf k S hS).

(** Source for [current_ambient_product_first_image_equation]:
    the preceding exact image in the first factor gives
    the exact original product image, supporting the
    iterated-join expansion in Federer 4.1.11, p. 366.
    Only equal degrees are identified; every compact
    current and every real coefficient is retained. *)
Lemma current_ambient_product_first_image_equation l (e:k=l) c
    (W:@current_space R h2 n (Full n) (hFull n) l)
    (hW:@compact (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n)))
      (@current_support R h2 n (Full n) (hFull n) l W)):
  @current_degree_transport R h2 n (Full n) (hFull n) k l e FS=c*:W->
  @current_degree_transport R h2 (n+p)%N (Full (n+p)%N) (hFull (n+p)%N)
    (k+a)%N (l+a)%N (congr2 addn e (erefl a))
    (@current_compact_map_pushforward R h2 (m+p)%N (n+p)%N (Full (m+p)%N) (Full (n+p)%N)
      (hFull (m+p)%N) (hFull (n+p)%N) Map Image MapClass (k+a)%N Product hProduct)=
  c*:@current_ambient_cartesian_product R h2 n p l a W T.
Proof.
case:l /e in W hW *;rewrite !current_degree_transport_identity=>hEquation.
have hNatural:=@current_ambient_product_pushforward R h2 m p n p f Id hf IdGlobal k a S T hS hT.
have hId:=@current_compact_identity_pushforward R h2 p (Full p) (hFull p)
  a T hT IdImage IdClass (@current_compact_map_proper R h2 p p a
    (Full p) (Full p) (hFull p) T Id IdImage (norm_class_continuous (IdClass 0%N)) hT).
change (@current_compact_map_pushforward R h2 p p (Full p) (Full p) (hFull p) (hFull p)
  Id IdImage IdClass a T hT=T) in hId.
have hClass:FClass=hf:=Prop_irrelevance _ _.
rewrite hId hClass hEquation in hNatural.
rewrite (bilZl (@current_ambient_cartesian_product_bilinear R h2 n p k a)) in hNatural.
exact:hNatural.
Qed.
End CurrentAmbientFirstImageEquation.
