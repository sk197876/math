(** Federer (1969), 4.1.11, p. 366: invert
    an original compact-current image equation when the
    reverse coordinate map is a left inverse. Reuse
    proper composition, map agreement and the identity
    image, retaining equal-degree bookkeeping. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws NormRegularity
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct CurrentSpaces
  CurrentDegreeTransport CurrentDegreeTransportIdentity CurrentCompactMapProper
  CurrentCompactPushforwardAlgebra CurrentCompactPushforwardImages CurrentElementaryPushforwards
  CurrentJoinSliceMapClass SmoothFormPullbackComposition.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentCompactInverseImageEquation.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables m n:nat.
Local Notation Full := (fun d:nat=>fun _:R_n R d=>True).
Local Notation hFull := (fun (d:nat) (x:R_n R d) (_:True)=>
  @norm_full_domain_interior R (R_n R d) (inner_norm (@euclidean_inner_productP R d)) x).
Variables (f:R_n R m->R_n R n) (g:R_n R n->R_n R m).
Hypothesis hf:norm_class_all_orders (inner_norm_real_norm (@euclidean_inner_productP R m))
  (inner_norm_real_norm (@euclidean_inner_productP R n)) (Full m) f.
Hypothesis hg:norm_class_all_orders (inner_norm_real_norm (@euclidean_inner_productP R n))
  (inner_norm_real_norm (@euclidean_inner_productP R m)) (Full n) g.
Hypothesis hInverse:cancel f g.
Local Notation FImage := (fun (x:R_n R m) (_:True)=>Logic.I).
Local Notation GImage := (fun (x:R_n R n) (_:True)=>Logic.I).
Local Notation CompositeImage := (@current_smooth_composite_image R m n m
  (Full m) (Full n) (Full m) f g FImage GImage).
Local Notation CompositeClass := (@current_smooth_composite_class R m n m
  (Full m) (Full n) f g FImage hf hg).
Variable k:nat.
Variable T:@current_space R h2 m (Full m) (hFull m) k.
Hypothesis hT:@compact (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R m)))
  (@current_support R h2 m (Full m) (hFull m) k T).
Local Notation FT := (@current_compact_map_pushforward R h2 m n (Full m) (Full n)
  (hFull m) (hFull n) f FImage hf k T hT).
Local Notation hFT := (@current_compact_map_image_compact R h2 m n (Full m) (Full n)
  (hFull m) (hFull n) f FImage hf k T hT).

(** Source for [current_compact_inverse_image_equation]: the
    reverse of an original invertible coordinate image
    equation is exact on the original compact currents,
    supporting associativity in Federer 4.1.11, p. 366.
    Only a left inverse and the displayed image equation
    are needed; neither integration nor finite mass is imposed. *)
Lemma current_compact_inverse_image_equation l (e:k=l)
    (W:@current_space R h2 n (Full n) (hFull n) l)
    (hW:@compact (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n)))
      (@current_support R h2 n (Full n) (hFull n) l W)):
  @current_degree_transport R h2 n (Full n) (hFull n) k l e FT=W->
  @current_degree_transport R h2 m (Full m) (hFull m) l k (esym e)
    (@current_compact_map_pushforward R h2 n m (Full n) (Full m) (hFull n) (hFull m)
      g GImage hg l W hW)=T.
Proof.
case:l /e in W hW *;rewrite !current_degree_transport_identity=>hEquation.
have hCompose:=@current_compact_map_images_compose R h2 m n m
  (Full m) (Full n) (Full m) (hFull m) (hFull n) (hFull m)
  f g FImage GImage hf hg k T hT hFT.
have hReplace:=@current_compact_map_pushforward_congruence R h2 n m
  (Full n) (Full m) (hFull n) (hFull m) g GImage hg k FT W hFT hW hEquation.
pose Id:=fun x:R_n R m=>x.
pose IdClass:=@current_join_slice_identity_smooth R m.
pose IdImage:=fun (x:R_n R m) (_:True)=>Logic.I.
have hMaps:=@current_compact_map_images_agree R h2 m m
  (Full m) (Full m) (hFull m) (hFull m) (fun x=>g (f x)) CompositeImage CompositeClass
  k T hT Id IdImage IdClass hT (fun x _=>hInverse x).
have hId:=@current_compact_identity_pushforward R h2 m (Full m) (hFull m)
  k T hT IdImage IdClass (@current_compact_map_proper R h2 m m k
    (Full m) (Full m) (hFull m) T Id IdImage (norm_class_continuous (IdClass 0%N)) hT).
change (@current_compact_map_pushforward R h2 m m (Full m) (Full m) (hFull m) (hFull m)
  Id IdImage IdClass k T hT=T) in hId.
exact:(eq_trans (esym hReplace) (eq_trans (esym hCompose) (eq_trans hMaps hId))).
Qed.
End CurrentCompactInverseImageEquation.
