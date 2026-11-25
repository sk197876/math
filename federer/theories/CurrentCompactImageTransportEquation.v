(** Federer (1969), 4.1.11, p. 366: carry
    an original signed image equation through a further
    compact smooth image. Equal-degree bookkeeping is
    eliminated, then proper composition and linearity
    give the claim. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws NormRegularity
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct CurrentSpaces
  CurrentDegreeTransport CurrentDegreeTransportIdentity CurrentCompactCurrentArithmetic
  CurrentCompactPushforwardAlgebra CurrentCompactPushforwardImages SmoothFormPullbackComposition.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentCompactImageTransportEquation.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables m n p:nat.
Local Notation Full := (fun d:nat=>fun _:R_n R d=>True).
Local Notation hFull := (fun (d:nat) (x:R_n R d) (_:True)=>
  @norm_full_domain_interior R (R_n R d) (inner_norm (@euclidean_inner_productP R d)) x).
Variables (f:R_n R m->R_n R n) (g:R_n R n->R_n R p).
Hypothesis hf:norm_class_all_orders (inner_norm_real_norm (@euclidean_inner_productP R m))
  (inner_norm_real_norm (@euclidean_inner_productP R n)) (Full m) f.
Hypothesis hg:norm_class_all_orders (inner_norm_real_norm (@euclidean_inner_productP R n))
  (inner_norm_real_norm (@euclidean_inner_productP R p)) (Full n) g.
Local Notation FImage := (fun (x:R_n R m) (_:True)=>Logic.I).
Local Notation GImage := (fun (x:R_n R n) (_:True)=>Logic.I).
Local Notation CompositeImage := (@current_smooth_composite_image R m n p
  (Full m) (Full n) (Full p) f g FImage GImage).
Local Notation CompositeClass := (@current_smooth_composite_class R m n p
  (Full m) (Full n) f g FImage hf hg).
Variable k:nat.
Variable T:@current_space R h2 m (Full m) (hFull m) k.
Hypothesis hT:@compact (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R m)))
  (@current_support R h2 m (Full m) (hFull m) k T).
Local Notation FT := (@current_compact_map_pushforward R h2 m n (Full m) (Full n)
  (hFull m) (hFull n) f FImage hf k T hT).
Local Notation hFT := (@current_compact_map_image_compact R h2 m n (Full m) (Full n)
  (hFull m) (hFull n) f FImage hf k T hT).

(** Source for [current_compact_image_transport_equation]: an
    exact original signed current image remains exact
    under a further smooth image, with its equal-degree
    identification, supporting Federer 4.1.11, p. 366.
    No properness beyond compact supports is imposed. *)
Lemma current_compact_image_transport_equation l (e:k=l) c
    (W:@current_space R h2 n (Full n) (hFull n) l)
    (hW:@compact (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n)))
      (@current_support R h2 n (Full n) (hFull n) l W)):
  @current_degree_transport R h2 n (Full n) (hFull n) k l e FT=c*:W->
  @current_degree_transport R h2 p (Full p) (hFull p) k l e
    (@current_compact_map_pushforward R h2 m p (Full m) (Full p) (hFull m) (hFull p)
      (fun x=>g (f x)) CompositeImage CompositeClass k T hT)=
    c*:@current_compact_map_pushforward R h2 n p (Full n) (Full p) (hFull n) (hFull p)
      g GImage hg l W hW.
Proof.
case:l /e in W hW *;rewrite !current_degree_transport_identity=>hEquation.
pose hScaled:=@current_compact_scaled_support R h2 n k (Full n) (hFull n) W c hW.
have hCompose:=@current_compact_map_images_compose R h2 m n p
  (Full m) (Full n) (Full p) (hFull m) (hFull n) (hFull p)
  f g FImage GImage hf hg k T hT hFT.
have hReplace:=@current_compact_map_pushforward_congruence R h2 n p
  (Full n) (Full p) (hFull n) (hFull p) g GImage hg k FT (c*:W) hFT hScaled hEquation.
have hScale:=@current_compact_map_scaled_image R h2 n p
  (Full n) (Full p) (hFull n) (hFull p) g GImage hg k W c hW hScaled.
exact:(eq_trans hCompose (eq_trans hReplace hScale)).
Qed.
End CurrentCompactImageTransportEquation.
