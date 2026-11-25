(** Federer (1969), 4.1.20, p. 378: for the original
    invertible orthogonal map, spt(g#T)=g(spt T), and
    g#T=0 implies T=0. Reuse the already proved compact
    inverse-image equation of 4.1.11, p. 366, and the
    support-image law of 4.1.7, p. 359. The supporting
    theorem retains arbitrary inverse smooth Euclidean maps. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  NormRegularity NormOpenDomainLaws InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct CurrentSpaces
  CurrentCompactMapProper CurrentCompactPushforwardAlgebra CurrentCompactPushforwardImages
  CurrentCompactInverseImageEquation CurrentPushforwardSupport
  CurrentDegreeTransport CurrentDegreeTransportIdentity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section InverseSupport.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n nu k:nat.
Local Notation X:=(R_n R n).
Local Notation Y:=(R_n R nu).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R n)).
Local Notation NY:=(inner_norm (@euclidean_inner_productP R nu)).
Local Notation UX:=(fun _:X=>True).
Local Notation UY:=(fun _:Y=>True).
Local Notation hX:=(fun (x:X) (_:True)=>norm_full_domain_interior NX x).
Local Notation hY:=(fun (y:Y) (_:True)=>norm_full_domain_interior NY y).
Variables (f:X->Y) (g:Y->X).
Hypothesis hf:norm_class_all_orders (inner_norm_real_norm (@euclidean_inner_productP R n))
  (inner_norm_real_norm (@euclidean_inner_productP R nu)) UX f.
Hypothesis hg:norm_class_all_orders (inner_norm_real_norm (@euclidean_inner_productP R nu))
  (inner_norm_real_norm (@euclidean_inner_productP R n)) UY g.
Hypothesis hFG:cancel f g.
Hypothesis hGF:cancel g f.
Variable T:@current_space R h2 n UX hX k.
Hypothesis hT:@compact (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n)))
  (@current_support R h2 n UX hX k T).
Local Notation fImage:=(fun (x:X) (_:True)=>Logic.I).
Local Notation gImage:=(fun (y:Y) (_:True)=>Logic.I).
Local Notation S:=(@current_compact_map_pushforward R h2 n nu UX UY hX hY f fImage hf k T hT).
Local Notation hS:=(@current_compact_map_image_compact R h2 n nu UX UY hX hY f fImage hf k T hT).
Local Notation Back:=(@current_compact_map_pushforward R h2 nu n UY UX hY hX g gImage hg k S hS).

(** Source for [current_compact_mutual_inverse_recovery]:
    the inverse orthogonal image recovers T in the last
    sentence of Federer 4.1.20, p. 378. This is the already
    proved compact inverse-image equation, without finite mass. *)
Lemma current_compact_mutual_inverse_recovery:Back=T.
Proof.
have hEquation:@current_degree_transport R h2 nu UY hY k k (erefl k) S=S.
  by rewrite current_degree_transport_identity.
have h:=@current_compact_inverse_image_equation R h2 n nu f g hf hg hFG
  k T hT k (erefl k) S hS hEquation.
by rewrite current_degree_transport_identity in h.
Qed.

(** Source for [current_compact_inverse_support]: the exact
    original support identity spt(g#T)=g(spt T), used in
    Federer 4.1.20, p. 378. Both inclusions follow from the
    earlier support-image theorem and inverse recovery. *)
Theorem current_compact_inverse_support:
  @current_support R h2 nu UY hY k S=f @` (@current_support R h2 n UX hX k T).
Proof.
apply/seteqP;split.
- exact:(@current_pushforward_support_image R h2 n nu k UX UY hX hY T
    f fImage hf (@current_compact_map_proper R h2 n nu k UX UY hX T
      f fImage (norm_class_continuous (hf 0%N)) hT)).
- move=>y [x hx <-].
  have hBack:@current_support R h2 n UX hX k Back x.
    by rewrite current_compact_mutual_inverse_recovery.
  have[z hz hzx]:=@current_pushforward_support_image R h2 nu n k UY UX hY hX S
    g gImage hg (@current_compact_map_proper R h2 nu n k UY UX hY S
      g gImage (norm_class_continuous (hg 0%N)) hS) x hBack.
  have hPoint:f x=z by rewrite -hzx hGF.
  by rewrite hPoint.
Qed.

(** Source for [current_compact_inverse_image_zero]: the final
    implication g#T=0 -> T=0 in Federer 4.1.20, p. 378,
    from the original inverse image and zero-image law. *)
Theorem current_compact_inverse_image_zero:S=0->T=0.
Proof.
move=>hZero.
have hBackZero:=@current_compact_map_pushforward_zero R h2 nu n UY UX hY hX
  g gImage hg k S hS hZero.
by rewrite current_compact_mutual_inverse_recovery in hBackZero.
Qed.
End InverseSupport.
