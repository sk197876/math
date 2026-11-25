(** Federer (1969), 4.1.11, p. 366: an
    original segment on a containing domain equal to
    the whole Euclidean space is the same full-space
    segment. Identify only equal domains and proof parameters. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormOpenDomainLaws
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct CurrentSpaces
  CurrentDomainTransport CurrentDomainTransportIdentity CurrentSegmentMapUP OrientedSegmentCurrentSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [current_segment_full_domain_transport]: retain
    the original oriented segment under an equal whole-
    domain presentation, supporting the rectangular sum
    in Federer 4.1.11, p. 366. Endpoints may coincide
    and the Euclidean dimension may be zero. *)
Lemma current_segment_full_domain_transport (R:realType) (h2:(1+1:R)!=0) n
    (U:set (R_n R n))
    (hU:forall x,U x->norm_domain_interior (inner_norm (@euclidean_inner_productP R n)) U x)
    (e:U=(fun _=>True)) (u v:R_n R n)
    (hUV:@is_current_segment_domain R n U u v):
  @current_domain_transport R h2 n U hU (fun _=>True) e
    (fun x (_:True)=>@norm_full_domain_interior R (R_n R n)
      (inner_norm (@euclidean_inner_productP R n)) x) 1%N
    (@OrientedSegmentCurrent.value R h2 n U hU u v hUV)=
  @OrientedSegmentCurrent.value R h2 n (fun _=>True)
    (fun x (_:True)=>@norm_full_domain_interior R (R_n R n)
      (inner_norm (@euclidean_inner_productP R n)) x) u v
    (fun (t:R) (_:t \in `[0,1])=>Logic.I).
Proof.
subst U.
pose hFull:=fun (x:R_n R n) (_:True)=>@norm_full_domain_interior R (R_n R n)
  (inner_norm (@euclidean_inner_productP R n)) x.
have hOpen:hU=hFull:=Prop_irrelevance _ _;subst hU.
rewrite current_domain_transport_identity.
have hContains:hUV=(fun (t:R) (_:t \in `[0,1])=>Logic.I):=Prop_irrelevance _ _.
by rewrite hContains.
Qed.
