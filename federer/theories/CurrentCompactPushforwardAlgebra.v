(** Federer (1969), 4.1.11, pp. 365–366: the original
    smooth pushforward acts linearly on compact currents and
    respects equal degrees. These supporting laws are direct
    consequences of the preceding support-proper pushforward;
    no new current construction is used. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  NormClassOneUP NormRegularity InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct CurrentSpaces
  CurrentProperSupport CurrentCompactMapProper CurrentPushforwardSealed
  CurrentPushforwardCongruence CurrentPushforwardLinear
  CurrentDegreeTransport CurrentPushforwardDegreeTransport CurrentZeroPushforward.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

Section CurrentCompactPushforwardAlgebra.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables v n:nat.
Variables (U:set (R_n R v)) (V:set (R_n R n)).
Hypothesis hU:forall x,U x->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R v)) U x.
Hypothesis hV:forall y,V y->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) V y.
Variable f:R_n R v->R_n R n.
Hypothesis hImage:forall x,U x->V (f x).
Hypothesis hf:norm_class_all_orders
  (inner_norm_real_norm (@euclidean_inner_productP R v))
  (inner_norm_real_norm (@euclidean_inner_productP R n)) U f.
Local Notation C := (fun k=>@current_space R h2 v U hU k).
Local Notation D := (fun k=>@current_space R h2 n V hV k).
Local Notation Compact := (fun k (T:C k)=>@compact
  (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R v)))
  (@current_support R h2 v U hU k T)).
Local Notation Proper := (fun k (T:C k) (hT:Compact k T)=>
  @current_compact_map_proper R h2 v n k U V hU T f hImage
    (norm_class_continuous (hf 0%N)) hT).

(** Source for [current_compact_map_pushforward]: the original
    f#T for compactly supported T, used throughout the join and
    simplex identities of Federer 4.1.11, pp. 365–366. This alias
    supplies the already proved support-properness witness. *)
Definition current_compact_map_pushforward k (T:C k) (hT:Compact k T):D k:=
  @CurrentPushforward.value R h2 v n k U V hU hV T f hImage hf (Proper k T hT).

(** Source for [current_compact_map_pushforward_congruence]:
    equal compact currents have the same original image, with
    any compactness witnesses, supporting Federer 4.1.11, p. 365. *)
Lemma current_compact_map_pushforward_congruence k (T S:C k)
    (hT:Compact k T) (hS:Compact k S):
  T=S->current_compact_map_pushforward hT=current_compact_map_pushforward hS.
Proof. exact:current_pushforward_current_congruence. Qed.

(** Source for [current_compact_map_pushforward_linear]: the
    original f#(cT+S)=c f#T+f#S on compact currents, supporting
    the boundary and simplex calculations of Federer 4.1.11,
    pp. 365–366. Reuse the preceding linearity theorem. *)
Lemma current_compact_map_pushforward_linear k c (T S:C k)
    (hT:Compact k T) (hS:Compact k S) (hSum:Compact k (c*:T+S)):
  current_compact_map_pushforward hSum=
    c*:current_compact_map_pushforward hT+current_compact_map_pushforward hS.
Proof. exact:current_pushforward_linear. Qed.

(** Source for [current_compact_map_pushforward_right_linear]:
    the same preceding linearity with the scalar term written
    second, supporting the original ordering of the join boundary
    and simplex formulas in Federer 4.1.11, pp. 365–366. *)
Lemma current_compact_map_pushforward_right_linear k c (T S:C k)
    (hT:Compact k T) (hS:Compact k S) (hSum:Compact k (T+c*:S)):
  current_compact_map_pushforward hSum=
    current_compact_map_pushforward hT+c*:current_compact_map_pushforward hS.
Proof.
have hSwap:Compact k (c*:S+T) by rewrite addrC.
have hEqual:=current_compact_map_pushforward_congruence hSum hSwap (addrC T (c*:S)).
have hLinear:=current_compact_map_pushforward_linear hS hT hSwap.
by rewrite hEqual hLinear addrC.
Qed.

(** Source for [current_compact_map_pushforward_subtract]: the
    original image of a difference is the difference of images,
    supporting the endpoint and alternating simplex formulas in
    Federer 4.1.11, pp. 365–366. Compactness witnesses may differ. *)
Lemma current_compact_map_pushforward_subtract k (T S:C k)
    (hT:Compact k T) (hS:Compact k S) (hDifference:Compact k (T-S)):
  current_compact_map_pushforward hDifference=
    current_compact_map_pushforward hT-current_compact_map_pushforward hS.
Proof.
have hSum:Compact k (T+(-1:R)*:S) by rewrite scaleN1r.
have h:=current_compact_map_pushforward_right_linear hT hS hSum.
have hEqual:T+(-1:R)*:S=T-S by rewrite scaleN1r.
have hPush:=current_compact_map_pushforward_congruence hSum hDifference hEqual.
by rewrite hPush scaleN1r in h.
Qed.

(** Source for [current_compact_map_pushforward_add]: the
    original image of a sum is the sum of images, supporting
    the boundary and simplex formulas in Federer 4.1.11,
    pp. 365–366. This is the scalar-one linearity case. *)
Lemma current_compact_map_pushforward_add k (T S:C k)
    (hT:Compact k T) (hS:Compact k S) (hSum:Compact k (T+S)):
  current_compact_map_pushforward hSum=
    current_compact_map_pushforward hT+current_compact_map_pushforward hS.
Proof.
have hCombination:Compact k (1*:T+S) by rewrite scale1r.
have h:=current_compact_map_pushforward_linear hT hS hCombination.
have hEqual:1*:T+S=T+S by rewrite scale1r.
have hPush:=current_compact_map_pushforward_congruence hCombination hSum hEqual.
by rewrite hPush scale1r in h.
Qed.

(** Source for [current_compact_map_pushforward_degree]: identify
    equal degrees before or after the original pushforward, as
    required by the join and simplex identities in Federer
    4.1.11, pp. 365–366. Only degree bookkeeping is involved. *)
Lemma current_compact_map_pushforward_degree k l (e:k=l) (T:C k)
    (hT:Compact k T)
    (hCast:Compact l (@current_degree_transport R h2 v U hU k l e T)):
  @current_degree_transport R h2 n V hV k l e (current_compact_map_pushforward hT)=
    current_compact_map_pushforward hCast.
Proof. exact:current_pushforward_degree_transport. Qed.

(** Source for [current_compact_map_pushforward_zero]: the
    original image of a zero current is zero, supporting endpoint
    cancellations in Federer 4.1.11, p. 365. This uses the
    previously proved all-test zero-pushforward law. *)
Lemma current_compact_map_pushforward_zero k (T:C k) (hT:Compact k T):
  T=0->current_compact_map_pushforward hT=0.
Proof. exact:current_pushforward_of_zero. Qed.
End CurrentCompactPushforwardAlgebra.
