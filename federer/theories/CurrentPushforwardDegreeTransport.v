(** Federer (1969), 4.1.11, p. 365: equal natural degrees
    in the original join boundary formulas are identified through
    the existing public current transports. Such bookkeeping changes
    neither support properness nor the actual proper pushforward. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP
  NormRegularity InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct CurrentSpaces
  CurrentDegreeTransport CurrentDegreeTransportIdentity
  CurrentProperSupport CurrentPushforwardSealed CurrentPushforwardCongruence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

Section CurrentPushforwardDegreeTransport.
Variable R : realType.
Hypothesis h2 : (1+1:R)!=0.
Variables n nu : nat.
Variables (U : set (R_n R n)) (V : set (R_n R nu)).
Hypothesis hU : forall x, U x -> norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) U x.
Hypothesis hV : forall y, V y -> norm_domain_interior
  (inner_norm (@euclidean_inner_productP R nu)) V y.
Variable f : R_n R n -> R_n R nu.
Hypothesis hImage : forall x, U x -> V (f x).
Hypothesis hf : norm_class_all_orders
  (inner_norm_real_norm (@euclidean_inner_productP R n))
  (inner_norm_real_norm (@euclidean_inner_productP R nu)) U f.
Local Notation C := (fun k => @current_space R h2 n U hU k).
Local Notation SourceTr := (fun k l (e : k=l) =>
  @current_degree_transport R h2 n U hU k l e).
Local Notation TargetTr := (fun k l (e : k=l) =>
  @current_degree_transport R h2 nu V hV k l e).
Local Notation Proper := (fun k (T : C k) =>
  @is_current_proper_on_support R h2 n nu k U hU V T f hImage).

(** Source for [current_degree_transport_proper]: identifying
    equal original current degrees preserves support properness,
    supporting Federer 4.1.11, p. 365. No current or map changes. *)
Theorem current_degree_transport_proper k l (e : k=l) (T : C k) :
  Proper k T -> Proper l (SourceTr _ _ e T).
Proof.
case: l / e.
by rewrite current_degree_transport_identity.
Qed.

(** Source for [current_pushforward_degree_transport]: the
    original proper pushforward commutes with equal-degree
    identification, supporting Federer 4.1.11, p. 365. Every
    admissible properness proof is permitted on both sides. *)
Theorem current_pushforward_degree_transport k l (e : k=l) (T : C k)
    (hp : Proper k T) (hq : Proper l (SourceTr _ _ e T)) :
  TargetTr _ _ e
    (@CurrentPushforward.value R h2 n nu k U V hU hV T f hImage hf hp) =
  @CurrentPushforward.value R h2 n nu l U V hU hV
    (SourceTr _ _ e T) f hImage hf hq.
Proof.
case: l / e in hq *.
rewrite !current_degree_transport_identity.
exact: (@current_pushforward_current_congruence R h2 n nu k
  U V hU hV f hImage hf T T hp hq (erefl T)).
Qed.
End CurrentPushforwardDegreeTransport.
