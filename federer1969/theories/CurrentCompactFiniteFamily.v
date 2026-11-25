(** Federer (1969), 4.1.11, p. 366: finite
    compact sums and their original smooth images.
    Identify a finite family with its existing ordinal
    enumeration; reuse the preceding finite-sum laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormRegularity
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct CurrentSpaces
  CurrentCompactFiniteSum CurrentCompactMapFiniteSum CurrentCompactPushforwardAlgebra.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section CurrentCompactFiniteFamily.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables m n:nat.
Variables (U:set (R_n R m)) (V:set (R_n R n)).
Hypothesis hU:forall x,U x->norm_domain_interior (inner_norm (@euclidean_inner_productP R m)) U x.
Hypothesis hV:forall y,V y->norm_domain_interior (inner_norm (@euclidean_inner_productP R n)) V y.
Variable k:nat.
Local Notation C := (@current_space R h2 m U hU k).
Local Notation Compact := (fun T:C=>@compact
  (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R m)))
  (@current_support R h2 m U hU k T)).

(** Source for [current_compact_finite_family]: every finite
    family of original compact currents has compact sum,
    supporting the rectangular decomposition in Federer
    4.1.11, p. 366. Empty families are retained. *)
Lemma current_compact_finite_family (I:finType) (T:I->C):
  (forall r,Compact (T r))->Compact (\sum_r T r).
Proof.
move=>hT.
rewrite (big_enum_val (A:=predT) T).
exact:(@current_compact_finite_sum R h2 m k U hU #|I|
  (fun r=>T (enum_val r)) (fun r=>hT (enum_val r))).
Qed.

(** Source for [current_compact_weighted_finite_family]: arbitrary
    real coefficients preserve compactness of the original
    finite sum, supporting Federer 4.1.11, p. 366. *)
Lemma current_compact_weighted_finite_family (I:finType) (a:I->R) (T:I->C):
  (forall r,Compact (T r))->Compact (\sum_r a r*:T r).
Proof.
move=>hT.
rewrite (big_enum_val (A:=predT) (fun r=>a r*:T r)).
exact:(@current_compact_weighted_finite_sum R h2 m k U hU #|I|
  (fun r=>a (enum_val r)) (fun r=>T (enum_val r)) (fun r=>hT (enum_val r))).
Qed.

Variable f:R_n R m->R_n R n.
Hypothesis hImage:forall x,U x->V (f x).
Hypothesis hf:norm_class_all_orders (inner_norm_real_norm (@euclidean_inner_productP R m))
  (inner_norm_real_norm (@euclidean_inner_productP R n)) U f.
Local Notation Push := (fun (T:C) (hT:Compact T)=>
  @current_compact_map_pushforward R h2 m n U V hU hV f hImage hf k T hT).

(** Source for [current_compact_map_weighted_family]: the
    actual smooth image commutes with each original
    finite weighted family, supporting affine rectangular
    decomposition in Federer 4.1.11, p. 366. Properness
    is needed only on the compact supports. *)
Lemma current_compact_map_weighted_family (I:finType) (a:I->R) (T:I->C)
    (hT:forall r,Compact (T r)) (hSum:Compact (\sum_r a r*:T r)):
  Push (\sum_r a r*:T r) hSum=\sum_r a r*:Push (T r) (hT r).
Proof.
pose A:=fun r:'I_#|I|=>a (enum_val r).
pose S:=fun r:'I_#|I|=>T (enum_val r).
pose hS:=fun r:'I_#|I|=>hT (enum_val r).
pose hOrdinalSum:=@current_compact_weighted_finite_sum R h2 m k U hU #|I| A S hS.
have hSumEquality:(\sum_r a r*:T r)=\sum_r A r*:S r.
  exact:(big_enum_val (A:=predT) (fun r=>a r*:T r)).
have hInput:=@current_compact_map_pushforward_congruence R h2 m n U V hU hV f hImage hf k
  (\sum_r a r*:T r) (\sum_r A r*:S r) hSum hOrdinalSum hSumEquality.
have hImageSum:=@current_compact_map_weighted_sum R h2 m n U V hU hV f hImage hf k
  #|I| A S hS hOrdinalSum.
rewrite hInput hImageSum [RHS]big_enum_val.
by [].
Qed.
End CurrentCompactFiniteFamily.
