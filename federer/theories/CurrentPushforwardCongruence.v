(** Federer (1969), 4.1.7, p. 359:
    the original pushed current depends only
    on its source current and the
    original map. Uniqueness of the defining
    test action removes dependence on the
    proof of support-properness. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import RealNormUP NormDifferentialUP NormRegularity InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct CurrentSpaces CurrentProperSupport CurrentPushforwardUP
  CurrentPushforwardExistence CurrentPushforwardSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentPushforwardCongruence.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables v n m:nat.
Variables (U:R_n R v->Prop) (V:R_n R n->Prop).
Hypothesis hU:forall x,U x->norm_domain_interior (inner_norm (@euclidean_inner_productP R v)) U x.
Hypothesis hV:forall y,V y->norm_domain_interior (inner_norm (@euclidean_inner_productP R n)) V y.
Variable f:R_n R v->R_n R n.
Hypothesis hImage:forall x,U x->V (f x).
Hypothesis hf:norm_class_all_orders (inner_norm_real_norm (@euclidean_inner_productP R v))
  (inner_norm_real_norm (@euclidean_inner_productP R n)) U f.

(** Source for [current_pushforward_current_congruence]:
    equal actual source currents have equal
    pushforwards, supporting restriction compatibility in
    Federer 4.1.7, p. 359. The
    two properness proofs may differ. *)
Theorem current_pushforward_current_congruence
    (T S:@current_space R h2 v U hU m)
    (hT:@is_current_proper_on_support R h2 v n m U hU V T f hImage)
    (hS:@is_current_proper_on_support R h2 v n m U hU V S f hImage):
  T=S->@CurrentPushforward.value R h2 v n m U V hU hV T f hImage hf hT=
    @CurrentPushforward.value R h2 v n m U V hU hV S f hImage hf hS.
Proof.
move=>hTS;subst S.
exact:(@current_pushforward_unique R h2 v n m U V hU hV T f hImage hf hT _ _
  (@CurrentPushforward.laws R h2 v n m U V hU hV T f hImage hf hT)
  (@CurrentPushforward.laws R h2 v n m U V hU hV T f hImage hf hS)).
Qed.
End CurrentPushforwardCongruence.
