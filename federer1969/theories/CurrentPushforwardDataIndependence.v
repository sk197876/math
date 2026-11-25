(** Federer (1969), 4.1.13, pp. 369–370: the endpoint
    images are the same original currents when their image,
    smoothness or support-properness evidence is presented
    differently. This is proof bookkeeping for the existing
    independently specified pushforward of 4.1.7, p. 359. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import RealNormUP NormDifferentialUP NormRegularity InnerNorm
  HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  CurrentSpaces CurrentProperSupport CurrentPushforwardSealed CurrentPushforwardCongruence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [current_pushforward_data_independent]: the original
    pushforward is unaffected by evidence for its hypotheses,
    supporting the original endpoint identification after source
    restriction in Federer 4.1.13, pp. 369–370. *)
Theorem current_pushforward_data_independent (R:realType) (h2:(1+1:R)!=0)
    n nu m (U:set (R_n R n)) (V:set (R_n R nu))
    (hU:forall x,U x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) U x)
    (hV:forall y,V y->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R nu)) V y)
    (T:@current_space R h2 n U hU m) (f:R_n R n->R_n R nu)
    (hImage hImage':forall x,U x->V (f x))
    (hf hf':norm_class_all_orders
      (inner_norm_real_norm (@euclidean_inner_productP R n))
      (inner_norm_real_norm (@euclidean_inner_productP R nu)) U f)
    (hp:@is_current_proper_on_support R h2 n nu m U hU V T f hImage)
    (hp':@is_current_proper_on_support R h2 n nu m U hU V T f hImage'):
  @CurrentPushforward.value R h2 n nu m U V hU hV T f hImage hf hp=
    @CurrentPushforward.value R h2 n nu m U V hU hV T f hImage' hf' hp'.
Proof.
have hImages:hImage'=hImage:=Prop_irrelevance _ _;subst hImage'.
have hClasses:hf'=hf:=Prop_irrelevance _ _;subst hf'.
exact:(@current_pushforward_current_congruence R h2 n nu m U V hU hV
  f hImage hf T T hp hp' (erefl T)).
Qed.
