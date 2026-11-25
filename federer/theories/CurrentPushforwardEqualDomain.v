(** Federer (1969), 4.1.18, p. 374: changing
    only the openness proofs of the same original
    source and target leaves a smooth pushforward
    unchanged. The proof uses old domain transport
    and public current congruence, with no new
    mathematical premise.  *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormRegularity InnerNorm
  HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct CurrentSpaces
  CurrentDomainTransport CurrentProperSupport CurrentPushforwardSealed CurrentPushforwardCongruence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [current_pushforward_equal_domain]: equality
    bookkeeping for the original h_z deformation
    and its endpoints, Federer 4.1.18, p. 374.
    Both properness witnesses are independently checked. *)
Theorem current_pushforward_equal_domain
    (R:realType) (h2:(1+1:R)!=0) n nu m
    (U:set (R_n R n)) (V:set (R_n R nu))
    (hU hU':forall x,U x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) U x)
    (hV hV':forall y,V y->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R nu)) V y)
    (f:R_n R n->R_n R nu)
    (hImage hImage':forall x,U x->V (f x))
    (hf hf':norm_class_all_orders
      (inner_norm_real_norm (@euclidean_inner_productP R n))
      (inner_norm_real_norm (@euclidean_inner_productP R nu)) U f)
    (T:@current_space R h2 n U hU m)
    (hProper:@is_current_proper_on_support R h2 n nu m U hU V T f hImage)
    (hProper':@is_current_proper_on_support R h2 n nu m U hU' V
      (@current_domain_transport R h2 n U hU U (erefl U) hU' m T) f hImage'):
  @current_domain_transport R h2 nu V hV' V (erefl V) hV m
    (@CurrentPushforward.value R h2 n nu m U V hU' hV'
      (@current_domain_transport R h2 n U hU U (erefl U) hU' m T)
      f hImage' hf' hProper')=
  @CurrentPushforward.value R h2 n nu m U V hU hV T f hImage hf hProper.
Proof.
have hSource:hU'=hU:=Prop_irrelevance _ _;subst hU'.
have hTarget:hV'=hV:=Prop_irrelevance _ _;subst hV'.
have hImages:hImage'=hImage:=Prop_irrelevance _ _;subst hImage'.
have hClasses:hf'=hf:=Prop_irrelevance _ _;subst hf'.
rewrite current_domain_transport_refl.
apply:(@current_pushforward_current_congruence R h2 n nu m U V hU hV
  f hImage hf _ T hProper' hProper).
exact:current_domain_transport_refl.
Qed.
