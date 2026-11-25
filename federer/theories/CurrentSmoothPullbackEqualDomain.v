(** Federer (1969), 4.1.18, p. 375: original
    smooth pullbacks respect exact equality of
    source and target domain presentations. Only
    equality and proof irrelevance are used;
    no differential or image hypothesis is added. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormRegularity InnerNorm
  HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  CurrentSpaces CurrentEqualDomainSmooth SmoothFormPullbackSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [current_smooth_pullback_equal_domain]:
    equal original domains yield the same
    actual pullback form, supporting the averaged
    form homotopy in 4.1.18, p. 375. *)
Theorem current_smooth_pullback_equal_domain
    (R:realType) (h2:(1+1:R)!= 0) n nu m
    (U U':set (R_n R n)) (V V':set (R_n R nu))
    (hU:forall x,U x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) U x)
    (hU':forall x,U' x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) U' x)
    (hV:forall x,V x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R nu)) V x)
    (hV':forall x,V' x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R nu)) V' x)
    (eU:U= U') (eV:V= V') (f:R_n R n->R_n R nu)
    (hImage:forall x,U x->V (f x)) (hImage':forall x,U' x->V' (f x))
    (hf:norm_class_all_orders
      (inner_norm_real_norm (@euclidean_inner_productP R n))
      (inner_norm_real_norm (@euclidean_inner_productP R nu)) U f)
    (hf':norm_class_all_orders
      (inner_norm_real_norm (@euclidean_inner_productP R n))
      (inner_norm_real_norm (@euclidean_inner_productP R nu)) U' f)
    (omega:@current_smooth_space R h2 nu V hV m):
  @current_smooth_equal_domain R h2 n m U U' hU hU' eU
    (@SmoothFormPullback.operator R h2 n nu m U V hU hV f hImage hf omega)=
  @SmoothFormPullback.operator R h2 n nu m U' V' hU' hV' f hImage' hf'
    (@current_smooth_equal_domain R h2 nu m V V' hV hV' eV omega).
Proof.
destruct eU;destruct eV.
have hSource:hU'= hU:=Prop_irrelevance _ _;subst hU'.
have hTarget:hV'= hV:=Prop_irrelevance _ _;subst hV'.
have hImages:hImage'= hImage:=Prop_irrelevance _ _;subst hImage'.
have hClasses:hf'= hf:=Prop_irrelevance _ _;subst hf'.
rewrite /current_smooth_equal_domain.
rewrite ?(Prop_irrelevance (Prop_irrelevance hU hU) (erefl hU))
  ?(Prop_irrelevance (Prop_irrelevance hV hV) (erefl hV)).
reflexivity.
Qed.

(** Source for [current_smooth_pullback_equal_domain_reverse]:
    the same original equality law when the input
    form starts on the final target presentation,
    supporting 4.1.18, p. 375. *)
Theorem current_smooth_pullback_equal_domain_reverse
    (R:realType) (h2:(1+1:R)!= 0) n nu m
    (U U':set (R_n R n)) (V V':set (R_n R nu))
    (hU:forall x,U x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) U x)
    (hU':forall x,U' x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) U' x)
    (hV:forall x,V x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R nu)) V x)
    (hV':forall x,V' x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R nu)) V' x)
    (eU:U= U') (eV:V= V') (f:R_n R n->R_n R nu)
    (hImage:forall x,U x->V (f x)) (hImage':forall x,U' x->V' (f x))
    (hf:norm_class_all_orders
      (inner_norm_real_norm (@euclidean_inner_productP R n))
      (inner_norm_real_norm (@euclidean_inner_productP R nu)) U f)
    (hf':norm_class_all_orders
      (inner_norm_real_norm (@euclidean_inner_productP R n))
      (inner_norm_real_norm (@euclidean_inner_productP R nu)) U' f)
    (omega:@current_smooth_space R h2 nu V' hV' m):
  @current_smooth_equal_domain R h2 n m U U' hU hU' eU
    (@SmoothFormPullback.operator R h2 n nu m U V hU hV f hImage hf
      (@current_smooth_equal_domain R h2 nu m V' V hV' hV (esym eV) omega))=
  @SmoothFormPullback.operator R h2 n nu m U' V' hU' hV' f hImage' hf' omega.
Proof.
destruct eU;destruct eV.
have hSource:hU'= hU:=Prop_irrelevance _ _;subst hU'.
have hTarget:hV'= hV:=Prop_irrelevance _ _;subst hV'.
have hImages:hImage'= hImage:=Prop_irrelevance _ _;subst hImage'.
have hClasses:hf'= hf:=Prop_irrelevance _ _;subst hf'.
rewrite (Prop_irrelevance (esym (erefl V)) (erefl V)).
rewrite /current_smooth_equal_domain.
rewrite ?(Prop_irrelevance (Prop_irrelevance hU hU) (erefl hU))
  ?(Prop_irrelevance (Prop_irrelevance hV hV) (erefl hV)).
reflexivity.
Qed.
