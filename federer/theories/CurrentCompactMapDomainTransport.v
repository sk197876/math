(** Federer (1969), 4.1.11, p. 366: identify
    equal presentations of the original source and
    target domains of a compact pushforward. This is
    equality bookkeeping for the Cartesian affine prism
    transfer, with every proof parameter retained. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormRegularity
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct CurrentSpaces
  CurrentDomainTransport CurrentCompactPushforwardAlgebra.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [current_compact_map_domain_transport]:
    equal original source and target domains preserve
    the actual compact-current image, supporting the
    prism transfer in Federer 4.1.11, p. 366.
    Only domain equalities are eliminated; smoothness
    and compactness requirements are unchanged. *)
Theorem current_compact_map_domain_transport (R:realType) (h2:(1+1:R)!=0) m n
    (U U':set (R_n R m)) (V V':set (R_n R n))
    (hU:forall x,U x->norm_domain_interior (inner_norm (@euclidean_inner_productP R m)) U x)
    (hU':forall x,U' x->norm_domain_interior (inner_norm (@euclidean_inner_productP R m)) U' x)
    (hV:forall y,V y->norm_domain_interior (inner_norm (@euclidean_inner_productP R n)) V y)
    (hV':forall y,V' y->norm_domain_interior (inner_norm (@euclidean_inner_productP R n)) V' y)
    (eU:U=U') (eV:V=V') (f:R_n R m->R_n R n)
    (hImage:forall x,U x->V (f x)) (hImage':forall x,U' x->V' (f x))
    (hf:norm_class_all_orders (inner_norm_real_norm (@euclidean_inner_productP R m))
      (inner_norm_real_norm (@euclidean_inner_productP R n)) U f)
    (hf':norm_class_all_orders (inner_norm_real_norm (@euclidean_inner_productP R m))
      (inner_norm_real_norm (@euclidean_inner_productP R n)) U' f)
    k (T:@current_space R h2 m U hU k)
    (hT:@compact (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R m)))
      (@current_support R h2 m U hU k T))
    (hT':@compact (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R m)))
      (@current_support R h2 m U' hU' k (@current_domain_transport R h2 m U hU U' eU hU' k T))):
  @current_compact_map_pushforward R h2 m n U' V' hU' hV' f hImage' hf' k
    (@current_domain_transport R h2 m U hU U' eU hU' k T) hT'=
  @current_domain_transport R h2 n V hV V' eV hV' k
    (@current_compact_map_pushforward R h2 m n U V hU hV f hImage hf k T hT).
Proof.
subst U';subst V'.
have hSource:hU'=hU:=Prop_irrelevance _ _;subst hU'.
have hTarget:hV'=hV:=Prop_irrelevance _ _;subst hV'.
have hImages:hImage'=hImage:=Prop_irrelevance _ _;subst hImage'.
have hClasses:hf'=hf:=Prop_irrelevance _ _;subst hf'.
rewrite [RHS]current_domain_transport_refl.
apply:(@current_compact_map_pushforward_congruence R h2 m n U V hU hV f hImage hf k
  _ T hT' hT).
exact:current_domain_transport_refl.
Qed.
