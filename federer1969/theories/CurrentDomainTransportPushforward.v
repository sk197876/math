(** Federer (1969), 4.1.11, p. 366: an equal
    target-domain presentation preserves the actual proper
    pushforward. This equality adapter permits the original
    prism formula on the whole Euclidean product. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormRegularity
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  CurrentSpaces CurrentDomainTransport CurrentCompactPushforwardAlgebra.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [current_domain_transport_compact_pushforward]:
    equal presentations of the original target domain give
    the same actual compact-current image, supporting the
    prism and triangle identities in Federer 4.1.11,
    p. 366. Every image and openness proof is retained. *)
Theorem current_domain_transport_compact_pushforward
    (R:realType) (h2:(1+1:R)!=0) m n
    (A:set (R_n R m)) (U V:set (R_n R n))
    (hA:forall x,A x->norm_domain_interior (inner_norm (@euclidean_inner_productP R m)) A x)
    (hU:forall y,U y->norm_domain_interior (inner_norm (@euclidean_inner_productP R n)) U y)
    (e:U=V)
    (hV:forall y,V y->norm_domain_interior (inner_norm (@euclidean_inner_productP R n)) V y)
    (f:R_n R m->R_n R n)
    (hImageU:forall x,A x->U (f x)) (hImageV:forall x,A x->V (f x))
    (hf:norm_class_all_orders
      (inner_norm_real_norm (@euclidean_inner_productP R m))
      (inner_norm_real_norm (@euclidean_inner_productP R n)) A f)
    k (T:@current_space R h2 m A hA k)
    (hT:@compact (real_norm_metric_space
      (inner_norm_real_norm (@euclidean_inner_productP R m)))
      (@current_support R h2 m A hA k T)):
  @current_domain_transport R h2 n U hU V e hV k
    (@current_compact_map_pushforward R h2 m n A U hA hU f hImageU hf k T hT)=
  @current_compact_map_pushforward R h2 m n A V hA hV f hImageV hf k T hT.
Proof.
subst V.
have hOpen:hV=hU:=Prop_irrelevance _ _;subst hV.
have hImage:hImageV=hImageU:=Prop_irrelevance _ _;subst hImageV.
exact:current_domain_transport_refl.
Qed.
