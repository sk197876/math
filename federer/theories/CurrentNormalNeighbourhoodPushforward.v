(** Federer (1969), 4.1.13, pp. 369–370: a normal
    current has the same smooth image after restriction
    to an open neighbourhood of its support. Compactness
    supplies every required support-properness witness. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormRegularity
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  CurrentSpaces CurrentProperSupport CurrentCompactMapProper CurrentPushforwardSealed
  CurrentCompactPushforwardAlgebra CurrentOpenRestriction CurrentOpenRestrictionNormal
  NormalCurrentsUP CurrentOpenIdentitySmooth CurrentPushforwardNeighbourhoodParameters.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [current_normal_neighbourhood_pushforward]: the
    endpoint image of the original normal current is preserved
    by the source-neighbourhood replacement in Federer 4.1.13,
    pp. 369–370. The smaller map may carry any evidence
    of its original smoothness and support properness. *)
Theorem current_normal_neighbourhood_pushforward (R:realType) (h2:(1+1:R)!=0)
    n nu m (W U:set (R_n R n)) (V:set (R_n R nu))
    (hW:forall x,W x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) W x)
    (hU:forall x,U x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) U x)
    (hV:forall y,V y->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R nu)) V y)
    (hWU:forall x,W x->U x) (f:R_n R n->R_n R nu)
    (hImage:forall x,U x->V (f x))
    (hf:norm_class_all_orders (inner_norm_real_norm (@euclidean_inner_productP R n))
      (inner_norm_real_norm (@euclidean_inner_productP R nu)) U f)
    (hImageSmall:forall x,W x->V (f x))
    (hfSmall:norm_class_all_orders (inner_norm_real_norm (@euclidean_inner_productP R n))
      (inner_norm_real_norm (@euclidean_inner_productP R nu)) W f)
    (T:@current_space R h2 n U hU m)
    (hNormal:@is_normal_current R h2 n U hU m T)
    (hSupport:@current_support R h2 n U hU m T `<=` W)
    (hpSmall:@is_current_proper_on_support R h2 n nu m W hW V
      (@current_open_restriction R h2 n m W U hW hU hWU T) f hImageSmall):
  @current_compact_map_pushforward R h2 n nu U V hU hV f hImage hf m T hNormal.2=
    @CurrentPushforward.value R h2 n nu m W V hW hV
      (@current_open_restriction R h2 n m W U hW hU hWU T)
      f hImageSmall hfSmall hpSmall.
Proof.
pose S:=@current_open_restriction R h2 n m W U hW hU hWU T.
have hNS:=@current_normal_neighbourhood_restriction R h2 n W U hW hU hWU
  m T hNormal hSupport.
pose hId:=@current_open_identity_smooth R n W hW.
pose hpI:=@current_compact_map_proper R h2 n n m W U hW S (fun x=>x) hWU
  (norm_class_continuous (hId 0%N)) hNS.2.
pose hpOriginal:=@current_compact_map_proper R h2 n nu m U V hU T f hImage
  (norm_class_continuous (hf 0%N)) hNormal.2.
exact:(@current_pushforward_neighbourhood_parameters R h2 n nu m W U V
  hW hU hV hWU hId f hImage hf hImageSmall hfSmall T hSupport hpI hpSmall hpOriginal).
Qed.
