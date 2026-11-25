(** Federer (1969), 4.1.15, p. 373: the original
    flat image agrees with the preceding smooth image.
    Apply 4.1.14, pp. 370–371, at one compact index
    supplied by flat membership. Every support-properness
    witness gives the same original smooth image. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  NormRegularity NormClassOneUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct LipschitzUP
  CurrentSpaces CurrentProperSupport CurrentPushforwardSealed
  CurrentCompactMapProper CurrentCompactPushforwardAlgebra
  CurrentPushforwardDataIndependence FlatCurrentsUP
  CurrentLipschitzCompactImage CurrentCompactLipschitzPushforwardSmooth
  CurrentFlatLipschitzPushforwardSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [current_flat_lipschitz_pushforward_smooth]: use
    the actual smooth identity and constant maps in the
    point-support corollaries of Federer 4.1.15, p. 373.
    The compact index and its compactness proof are derived
    internally from the original flat membership. *)
Theorem current_flat_lipschitz_pushforward_smooth (R:realType)
    (h2:(1+1:R)!=0) n nu m
    (U:set (R_n R n)) (V:set (R_n R nu))
    (hU:forall x,U x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) U x)
    (hV:forall y,V y->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R nu)) V y)
    (f:R_n R n->R_n R nu)
    (hImage:forall x,U x->V (f x))
    (hLocal:@is_locally_metric_lipschitz R
      (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n)))
      (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R nu))) U f)
    (T:@current_space R h2 n U hU m)
    (hFlat:@is_flat_current R h2 n m U hU T)
    (hSmooth:norm_class_all_orders
      (inner_norm_real_norm (@euclidean_inner_productP R n))
      (inner_norm_real_norm (@euclidean_inner_productP R nu)) U f)
    (hProper:@is_current_proper_on_support R h2 n nu m U hU V T f hImage):
  @CurrentFlatLipschitzPushforward.value R h2 n nu m U V hU hV
    f hImage hLocal T hFlat=
  @CurrentPushforward.value R h2 n nu m U V hU hV
    T f hImage hSmooth hProper.
Proof.
have[K hK]:=hFlat.
rewrite (@CurrentFlatLipschitzPushforward.compact_value R h2 n nu m
  U V hU hV f hImage hLocal T hFlat K hK).
rewrite (@current_compact_lipschitz_pushforward_smooth R h2 n nu m
  U V hU hV f hImage hLocal K T hK hSmooth).
exact:(@current_pushforward_data_independent R h2 n nu m U V hU hV T f
  hImage hImage hSmooth hSmooth _ hProper).
Qed.

Arguments current_flat_lipschitz_pushforward_smooth : clear implicits.
