(** Federer (1969), 3.2.33, p. 270: a nonempty
    relatively open manifold piece has positive intrinsic
    Hausdorff measure. Actual coordinate maps prove this. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  HilbertFormCompactness InnerNormTopologyAdapters NormCoordinateSystemUP NormRegularity
  NormOpenPreimage EuclideanOpenPositiveMass EuclideanHausdorffLebesgue
  HausdorffMeasure ClassOneDomainNullImage.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.

(** Source for [coordinate_relative_open_nonnull]: the
    nonnull relatively open coordinate pieces needed for
    continuation of analytic rank bounds in Federer 3.2.33,
    p. 270. If such a piece were Hausdorff null,
    its class-one forward coordinate map would have null
    image. That image is an actual nonempty open parameter
    set, contradicting its positive Lebesgue measure.
    No global Lipschitz bound or positive dimension is assumed. *)
Theorem coordinate_relative_open_nonnull (R:realType) n m
    (W T:set (R_n R n)) (V:set (R_n R m))
    (phi:R_n R n->R_n R m) (psi:R_n R m->R_n R n)
    (O:set (inner_metric_space (@euclidean_inner_productP R n))) a:
  is_norm_coordinate_system (inner_norm_real_norm (@euclidean_inner_productP R n))
    (inner_norm_real_norm (@euclidean_inner_productP R m)) W T V phi psi 1%N ->
  open O ->W a ->T a ->O a ->
  @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m
    ((W `&` T) `&` O)<>0%E.
Proof.
move=>hc hO ha ht hoa hNull.
pose NX:=inner_norm (@euclidean_inner_productP R n).
pose NZ:=inner_norm (@euclidean_inner_productP R m).
pose hNX:=inner_norm_real_norm (@euclidean_inner_productP R n).
pose hNZ:=inner_norm_real_norm (@euclidean_inner_productP R m).
pose P:set (inner_metric_space (@euclidean_inner_productP R m)):=
  [set u|V u /\O (psi u)].
have hPopen:open P.
  apply:(inner_norm_openP (@euclidean_inner_productP R m) P).2.
  exact:(@norm_class_zero_open_preimage R (R_n R m) (R_n R n) NZ NX hNZ hNX
    V O psi (norm_class_continuous (norm_coordinate_class_backward hc))
    ((inner_norm_openP (@euclidean_inner_productP R n) O).1 hO)).
have hPoint:P (phi a).
  split; first exact:(@norm_coordinate_forward_range R (R_n R n) (R_n R m) NX NZ hNX hNZ W T V phi psi 1%N hc a ht).
  by rewrite (norm_coordinate_base_inverse hc ha ht).
have hImage:phi @` ((W `&` T) `&` O)= P.
  apply/seteqP; split=>u.
  - move=>[x [[hx hxt] hxo] <-]; split.
    + exact:(@norm_coordinate_forward_range R (R_n R n) (R_n R m) NX NZ hNX hNZ W T V phi psi 1%N hc x hxt).
    + by rewrite (norm_coordinate_base_inverse hc hx hxt).
  - move=>[hu ho]; exists (psi u).
    + split; last exact ho; exact:(@norm_coordinate_backward_membership R (R_n R n) (R_n R m) NX NZ hNX hNZ W T V phi psi 1%N hc u hu).
    + exact:(@norm_coordinate_cancel R (R_n R n) (R_n R m) NX NZ hNX hNZ W T V phi psi 1%N hc u hu).
have hNullImage:=@class_one_domain_hausdorff_null_image R n m m T
  ((W `&` T) `&` O) phi
  ((norm_class_firstP hNX hNZ T phi).1 (norm_coordinate_class_forward hc))
  (fun x hx=>hx.1.2) hNull.
rewrite hImage (euclidean_hausdorff_spherical_lebesgue P).1 in hNullImage.
have hPositive:=euclidean_open_positive_mass hPopen hPoint.
by rewrite hNullImage ltxx in hPositive.
Qed.
