(** Federer (1969), 4.1.13, pp. 369–370: replacing
    the original source by a smaller open neighbourhood
    preserves Df and hence the printed rho. Reuse the
    local differential laws of 3.1.1, pp. 209–210. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormDifferentialLocal
  NormRegularity InnerNorm HilbertFormCompactness GrassmannAbbreviations
  EuclideanInnerProduct CurrentMapDifferential.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [current_map_differential_open_restriction]:
    the actual derivative fields agree on the smaller open
    source, supporting the original rho-weighted integrals
    in Federer 4.1.13, pp. 369–370, by locality
    in 3.1.1, pp. 209–210. *)
Theorem current_map_differential_open_restriction (R:realType) n nu
    (U V:set (R_n R n))
    (hU:forall x,U x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) U x)
    (hUV:forall x,U x->V x) (f:R_n R n->R_n R nu):
  norm_class_all_orders (inner_norm_real_norm (@euclidean_inner_productP R n))
    (inner_norm_real_norm (@euclidean_inner_productP R nu)) V f->
  forall x,U x->@current_map_differential R n nu U f x=
    @current_map_differential R n nu V f x.
Proof.
move=>hf x hx;apply:current_map_differential_unique.
apply:(norm_differential_restrict hUV (hU x hx)).
exact:(@current_map_differential_actual R n nu V f hf x (hUV x hx)).
Qed.
