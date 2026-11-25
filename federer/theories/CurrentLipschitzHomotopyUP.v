(** Federer (1969), 4.1.14, p. 371: the
    homotopy formula of 4.1.9, p. 363,
    extends to locally Lipschitz homotopies proper
    on [0,1] times spt T. Retain the
    original open A times U domain. The
    support-cylinder properness is specified separately. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  LipschitzUP CurrentHomotopyUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [is_locally_lipschitz_current_homotopy]:
    the original homotopy geometry on open A
    times U, with the local Lipschitz regularity
    stated in Federer 4.1.14, p. 371.
    No global Lipschitz constant, smoothness or
    whole-domain properness is built into this definition. *)
Definition is_locally_lipschitz_current_homotopy
    (R:realType) n nu (A:set R)
    (U:set (R_n R n)) (V:set (R_n R nu))
    (f g:R_n R n->R_n R nu)
    (h:R_n R (1+n)%N->R_n R nu):Prop:=
  @is_current_homotopy_geometry R n nu A U V f g h /\
  @is_locally_metric_lipschitz R
    (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R (1+n)%N)))
    (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R nu)))
    (@current_homotopy_product_domain R n A U) h.
