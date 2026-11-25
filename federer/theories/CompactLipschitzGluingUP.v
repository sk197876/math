(** Federer (1969), 4.1.24, p. 380: the
    additive-group assertion for image approximants combines
    two source pieces placed in disjoint compact parts
    of one Euclidean space. These independent gluing
    laws retain open source pieces, original map values
    and a global Lipschitz bound on their union. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  SmoothCompactSet LipschitzUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [is_compact_lipschitz_gluing]: independent
    source-gluing laws for the original defining witnesses
    in the additive assertion of 4.1.24, p. 380.
    The glued source is an open union. No value
    is prescribed outside it and no compact is
    assumed nonempty. *)
Record is_compact_lipschitz_gluing (R:realType) d n
    (O0 O1:set (R_n R d)) (U:set (R_n R n))
    (K0:smooth_compact_set (inner_norm_real_norm (@euclidean_inner_productP R d)) O0)
    (K1:smooth_compact_set (inner_norm_real_norm (@euclidean_inner_productP R d)) O1)
    (f0 f1:R_n R d->R_n R n)
    (W0 W1:set (R_n R d)) (F:R_n R d->R_n R n):Prop:={
  (** Source: the common source is open, 4.1.24, p. 380. *)
  compact_lipschitz_gluing_open0:@open
    (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R d))) W0;
  (** Source: the second original open source piece, p. 380. *)
  compact_lipschitz_gluing_open1:@open
    (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R d))) W1;
  (** Source: preserve every point of the first compact, p. 380. *)
  compact_lipschitz_gluing_contains0:smooth_compact_carrier K0 `<=` W0;
  (** Source: preserve every point of the second compact, p. 380. *)
  compact_lipschitz_gluing_contains1:smooth_compact_carrier K1 `<=` W1;
  (** Source: the first original map remains defined, p. 380. *)
  compact_lipschitz_gluing_inside0:W0 `<=` O0;
  (** Source: the second original map remains defined, p. 380. *)
  compact_lipschitz_gluing_inside1:W1 `<=` O1;
  (** Source: exact first map values, p. 380. *)
  compact_lipschitz_gluing_values0:forall x,W0 x->F x=f0 x;
  (** Source: exact second map values, p. 380. *)
  compact_lipschitz_gluing_values1:forall x,W1 x->F x=f1 x;
  (** Source: the new defining map is globally Lipschitz on
      its original open source, not merely locally so, p. 380. *)
  compact_lipschitz_gluing_bound:@is_metric_lipschitz R
    (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R d)))
    (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n)))
    (W0 `|` W1) F;
  (** Source: the actual target remains the original U, p. 380. *)
  compact_lipschitz_gluing_image:forall x,(W0 `|` W1) x->U (F x)
}.
