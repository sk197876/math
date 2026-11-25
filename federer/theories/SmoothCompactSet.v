(** Federer (1969), 4.1.1, pp. 343–344: compact subsets K
    of the actual open domain U index the derivative seminorms
    and the fixed-support subspaces. Compactness uses the existing
    norm topology on the source; no compact exhaustion is assumed. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [smooth_compact_set]: the index K in nu^i_K
    and D_K(U,Y), Federer 4.1.1, pp. 343–344. The underlying
    subset, inclusion in U and compactness are independent data. *)
Record smooth_compact_set (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) (U:set X) := {
  (** Source for [smooth_compact_carrier]: the actual subset
      K of the source, Federer 4.1.1, p. 343. *)
  smooth_compact_carrier : set X;
  (** Source for [smooth_compact_in_domain]: K is contained
      in the open domain U, Federer 4.1.1, p. 343. *)
  smooth_compact_in_domain : smooth_compact_carrier `<=` U;
  (** Source for [smooth_compact_is_compact]: K is compact
      for the original norm topology, Federer 4.1.1, p. 343. *)
  smooth_compact_is_compact : compact [set x:real_norm_metric_space hNX|
    smooth_compact_carrier x]
}.

Arguments smooth_compact_carrier {R X NX hNX U} s _.
Arguments smooth_compact_in_domain {R X NX hNX U} s _ _.
Arguments smooth_compact_is_compact {R X NX hNX U} s.

(** Source for [smooth_compact_empty]: the empty compact set
    is an allowed index, including empty U, Federer 4.1.1, p. 343. *)
Definition smooth_compact_empty (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) (U:set X) : smooth_compact_set hNX U.
Proof.
refine (@Build_smooth_compact_set R X NX hNX U set0 _ _).
- by move=>x hx.
- exact:compact0.
Defined.

(** Source for [smooth_compact_union]: union of two compact
    indices gives a common compact index, supporting the directed
    seminorm neighbourhood base in Federer 4.1.1, p. 344. *)
Definition smooth_compact_union (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) (U:set X)
    (K L:smooth_compact_set hNX U) : smooth_compact_set hNX U.
Proof.
refine (@Build_smooth_compact_set R X NX hNX U
  (smooth_compact_carrier K `|` smooth_compact_carrier L) _ _).
- rewrite subUset; split; [exact:(@smooth_compact_in_domain R X NX hNX U K)|exact:(@smooth_compact_in_domain R X NX hNX U L)].
- change (compact ([set x:real_norm_metric_space hNX|smooth_compact_carrier K x] `|`
    [set x:real_norm_metric_space hNX|smooth_compact_carrier L x])).
  exact:(@compactU (real_norm_metric_space hNX) _ _
    (@smooth_compact_is_compact R X NX hNX U K)
    (@smooth_compact_is_compact R X NX hNX U L)).
Defined.

(** Source for [smooth_compact_singleton]: every domain point
    gives an order-zero evaluation seminorm, supporting the
    Hausdorff assertion in Federer 4.1.1, p. 344. *)
Definition smooth_compact_singleton (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) (U:set X) (a:X) (ha:U a) :
    smooth_compact_set hNX U.
Proof.
refine (@Build_smooth_compact_set R X NX hNX U [set a] _ _).
- by move=>x ->.
- exact:(@compact_set1 (real_norm_metric_space hNX) a).
Defined.
