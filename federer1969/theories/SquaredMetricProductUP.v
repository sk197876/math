(** Federer (1969), 2.10.45, printed p. 202, opening hypothesis: the
    Cartesian product has squared distance equal to the sum of the two
    squared factor distances. Specify pairing, projections and this equality
    on an abstract carrier. Nonexpansion of projections and isometry of
    slices are consequences, not extra hypotheses. This general metric
    interface supports the printed Euclidean-times-arbitrary-metric case. *)
From mathcomp Require Import all_boot all_order all_algebra reals topology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [is_squared_metric_product]: direct
    Cartesian pairing and squared-distance hypothesis
    of 2.10.45, p. 202. Only the
    first factor is specialised to Euclidean space
    in the later measure theorem. *)
Record is_squared_metric_product (R : realType) (P X Y : metricType R)
    (pair : X -> Y -> P) (first : P -> X) (second : P -> Y) : Prop := {
  (** Source for [squared_product_first_pair_law]: supporting
      first-coordinate identity of the product in
      2.10.45, p. 202. *)
  squared_product_first_pair_law : forall x y, first (pair x y)=x;
  (** Source for [squared_product_second_pair_law]: supporting
      second-coordinate identity of the product in
      2.10.45, p. 202. *)
  squared_product_second_pair_law : forall x y, second (pair x y)=y;
  (** Source for [squared_product_recovery_law]: supporting
      recovery of a Cartesian product point from
      its coordinates in 2.10.45, p. 202. *)
  squared_product_recovery_law : forall p, pair (first p) (second p)=p;
  (** Source for [squared_product_distance_law]: direct
      opening squared-distance equality of 2.10.45,
      p. 202, for two paired points. *)
  squared_product_distance_law : forall x y u v,
    mdist (pair x y) (pair u v)^+2=mdist x u^+2+mdist y v^+2
}.
