(** Federer (1969), 3.1.16, p. 228: abstract laws of the locally
    Lipschitz extension assembled by repeated use of 2.10.43. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
From Federer Require Import EuclideanInnerProduct InnerMetric LipschitzUP MetricClosedBalls.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(** Source for [is_annular_lipschitz_extension]: the intermediate map h
    in Federer 3.1.16, p. 228. Agreement on the chosen compact pieces
    and a Lipschitz restriction to each closed integer ball specify the
    needed extension laws. Existence is proved separately. *)
Record is_annular_lipschitz_extension (R : realType) m n
    (C : nat->set (inner_metric_space (@euclidean_inner_productP R m)))
    (f h : inner_metric_space (@euclidean_inner_productP R m)->
      inner_metric_space (@euclidean_inner_productP R n)) : Prop := {
  (** Source for [annular_extension_agreement]: h agrees with f on each
      selected compact C_i, Federer 3.1.16, p. 228. *)
  annular_extension_agreement : forall i x, C i x -> h x=f x;
  (** Source for [annular_extension_ball_lipschitz]: supporting form of
      local Lipschitz regularity of h, Federer 3.1.16, p. 228. The
      successive extensions give a finite bound on every bounded ball. *)
  annular_extension_ball_lipschitz : forall i : nat,
    is_metric_lipschitz (metric_closed_ball (0 : inner_metric_space (@euclidean_inner_productP R m)) (i%:R : R)) h
}.
