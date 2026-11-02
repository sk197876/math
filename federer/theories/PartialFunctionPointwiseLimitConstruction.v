(** Existence construction for the partial pointwise limit in Federer
    (1969), 2.3.9, pp. 79–80. Metric limits are unique, so the convergence
    relation is a function graph. Source context and domain convention:
    PartialFunctionPointwiseLimitUP.v. *)
From mathcomp Require Import all_boot boolp classical_sets reals topology.
From Federer Require Import PartialFunctionUP PartialFunctionPointwiseLimitUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [partial_function_pointwise_limit_witness]: private
    graph construction proving existence of h in Federer 2.3.9,
    pp. 79–80, without an inhabitance premise on the target. *)
Definition partial_function_pointwise_limit_witness (R : realType) (X : Type)
    (Y : metricType R) (f : nat -> partial_function X Y) : partial_function X Y.
Proof.
refine (@Build_partial_function X Y (fun x y => exists u : nat -> Y,
  (forall n, partial_function_graph (f n) x (u n)) /\ u @ \oo --> y) _).
move=> x y z [u [hu hy]] [v [hv hz]].
have he : u=v by apply: functional_extensionality_dep=> n; exact: partial_function_single_valued (hu n) (hv n).
rewrite -he in hz.
have PF0 : ProperFilter (\oo : set_system nat) by typeclasses eauto.
have PF : ProperFilter (u @ \oo) := @fmap_proper_filter nat Y u \oo PF0.
exact (@cvg_unique Y (@metric_hausdorff R Y) (u @ \oo) PF y z hy hz).
Defined.

(** Source for [partial_function_pointwise_limit_exists]: proved
    existence of the abstract pointwise limit function supporting
    Federer 2.3.9, pp. 79–80. *)
Theorem partial_function_pointwise_limit_exists (R : realType) (X : Type)
    (Y : metricType R) (f : nat -> partial_function X Y) :
  exists h, is_partial_function_pointwise_limit f h.
Proof. exists (partial_function_pointwise_limit_witness f)=> x y; by []. Qed.
