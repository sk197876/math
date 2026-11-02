(** Federer (1969), 2.10.43, printed p. 201: specify an extension by
    agreement on the original source and the same global Lipschitz bound.
    The existence witness is proved separately and will be hidden by opaque
    module ascription. Equality of optimal Lipschitz constants is a later
    consequence of these laws, not an interface axiom. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets.
From Federer Require Import EuclideanInnerProduct InnerMetric LipschitzUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [is_kirszbraun_extension]: direct extension
    and bound requirements in 2.10.43, p. 201.
    The arbitrary original subset and bound L are
    explicit. Zero bounds and empty source sets are
    allowed; existence is proved independently. *)
Record is_kirszbraun_extension (R : realType) m n
    (S : set (inner_metric_space (@euclidean_inner_productP R m)))
    (f g : inner_metric_space (@euclidean_inner_productP R m) ->
      inner_metric_space (@euclidean_inner_productP R n)) (L : R) : Prop := {
  (** Source for [kirszbraun_extension_agreement_law]: direct
      g restricted to S equals f requirement in
      2.10.43, p. 201. *)
  kirszbraun_extension_agreement_law : forall x, S x -> g x=f x;
  (** Source for [kirszbraun_extension_bound_law]: supporting
      same-bound global Lipschitz assertion of 2.10.43,
      p. 201. The inequality includes nonnegativity of L. *)
  kirszbraun_extension_bound_law : is_metric_lipschitz_bound setT g L
}.
