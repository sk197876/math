(** Public extension interface for Federer (1969), 2.10.43, printed p. 201.
    All consequences use only the agreement and global-bound laws of the
    opaque witness. Source context: KirszbraunExtensionUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets.
From Federer Require Import EuclideanInnerProduct InnerMetric LipschitzUP
  KirszbraunExtensionUP KirszbraunExtensionSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_lipschitz_extension]: abstract
    chosen extension map in 2.10.43, p. 201,
    at any supplied nonnegative Lipschitz bound. *)
Definition euclidean_lipschitz_extension (R : realType) m n
    (S : set (inner_metric_space (@euclidean_inner_productP R m)))
    (f : inner_metric_space (@euclidean_inner_productP R m) ->
      inner_metric_space (@euclidean_inner_productP R n)) (L : R)
    (hSf : is_metric_lipschitz_bound S f L) :=
  @KirszbraunExtension.value R m n S f L hSf.

(** Source for [euclidean_lipschitz_extension_specification]: proved
    agreement on S and global bound L in
    2.10.43, p. 201. The statement reveals
    no maximal graph or scalar normalisation. *)
Theorem euclidean_lipschitz_extension_specification (R : realType) m n
    (S : set (inner_metric_space (@euclidean_inner_productP R m)))
    (f : inner_metric_space (@euclidean_inner_productP R m) ->
      inner_metric_space (@euclidean_inner_productP R n)) (L : R)
    (hSf : is_metric_lipschitz_bound S f L) :
  is_kirszbraun_extension S f (@euclidean_lipschitz_extension R m n S f L hSf) L.
Proof. exact: KirszbraunExtension.laws. Qed.
