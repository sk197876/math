(** Opaque extension witness for Federer (1969), 2.10.43, printed p. 201.
    Only a total extension map and its proved agreement and global-bound
    laws are exposed. The maximal graph, scalar normalisation and zero-bound
    implementation remain hidden. Source context: KirszbraunExtensionUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals classical_sets.
From Federer Require Import EuclideanInnerProduct InnerMetric LipschitzUP
  KirszbraunExtensionUP KirszbraunExtensionConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Module Type KIRSZBRAUN_EXTENSION.
(** Source for [value]: abstract chosen extension
    in 2.10.43, p. 201, at a supplied
    nonnegative bound. Existence has been proved. *)
Parameter value : forall (R : realType) m n
  (S : set (inner_metric_space (@euclidean_inner_productP R m)))
  (f : inner_metric_space (@euclidean_inner_productP R m) ->
    inner_metric_space (@euclidean_inner_productP R n)) (L : R),
  is_metric_lipschitz_bound S f L ->
  inner_metric_space (@euclidean_inner_productP R m) ->
    inner_metric_space (@euclidean_inner_productP R n).
(** Source for [laws]: abstract agreement and global
    Lipschitz-bound laws of the extension in 2.10.43,
    p. 201. No witness implementation is exposed. *)
Parameter laws : forall (R : realType) m n
  (S : set (inner_metric_space (@euclidean_inner_productP R m)))
  (f : inner_metric_space (@euclidean_inner_productP R m) ->
    inner_metric_space (@euclidean_inner_productP R n)) (L : R)
  (hSf : is_metric_lipschitz_bound S f L),
  is_kirszbraun_extension S f (@value R m n S f L hSf) L.
End KIRSZBRAUN_EXTENSION.

Module KirszbraunExtension : KIRSZBRAUN_EXTENSION.
(** Source for [value]: privately proved extension
    witness for 2.10.43, p. 201, hidden
    by opaque module ascription. *)
Definition value (R : realType) m n
  (S : set (inner_metric_space (@euclidean_inner_productP R m)))
  (f : inner_metric_space (@euclidean_inner_productP R m) ->
    inner_metric_space (@euclidean_inner_productP R n)) (L : R)
  (hSf : is_metric_lipschitz_bound S f L) :=
  projT1 (cid (@kirszbraun_extension_exists R m n S f L hSf)).
(** Source for [laws]: proved agreement and bound
    for the opaque witness of 2.10.43, p. 201. *)
Lemma laws (R : realType) m n
  (S : set (inner_metric_space (@euclidean_inner_productP R m)))
  (f : inner_metric_space (@euclidean_inner_productP R m) ->
    inner_metric_space (@euclidean_inner_productP R n)) (L : R)
  (hSf : is_metric_lipschitz_bound S f L) :
  is_kirszbraun_extension S f (@value R m n S f L hSf) L.
Proof. exact: (projT2 (cid (@kirszbraun_extension_exists R m n S f L hSf))). Qed.
End KirszbraunExtension.
