(** Opaque witness of the agreeing annular extension of Federer (1969),
    3.1.16, p. 228. Only agreement and bounded-ball Lipschitz laws are exposed. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import EuclideanInnerProduct InnerMetric LipschitzUP
  OpenAnnuliClosedUnion AnnularLipschitzExtensionUP AnnularLipschitzExtensionConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Module Type ANNULAR_LIPSCHITZ_EXTENSION.
(** Source for [value]: abstract intermediate map h in Federer
    3.1.16, p. 228, whose existence is proved by successive extensions. *)
Parameter value : forall (R : realType) (m n : nat)
  (C : nat->set (inner_metric_space (@euclidean_inner_productP R m)))
  (f : inner_metric_space (@euclidean_inner_productP R m)->
    inner_metric_space (@euclidean_inner_productP R n))
  (hC : forall i, compact (C i))
  (hCU : forall i, C i `<=` open_annulus (0 : inner_metric_space (@euclidean_inner_productP R m)) i)
  (hCf : forall i, is_metric_lipschitz (C i) f),
  inner_metric_space (@euclidean_inner_productP R m)->
    inner_metric_space (@euclidean_inner_productP R n).
(** Source for [laws]: abstract agreement and local Lipschitz bounds
    of h in Federer 3.1.16, p. 228. *)
Parameter laws : forall (R : realType) (m n : nat)
  (C : nat->set (inner_metric_space (@euclidean_inner_productP R m)))
  (f : inner_metric_space (@euclidean_inner_productP R m)->
    inner_metric_space (@euclidean_inner_productP R n))
  (hC : forall i, compact (C i))
  (hCU : forall i, C i `<=` open_annulus (0 : inner_metric_space (@euclidean_inner_productP R m)) i)
  (hCf : forall i, is_metric_lipschitz (C i) f),
  is_annular_lipschitz_extension C f (@value R m n C f hC hCU hCf).
End ANNULAR_LIPSCHITZ_EXTENSION.

Module AnnularLipschitzExtension : ANNULAR_LIPSCHITZ_EXTENSION.
(** Source for [value]: privately proved intermediate map h in
    Federer 3.1.16, p. 228, hidden by opaque module ascription. *)
Definition value (R : realType) (m n : nat)
  (C : nat->set (inner_metric_space (@euclidean_inner_productP R m)))
  (f : inner_metric_space (@euclidean_inner_productP R m)->
    inner_metric_space (@euclidean_inner_productP R n))
  (hC : forall i, compact (C i))
  (hCU : forall i, C i `<=` open_annulus (0 : inner_metric_space (@euclidean_inner_productP R m)) i)
  (hCf : forall i, is_metric_lipschitz (C i) f) :=
  projT1 (cid (@annular_lipschitz_extension_exists R m n C f hC hCU hCf)).
(** Source for [laws]: the proved specification of the opaque
    intermediate map in Federer 3.1.16, p. 228. *)
Lemma laws (R : realType) (m n : nat)
  (C : nat->set (inner_metric_space (@euclidean_inner_productP R m)))
  (f : inner_metric_space (@euclidean_inner_productP R m)->
    inner_metric_space (@euclidean_inner_productP R n))
  (hC : forall i, compact (C i))
  (hCU : forall i, C i `<=` open_annulus (0 : inner_metric_space (@euclidean_inner_productP R m)) i)
  (hCf : forall i, is_metric_lipschitz (C i) f) :
  is_annular_lipschitz_extension C f (@value R m n C f hC hCU hCf).
Proof. exact: (projT2 (cid (@annular_lipschitz_extension_exists R m n C f hC hCU hCf))). Qed.
End AnnularLipschitzExtension.
