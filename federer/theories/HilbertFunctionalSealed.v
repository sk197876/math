(** Federer (1969), 1.7.13, p. 37: the vector representing a continuous
    linear functional, exposed only through its inner-product equation. The
    kernel-projection existence witness is private. Source context:
    HilbertSpaceUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp.
From mathcomp Require Import classical_sets topology num_normedtype normed_module.
From Federer Require Import InnerProductUP InnerMetric InnerNormedTopology
  HilbertSpaceUP HilbertFunctionalUP HilbertFunctionalConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import numFieldTopology.Exports numFieldNormedType.Exports.
Local Open Scope ring_scope.
Module Type HilbertFunctionalSig.
(** Source for [vector]: Federer 1.7.13, p. 37,
    the specified vector representing a continuous linear functional. *)
Parameter vector : forall (R : realType) (V : lmodType R)
  (B : V -> V -> R) (hB : is_inner_product B), is_hilbert_space hB ->
  forall f : {linear V -> R^o},
  continuous (fun x : inner_metric_space hB => (f x : R^o)) -> V.
(** Source for [laws]: Federer 1.7.13, p. 37,
    the representing vector satisfies f(v)=u.v for every v. *)
Parameter laws : forall (R : realType) (V : lmodType R)
  (B : V -> V -> R) (hB : is_inner_product B) (hH : is_hilbert_space hB)
  (f : {linear V -> R^o})
  (hf : continuous (fun x : inner_metric_space hB => (f x : R^o))),
  is_hilbert_functional_vector B f (@vector R V B hB hH f hf).
End HilbertFunctionalSig.
Module HilbertFunctional : HilbertFunctionalSig.
(** Source for [vector]: Federer 1.7.13, p. 37,
    select the proved representing vector inside the opaque module. *)
Definition vector (R : realType) (V : lmodType R)
  (B : V -> V -> R) (hB : is_inner_product B) (hH : is_hilbert_space hB)
  (f : {linear V -> R^o})
  (hf : continuous (fun x : inner_metric_space hB => (f x : R^o))) : V :=
  sval (constructive_indefinite_description
    (@hilbert_functional_vector_exists R V B hB hH f hf)).
(** Source for [laws]: Federer 1.7.13, p. 37,
    the selected representative satisfies the exported equation. *)
Lemma laws (R : realType) (V : lmodType R)
  (B : V -> V -> R) (hB : is_inner_product B) (hH : is_hilbert_space hB)
  (f : {linear V -> R^o})
  (hf : continuous (fun x : inner_metric_space hB => (f x : R^o))) :
  is_hilbert_functional_vector B f (@vector R V B hB hH f hf).
Proof. exact: (svalP (constructive_indefinite_description
    (@hilbert_functional_vector_exists R V B hB hH f hf))). Qed.
End HilbertFunctional.
