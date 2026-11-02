(** Federer (1969), 1.7.13, p. 37: public interface for the unique
    inner-product representative of a continuous linear functional. It uses
    only the sealed representation equation. Source context:
    HilbertSpaceUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From mathcomp Require Import classical_sets topology num_normedtype normed_module.
From Federer Require Import InnerProductUP InnerMetric InnerNormedTopology
  HilbertSpaceUP HilbertFunctionalUP HilbertFunctionalSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import numFieldTopology.Exports numFieldNormedType.Exports.
Local Open Scope ring_scope.
Section Functional.
Variable R : realType.
Variable V : lmodType R.
Variable B : V -> V -> R.
Hypothesis hB : is_inner_product B.
Hypothesis hH : is_hilbert_space hB.
Variable f : {linear V -> R^o}.
Hypothesis hf : continuous (fun x : inner_metric_space hB => (f x : R^o)).

(** Source for [hilbert_functional_vector]: Federer 1.7.13,
    p. 37, the unique representing vector supplied by its sealed laws. *)
Definition hilbert_functional_vector := @HilbertFunctional.vector R V B hB hH f hf.

(** Source for [hilbert_functional_vectorP]: Federer 1.7.13,
    p. 37, the equation f(v)=u.v for the specified representative. *)
Theorem hilbert_functional_vectorP :
  is_hilbert_functional_vector B f hilbert_functional_vector.
Proof. exact: HilbertFunctional.laws. Qed.

(** Source for [hilbert_functional_unique]: Federer 1.7.13,
    p. 37, every vector satisfying the representation equation
    equals the specified vector. *)
Theorem hilbert_functional_unique u :
  is_hilbert_functional_vector B f u -> u=hilbert_functional_vector.
Proof.
move=> hu.
exact (@hilbert_functional_vector_unique R V B hB f u hilbert_functional_vector
  hu hilbert_functional_vectorP).
Qed.
End Functional.
