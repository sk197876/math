(** Federer (1969), 1.10.5, p. 47, positivity of the induced symmetric inner
    product in arbitrary dimension. Supporting finite-support reduction:
    each symmetric vector is carried by a finite-dimensional subspace. This
    reuses the project's general subspace and finite-basis results; no
    global basis of the ambient space is chosen. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import TensorUP AlgebraUP Graded GradedComponents
  SymmetricAlgebra SymmetricGrading SymmetricMaps SymmetricPowerFunctor
  ModuleQuotient SubspaceCarrier FiniteIndependence FiniteSpans FiniteSpanSpace.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
From Federer Require Import SymmetricFiniteSupport.
Section Reduction.
Variable K : fieldType.
Variable V : lmodType K.
Variable m : nat.
Variable xi : symmetric_power V m.
(** Source for [symmetric_finite_dimensional_reduction]: Federer 1.10.5, p. 47,
    supporting finite-dimensional reduction. In words: Choose a finite independent family whose span carries the symmetric vector and contains any prescribed finite list. *)
Theorem symmetric_finite_dimensional_reduction (s : seq V) :
  exists n (e : 'I_n -> V) (he : finite_independent e),
    (forall v, v \in s -> finite_span_subspace e v) /\
    exists eta : symmetric_power (finite_span_vect he) m,
      symmetric_power_map (subspace_inclusion (finite_span_subspace e)) m eta = xi.
Proof.
have [t ht] := symmetric_subspace_finite_support xi.
have [n [e [he hs]]] := finite_independent_span (t++s).
exists n, e, he; split.
- move=> v hv; apply: hs; by rewrite mem_cat hv orbT.
- apply: ht => v hv; apply: hs; by rewrite mem_cat hv.
Qed.
End Reduction.
(** Source for [symmetric_pair_finite_reduction]: Federer 1.10.5, p. 47,
    supporting finite-dimensional reduction. In words: Two symmetric vectors, possibly of different degrees, lift to one common finite-dimensional subspace. *)
Theorem symmetric_pair_finite_reduction (R : fieldType) (V : lmodType R)
    p q (x : symmetric_power V p) (y : symmetric_power V q) :
  exists n (e : 'I_n -> V) (he : finite_independent e)
    (a : symmetric_power (finite_span_vect he) p)
    (b : symmetric_power (finite_span_vect he) q),
    symmetric_power_map (subspace_inclusion (finite_span_subspace e)) p a = x /\
    symmetric_power_map (subspace_inclusion (finite_span_subspace e)) q b = y.
Proof.
have [s hs] := symmetric_subspace_finite_support y.
have [n [e [he [hS [a ha]]]]] := symmetric_finite_dimensional_reduction x s.
have [b hb] := hs (finite_span_subspace e) hS.
by exists n, e, he, a, b; split.
Qed.
