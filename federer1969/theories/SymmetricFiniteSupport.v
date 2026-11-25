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
Section FiniteSupport.
Variable K : fieldType.
Variable V : lmodType K.
(** Source for [symmetric_finite_support]: Federer 1.10.5, p. 47,
    supporting finite-dimensional reduction. In words: Each symmetric-algebra element involves only finitely many generating vectors. A linear map fixing those vectors fixes the element. *)
Theorem symmetric_finite_support (x : symmetric_space V) :
  exists s : seq V, forall f : {linear V -> V},
    (forall v, v \in s -> f v = v) -> symmetric_algebra_map f x = x.
Proof.
elim/symmetric_word_induction: x => [|x y [s hs] [t ht]|c x [s hs]|s].
- exists [::] => f hf; exact: linear0.
- exists (s++t) => f hf; rewrite linearD.
  have hx : symmetric_algebra_map f x = x.
    apply: hs => v hv; apply: hf; by rewrite mem_cat hv.
  have hy : symmetric_algebra_map f y = y.
    apply: ht => v hv; apply: hf; by rewrite mem_cat hv orbT.
  by rewrite hx hy.
- exists s => f hf; by rewrite linearZ (hs f hf).
- exists s => f hf; rewrite symmetric_algebra_map_word.
  have hm : [seq f v | v <- s] = s.
    elim: s hf => [|v s ih] hf //=; rewrite (hf v (mem_head v s)).
    congr (_ :: _); apply: ih => w hw; apply: hf; by rewrite in_cons hw orbT.
  by rewrite hm.
Qed.
End FiniteSupport.
Section Inclusion.
Variable K : fieldType.
Variable V : lmodType K.
Variable S : subspace V.
Local Notation U := (GRing.Lmodule.clone K (subspace_space S) _).
Local Notation iota := (subspace_inclusion S).
Local Notation r := (subspace_retraction S).
(** Source for [symmetric_subspace_injective]: Federer 1.10.5, p. 47,
    supporting finite-dimensional reduction. In words: Subspace inclusion induces an injective symmetric-algebra map, since a linear retraction gives a left inverse. *)
Theorem symmetric_subspace_injective : injective (symmetric_algebra_map iota).
Proof. exact (can_inj (@symmetric_algebra_mapK K U V iota r (@subspace_retractionK K V S))). Qed.
(** Source for [symmetric_power_subspace_injective]: Federer 1.10.5, p. 47,
    supporting finite-dimensional reduction. In words: The induced map on each symmetric power is injective. *)
Theorem symmetric_power_subspace_injective m : injective (symmetric_power_map iota m).
Proof. exact (can_inj (@symmetric_power_mapK K U V iota r (@subspace_retractionK K V S) m)). Qed.
End Inclusion.
Section Support.
Variable K : fieldType.
Variable V : lmodType K.
Variable m : nat.
Variable xi : symmetric_power V m.
(** Source for [symmetric_subspace_finite_support]: Federer 1.10.5, p. 47,
    supporting finite-dimensional reduction. In words: Every homogeneous symmetric vector lifts to each subspace containing a suitable finite list of its generating vectors. *)
Theorem symmetric_subspace_finite_support :
  exists s : seq V, forall S : subspace V,
    (forall v, v \in s -> S v) ->
    exists eta : symmetric_power (GRing.Lmodule.clone K (subspace_space S) _) m,
      symmetric_power_map (subspace_inclusion S) m eta = xi.
Proof.
have [s hs] := symmetric_finite_support (component_val xi).
exists s => S hS.
pose f := linear_comp (subspace_inclusion S) (subspace_retraction S).
have hf v : v \in s -> f v = v.
  move=> hv; exact: subspace_retraction_on (hS v hv).
have hx := hs f hf.
exists (symmetric_power_map (subspace_retraction S) m xi).
apply: val_inj; change
  (symmetric_algebra_map (subspace_inclusion S)
    (symmetric_algebra_map (subspace_retraction S) (component_val xi)) = component_val xi).
by rewrite symmetric_algebra_map_comp.
Qed.
End Support.
