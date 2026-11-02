(** Federer (1969), 1.7.3, p. 29: existence of principal axes by successive
    maximisation on constrained unit spheres. This existence construction is
    imported only by the sealing module and assumption audit. *)
From mathcomp Require Import all_boot all_order all_algebra.
From mathcomp Require Import boolp classical_sets reals topology.
From Federer Require Import InnerProductUP InnerMetric OrthonormalFamilies
  OrthonormalisationUP GramSchmidt PrincipalAxesUP MaximalOrthonormalUP
  MaximalOrthonormalExtension MaximalPrincipalAxes ConstrainedUnitSphere
  ConstrainedSphereNonempty QuadraticContinuity CompactMaximum
  LinearBasis TensorUP InfiniteSequence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory.
Local Open Scope ring_scope.
Section Construction.
Variable R : realType.
Variable V : lmodType R.
Variable B S : V -> V -> R.
Hypothesis hB : is_inner_product B.
Hypothesis hS : @bilinear R V V R^o S.
Variable n : nat.
Variable b : 'I_n -> V.
Hypothesis hb : is_basis b.

(** Source for [maximal_orthonormal_witness]: Federer 1.7.3,
    p. 29, the inductive choice of maximising orthonormal axes up
    to any length not exceeding the dimension, including zero. *)
Theorem maximal_orthonormal_witness k : (k <= n)%N ->
  exists e : 'I_k -> V, is_maximal_orthonormal_family S hB e.
Proof.
have [b0 [hb0 hgs]] := @orthonormal_basis_exists R V B hB n b hb.
have hQ : continuous (fun x : inner_metric_space hB => (S x x : R^o)).
  exact (@quadratic_continuous R V B S hB hS n b0 hb0
    (orthonormalisation_orthonormal hgs)).
elim: k => [|k IH] hk.
- exists (fun _ : 'I_0 => (0 : V)); constructor.
  + move=> i; by have := ltn_ord i; rewrite ltn0.
  + move=> i; by have := ltn_ord i; rewrite ltn0.
- have [e he] := IH (leq_trans (leqnSn k) hk).
  have hne := @constrained_unit_sphere_nonempty R V B hB n b hb k e
    (maximal_family_orthonormal he) hk.
  have hc := @constrained_unit_sphere_compact R V B hB k e n b hb.
  have [v [hv hmax]] := @continuous_compact_maximum R
    (Topological.clone (inner_metric_space hB) _)
    (@constrained_unit_sphere R V B hB k e)
    (fun x => (S x x : R^o)) hne hc hQ.
  exists (ordinal_snoc e v).
  apply: (@maximal_orthonormal_snoc R V B S hB k e he v hv.1 hv.2).
  move=> x hx ho; exact: hmax x (conj hx ho).
Qed.

(** Source for [principal_axes_witness]: Federer 1.7.3,
    p. 29, the principal-axis theorem in the book's full ordered
    form, proved from successive maximisers and the algebraic
    stationary identity. *)
Theorem principal_axes_witness : (forall x y, S x y = S y x) ->
  exists e : 'I_n -> V, is_principal_axes B S e.
Proof.
move=> hs; have [e he] := maximal_orthonormal_witness (leqnn n).
exists e; exact: (@maximal_family_principal_axes R V B S hB hS hs n e he b hb).
Qed.
End Construction.
