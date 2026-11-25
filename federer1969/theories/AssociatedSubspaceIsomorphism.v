(** Federer (1969), 3.2.48, p. 286: an orthogonal isotropy
    action carries the associated tangent plane to the associated plane
    of the transformed word. Supporting naturality from 1.3.1, p. 14,
    and the defining wedge equation of 1.6.1, p. 23. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import ModuleQuotient SubspaceCarrier TensorUP Bilinear AlgebraUP ExteriorAlgebra ExteriorGrading
  ExteriorMaps GradedComponents AssociatedSubspace.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [associated_subspace_isomorphism]: the exact transformed
    associated plane used for tau(y h inverse) in 3.2.48, p. 286.
    Exterior-algebra functoriality and actual inverse laws prove both
    inclusions, including the literal empty word in degree zero. *)
Theorem associated_subspace_isomorphism (K:fieldType) (V W:lmodType K)
    (f:{linear V->W}) (g:{linear W->V}) m (x:exterior_power V m):
  cancel f g ->cancel g f ->forall u,
  FedererSimple.T (exterior_power_map f m x) u <->FedererSimple.T x (g u).
Proof.
move=>hLeft hRight.
have hCancel a:exterior_algebra_map g (exterior_algebra_map f a)=a.
  rewrite exterior_algebra_map_comp.
  have hMap:linear_comp g f=1 linear_id V by move=>v; exact (hLeft v).
  rewrite (@exterior_algebra_map_eq K V V (linear_comp g f) (linear_id V) hMap a).
  exact (exterior_algebra_map_id a).
have hNatural v:FedererSimple.T (exterior_power_map f m x) (f v) <->FedererSimple.T x v.
  change (wedge (component_val (exterior_power_map f m x)) (exterior_generator (f v))=0 <->
    wedge (component_val x) (exterior_generator v)=0).
  have hWedge:wedge (component_val (exterior_power_map f m x)) (exterior_generator (f v))=
      exterior_algebra_map f (wedge (component_val x) (exterior_generator v)).
    rewrite algebra_map_mul exterior_algebra_mapE; reflexivity.
  rewrite hWedge; split.
  - move=>h; have h' :=congr1 (exterior_algebra_map g) h.
    by rewrite hCancel linear0 in h'.
  - by move=>h; rewrite h linear0.
move=>u; have h:=hNatural (g u); by rewrite hRight in h.
Qed.
