(** Federer (1969), 4.1.22, p. 379: existence of the
    independently specified real span. Intersecting all original
    subspaces that contain the generators supplies a witness;
    subsequent consumers use only the abstract span laws. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets.
From Federer Require Import ModuleQuotient GeneratedLinearSubspaceUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [generated_linear_subspace_exists]: the
    algebraic span of the integral subgroup exists,
    supporting Federer 4.1.22, p. 379. Empty generators
    are allowed, and no norm or closure is introduced. *)
Theorem generated_linear_subspace_exists (K:fieldType) (V:lmodType K)
    (D:set V):exists S:subspace V,is_generated_linear_subspace D S.
Proof.
pose P:set V:=[set x|forall W:subspace V,D `<=` W->W x].
have hZero:P 0 by move=>W hD;exact:subspace_zero.
have hAdd:forall x y,P x->P y->P (x+y).
  move=>x y hx hy W hD;exact:subspace_add (hx W hD) (hy W hD).
have hScale:forall a x,P x->P (a*:x).
  move=>a x hx W hD;exact:(@subspace_scale K V W a x (hx W hD)).
exists (@Subspace K V P hZero hAdd hScale);constructor.
- move=>x hx W hD;exact:hD x hx.
- move=>W hD x hx;exact:hx W hD.
Qed.
