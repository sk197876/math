(** Federer (1969), 2.7.16, printed p. 133: "The class A(V, V') of all
    affine maps of V into V' is a vectorspace." Existence of a space
    satisfying is_affine_map_space (AffineMapSpaceUP.v): the affine maps
    form a linear subspace of the space of all maps V -> W with the
    pointwise operations, by the closure of affine maps under addition and
    scalar multiplication (AffineMaps.v); the subspace is realised as a
    subtype, as Hom(V, W) is in Hom.v. This construction serves only as an
    existence witness; it may be imported only by AffineMapSpaceSealed.v and
    tests/Assumptions.v. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets functions.
From Federer Require Import AffineMaps AffineMapSpaceUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

Section Construction.
Variable R : numFieldType.
Variables V W : lmodType R.
Local Notation F := (GRing.Lmodule.clone R (V -> W) _).

(** Source for [affine_function_pred]: membership in the class A(V, W)
    of all affine maps, Federer 2.7.16, p. 133. Definition of the
    witness. *)
Definition affine_function_pred (f : V -> W) := `[< is_affine_map f >].

(** Source for [affine_function]: the members of A(V, W) as a subtype
    of V -> W, Federer 2.7.16, p. 133. Definition of the witness. *)
Record affine_function := AffineFunction {
  affine_function_fun : V -> W;
  affine_function_proof : affine_function_pred affine_function_fun
}.

(** Source for [affine_function_rect]: the recursor of the subtype of
    affine maps, Federer 2.7.16, p. 133. Definition of the witness. *)
Definition affine_function_rect (P : affine_function -> Type)
    (h : forall f hf, P (@AffineFunction f hf)) (z : affine_function) : P z :=
  match z as z' return P z' with @AffineFunction f hf => h f hf end.
HB.instance Definition _ := [isSub for affine_function_fun by affine_function_rect].
HB.instance Definition _ := [Choice of affine_function by <:].

(** Source for [affine_function_closed]: A(V, W) is a linear subspace of
    the space of all maps, "the class A(V, V') ... is a vectorspace",
    Federer 2.7.16, p. 133. Supporting lemma of the witness. *)
Lemma affine_function_closed : GRing.submod_closed (fun f : F => `[< is_affine_map f >]).
Proof.
split.
- by apply/asboolP; exact: affine_map_zero.
- move=> a f g /asboolP hf /asboolP hg; apply/asboolP.
  exact: (affine_map_add (affine_map_scale a hf) hg).
Qed.
HB.instance Definition _ := GRing.SubChoice_isSubLmodule.Build
  R F (fun f : F => `[< is_affine_map f >]) affine_function affine_function_closed.

(** Source for [affine_function_space]: the subtype of affine maps with
    the pointwise operations satisfies the specification of A(V, W),
    Federer 2.7.16, p. 133. Existence witness. *)
Theorem affine_function_space : is_affine_map_space (fun f : affine_function => affine_function_fun f).
Proof.
split.
- by [].
- exact: val_inj.
- by move=> f; apply/asboolP; exact: affine_function_proof.
- by move=> h hh; exists (@AffineFunction h (introT (asboolP _) hh)).
Qed.

End Construction.
