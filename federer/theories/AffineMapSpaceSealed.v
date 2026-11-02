(** The vector space A(V, W) of Federer (1969), 2.7.16, printed p. 133: "The
    class A(V, V') of all affine maps of V into V' is a vectorspace." The
    signature exposes only the space, its evaluation and the specification
    is_affine_map_space of AffineMapSpaceUP.v; the opaque ascription hides
    the subtype of AffineMapSpaceConstruction.v, so later results depend on
    the specification alone. The interface names are affine_maps V W,
    affine_map_eval and affine_mapsP; the theorem
    affine_maps_finite_dimensional is "If dim V < oo, then dim A(V, V) <
    oo", p. 134, for A(V, W) with finite dimensional V and W. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import LinearBasis AffineMapSpaceUP AffineMapSpaceConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

Module Type AffineMapSpaceSig.
  (** Source for [space]: the vector space A(V, W) of all affine maps
      of V into W, Federer 2.7.16, p. 133, exposed through its
      specification. *)
  Parameter space : forall (R : numFieldType) (V W : lmodType R), lmodType R.
  (** Source for [eval]: the evaluation of members of A(V, W) as maps of
      V into W, Federer 2.7.16, p. 133, exposed through its
      specification. *)
  Parameter eval : forall (R : numFieldType) (V W : lmodType R), space V W -> V -> W.
  (** Source for [laws]: A(V, W) is the class of all affine maps with
      the pointwise operations, Federer 2.7.16, p. 133. *)
  Parameter laws : forall (R : numFieldType) (V W : lmodType R), is_affine_map_space (@eval R V W).
End AffineMapSpaceSig.

Module AffineMapSpaceImpl : AffineMapSpaceSig.
(** Source for [space]: witness of A(V, W), the subtype of affine maps,
    Federer 2.7.16, p. 133. *)
Definition space (R : numFieldType) (V W : lmodType R) : lmodType R :=
  GRing.Lmodule.clone R (affine_function V W) _.
(** Source for [eval]: witness of the evaluation of A(V, W), Federer
    2.7.16, p. 133. *)
Definition eval (R : numFieldType) (V W : lmodType R) : space V W -> V -> W :=
  fun f : affine_function V W => affine_function_fun f.
(** Source for [laws]: the witness satisfies the specification of
    A(V, W), Federer 2.7.16, p. 133. No new global assumption is
    introduced. *)
Lemma laws (R : numFieldType) (V W : lmodType R) : is_affine_map_space (@eval R V W).
Proof. exact: affine_function_space. Qed.
End AffineMapSpaceImpl.

Section Interface.
Variable R : numFieldType.
Variables V W : lmodType R.

(** Source for [affine_maps]: "The class A(V, V') of all affine maps of
    V into V' is a vectorspace", Federer 2.7.16, p. 133. Interface name
    of the sealed space. *)
Definition affine_maps : lmodType R := AffineMapSpaceImpl.space V W.

(** Source for [affine_map_eval]: the value f(v) of a member f of
    A(V, W), Federer 2.7.16, p. 133. Interface name of the sealed
    evaluation. *)
Definition affine_map_eval : affine_maps -> V -> W := @AffineMapSpaceImpl.eval R V W.

(** Source for [affine_mapsP]: A(V, W) satisfies the specification of
    the class of all affine maps with the pointwise operations, Federer
    2.7.16, p. 133. Specification of the interface names. *)
Theorem affine_mapsP : is_affine_map_space affine_map_eval.
Proof. exact: AffineMapSpaceImpl.laws. Qed.

(** Source for [affine_maps_finite_dimensional]: "If dim V < oo, then
    dim A(V, V) < oo", Federer 2.7.16, p. 134, for A(V, W): if V and W
    have bases of n and k members, then A(V, W) has a base of n k + k
    members. Direct formalisation. *)
Theorem affine_maps_finite_dimensional n k (b : 'I_n -> V) (c : 'I_k -> W) :
  is_basis b -> is_basis c -> exists u : 'I_(n * k + k) -> affine_maps, is_basis u.
Proof. by move=> hb hc; exact: (@affine_space_finite_dimensional R V W _ _ affine_mapsP n k b hb c hc). Qed.

End Interface.

Arguments affine_maps {R} V W.
Arguments affine_map_eval {R V W}.
Arguments affine_mapsP {R V W}.
