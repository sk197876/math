(** Supporting algebra for Federer (1969), 3.4.8(5), p. 328,
    using the original finite coefficient module of (8), p. 329.
    Pass a finite module to a quotient on which its scalars factor
    through the original residue field. Reuse the two existing
    finite-module transport theorems. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets.
From Federer Require Import RingScalarRestriction RingSubmoduleUP
  FiniteModuleSurjectiveImage FiniteModuleScalarEnlargement.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [finite_algebra_residue_field_module]: supporting
    finite residue-fibre connection for Federer 3.4.8(5), p. 328.
    A surjective original algebra image is finite over the residue
    field when its original scalar action factors through that field.
    No injectivity or vector-space basis is an extra premise. *)
Theorem finite_algebra_residue_field_module (A C Q:comNzRingType) (K:fieldType)
    (phi:{rmorphism A->C}) (rho:{rmorphism C->Q})
    (residue:{rmorphism A->K}) (scalar:{rmorphism K->Q}):
  (forall q:Q,exists c:C,rho c = q) ->
  (forall a:A,scalar (residue a) = rho (phi a)) ->
  is_finitely_generated_ring_submodule
    (setT:set [the lmodType A of ring_restricted_space phi C^o]) ->
  is_finitely_generated_ring_submodule
    (setT:set [the lmodType K of ring_restricted_space scalar Q^o]).
Proof.
move=>hOnto hTriangle hFinite.
pose sigma:=GRing.RMorphism.clone A Q (rho \o phi) _.
pose V:=[the lmodType A of ring_restricted_space phi C^o].
pose W:=[the lmodType A of ring_restricted_space sigma Q^o].
have hLinear:linear (rho:V->W).
  move=>a x y;change (rho (phi a*x+y) = rho (phi a)*rho x+rho y).
  by rewrite rmorphD rmorphM.
pose f:{linear V->W}:=HB.pack (rho:V->W) (GRing.isLinear.Build A V W *:%R rho hLinear).
have hFiniteImage:is_finitely_generated_ring_submodule (setT:set W):=
  @finite_module_surjective_linear_image A V W f hOnto hFinite.
exact:(@finite_module_scalar_enlargement A K Q sigma residue scalar hTriangle hFiniteImage).
Qed.
