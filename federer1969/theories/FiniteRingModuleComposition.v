(** Federer (1969), 3.4.8(8), p. 329:
    compose the original scalar homomorphisms
    in the finite analytic quotient tower.
    Reuse finite-module transitivity and the
    actual linear-image connection. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets.
From Federer Require Import RingScalarRestriction RingSubmoduleUP RingFiniteModuleTower
  FiniteModuleSurjectiveImage.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [finite_ring_module_composition]:
    the original composed scalar action gives
    a finite module, 3.4.8(8), p. 329.
    The identity linear map identifies the
    two independently specified restricted actions. *)
Theorem finite_ring_module_composition (A B C:comNzRingType)
  (phi:{rmorphism A->B}) (tau:{rmorphism B->C}) (sigma:{rmorphism A->C}):
  (forall a:A,tau (phi a) = sigma a) ->
  is_finitely_generated_ring_submodule
    (setT:set [the lmodType A of ring_restricted_space phi B^o]) ->
  is_finitely_generated_ring_submodule
    (setT:set [the lmodType B of ring_restricted_space tau C^o]) ->
  is_finitely_generated_ring_submodule
    (setT:set [the lmodType A of ring_restricted_space sigma C^o]).
Proof.
move=>hTriangle hAB hBC.
pose V:=[the lmodType B of ring_restricted_space tau C^o].
pose W:=[the lmodType A of ring_restricted_space phi V].
pose Z:=[the lmodType A of ring_restricted_space sigma C^o].
have hFinite:=@finite_ring_module_tower A B phi V hAB hBC.
have hLinear:linear (fun x:W=>(x:Z)).
  by move=>a x y;change (tau (phi a)*x+y = sigma a*x+y);rewrite hTriangle.
pose f:{linear W->Z}:=HB.pack (fun x:W=>(x:Z))
  (GRing.isLinear.Build _ _ _ _ _ hLinear).
apply:(@finite_module_surjective_linear_image A W Z f _ hFinite)=>z.
by exists z.
Qed.
