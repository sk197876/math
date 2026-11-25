(** Supporting algebra for Federer (1969), 3.4.8(8),
    p. 329: pass from one actual prefix
    image to the next. Reuse subring lifts,
    scalar enlargement and finite-module transitivity. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets.
From Federer Require Import CommutativeSubringUP CommutativeSubringRealisationUP
  CommutativeSubringLiftExistence CommutativeRingImageQuotient
  RingScalarRestriction RingSubmoduleUP FiniteModuleScalarEnlargement FiniteRingModuleComposition.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [finite_ring_image_step]: the original
    finite simple extension over Q_j is finite
    over p(Q_j), and hence over the original
    initial coefficient ring, 3.4.8(8), p. 329.
    Every scalar map retains its exact inclusion
    triangle. No injectivity of Q_j into the
    original quotient is required. *)
Theorem finite_ring_image_step (K A C D0 D1:comNzRingType)
  (original:{rmorphism A->C}) (include0:{rmorphism D0->C}) (include1:{rmorphism D1->C})
  (S:set C) (scalar:{rmorphism A->D1}) (base:{rmorphism K->D0}):
  is_commutative_subring_realisation (fun y:C=>exists a:A,y = original a) include0 ->
  is_commutative_subring_realisation S include1 ->
  (forall a:A,include1 (scalar a) = original a) ->
  is_finitely_generated_ring_submodule
    (setT:set [the lmodType K of ring_restricted_space base D0^o]) ->
  is_finitely_generated_ring_submodule
    (setT:set [the lmodType A of ring_restricted_space scalar D1^o]) ->
  exists next:{rmorphism K->D1},
    (forall a:K,include1 (next a) = include0 (base a)) /\
    is_finitely_generated_ring_submodule
      (setT:set [the lmodType K of ring_restricted_space next D1^o]).
Proof.
move=>hImage0 hImage1 hTriangle hFinite0 hFinite1.
have hContained d:S (include0 d).
  have [a hA]:(exists a:A,include0 d = original a).
    apply:(commutative_subring_inclusion_image hImage0 _).2;by exists d.
  rewrite hA -hTriangle.
  apply:(commutative_subring_inclusion_image hImage1 _).2;by exists (scalar a).
have [lift hLift]:=@commutative_subring_ring_lift_exists D0 C D1 S include1 hImage1 include0 hContained.
have [rho [hRho hQuotient]]:=@commutative_ring_image_quotient A C D0 original include0 hImage0.
have hInjective:=commutative_subring_inclusion_injective hImage1.
have hFactor a:lift (rho a) = scalar a.
  apply:hInjective;by rewrite hLift hRho hTriangle.
have hFiniteStep:=@finite_module_scalar_enlargement A D0 D1 scalar rho lift hFactor hFinite1.
pose next:{rmorphism K->D1}:=GRing.RMorphism.clone K D1 (lift \o base) _.
exists next;split.
- move=>a;change (include1 (lift (base a)) = include0 (base a));exact:hLift.
- apply:(@finite_ring_module_composition K D0 D1 base lift next _ hFinite0 hFiniteStep).
  by move=>a.
Qed.
