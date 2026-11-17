(** Supporting algebra for Federer (1969), 3.4.8(8),
    pp. 329–330: original algebra generators
    generate the fraction field as a ring
    over the original coefficient field. Apply
    finite-extension inverse closure and the exact
    original fraction representation. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets.
From Federer Require Import RingScalarRestriction RingSubmoduleUP CommutativeSubringUP CommutativeSubfieldUP
  FractionFieldUP CoefficientFractionFieldUP FiniteFieldIntermediateSubfield.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [fraction_field_original_coordinate_generators]:
    the original L is generated as a ring
    by M and the original coordinate classes,
    as used in 3.4.8(8), pp. 329–330.
    This is proved from the original finite
    module and ring-generation data, not supplied
    as a geometric theorem hypothesis. *)
Theorem fraction_field_original_coordinate_generators (A C:comNzRingType) (M L:fieldType)
  (scalar:{rmorphism A->C}) (include:{rmorphism C->L})
  (eta:{rmorphism A->M}) (phi:{rmorphism M->L}) n (x:'I_n->C):
  is_commutative_fraction_field include ->
  (forall a:A,phi (eta a) = include (scalar a)) ->
  is_finitely_generated_ring_submodule
    (setT:set [the lmodType M of ring_restricted_space phi L^o]) ->
  is_generated_commutative_subring
    (fun y:C=>(exists i:'I_n,y = x i) \/exists a:A,y = scalar a) setT ->
  is_generated_commutative_subring
    (fun y:L=>(exists i:'I_n,y = include (x i)) \/exists a:M,y = phi a) setT.
Proof.
move=>hFraction hTriangle hFinite hOriginal;constructor.
- by constructor.
- by move=>y _.
- move=>S hS hGenerators.
  have hScalars a:S (phi a) by apply:hGenerators;right;by exists a.
  have hField:=@finite_field_intermediate_ring_subfield M L phi S hFinite hS hScalars.
  have hPreimage:is_commutative_subring (fun y:C=>S (include y)).
    constructor.
    * rewrite rmorph0;exact:commutative_subring_zero hS.
    * rewrite rmorph1;exact:commutative_subring_one hS.
    * move=>a b hA hB;rewrite rmorphD;exact:(@commutative_subring_add L S hS _ _ hA hB).
    * move=>a hA;rewrite rmorphN;exact:(@commutative_subring_opp L S hS _ hA).
    * move=>a b hA hB;rewrite rmorphM;exact:(@commutative_subring_multiply L S hS _ _ hA hB).
  have hOriginalGenerators:(fun y:C=>(exists i:'I_n,y = x i) \/exists a:A,y = scalar a) `<=`
      (fun y:C=>S (include y)).
    move=>y [[i ->]|[a ->]].
    * apply:hGenerators;left;by exists i.
    * rewrite -hTriangle;exact:hScalars (eta a).
  have hAlgebra:=generated_commutative_subring_minimal hOriginal hPreimage hOriginalGenerators.
  move=>y _;have [a [b [hB hY]]]:=fraction_field_fraction_representation hFraction y.
  rewrite hY;apply:(@commutative_subring_multiply L S hS);first exact:hAlgebra a I.
  exact:(@commutative_subfield_inverse L S hField (include b) (hAlgebra b I)).
Qed.
