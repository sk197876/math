(** Federer (1969), 3.4.12, p. 339, extending the functional
    submanifold definition of 3.4.5, p. 321: assemble the original
    finite scalar equations into their original complex coordinate map.
    Apply bounded complex linear inclusions, composition and finite sums. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets functions reals.
From Federer Require Import FieldPrefixSuffixSeparation FieldCoordinateFunctional NormDifferentialUP NormOpenDomainLaws HolomorphicRestriction Hom RealNormUP ScalarRestriction ComplexScalarSealed ComplexNormUP ComplexModulus
  ComplexScalarNorm FiniteCoordinates HolomorphicCoordinateNorm HolomorphicUP HolomorphicLinear
  HolomorphicFiniteCalculus HolomorphicOpenDomain.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Assembly.
Variable R:realType.
Local Notation C:=(ComplexScalars.C R).
Variable q:nat.
Local Notation Y:=(coordinate_space C q).
Local Notation YR:=(restricted_space (ComplexScalars.embed R) Y).
Local Notation CR:=(restricted_space (ComplexScalars.embed R) C^o).
Local Notation NY:=(@holomorphic_coordinate_norm R q).
Local Notation hNY:=(@holomorphic_coordinate_norm_laws R q).
(** Source for [complex_coordinate_inclusion]: the original coordinate
    line into the original finite complex target, supporting
    3.4.12, p. 339. Its values are prescribed by the basis. *)
Definition complex_coordinate_inclusion (i:'I_q):Hom C^o Y.
Proof.
apply:(@HomMap C C^o Y (fun z=>z*:@coordinate_basis C q i)).
apply/asboolP=>a z w.
by rewrite scalerDl scalerA.
Defined.
(** Source for [complex_coordinate_inclusion_bounded]: the original
    complex norm law gives the finite inclusion bound,
    3.4.12, p. 339. *)
Lemma complex_coordinate_inclusion_bounded i:
  @norm_bounded_linear R CR YR (@complex_modulus R) NY (complex_hom_real (complex_coordinate_inclusion i)).
Proof.
exists (NY (@coordinate_basis C q i));split.
- exact:(real_seminorm_nonnegative (complex_norm_real hNY).1).
- move=>z;change (is_true (NY (z*:@coordinate_basis C q i)<=NY (@coordinate_basis C q i)*complex_modulus z)).
  by rewrite (complex_norm_scale hNY) mulrC.
Qed.
(** Source for [holomorphic_scalar_assembly]: the original vector
    of holomorphic scalar functions is holomorphic, including an
    empty equation family, 3.4.12, p. 339. *)
Theorem holomorphic_scalar_assembly (X:lmodType C) (NX:X->R)
    (hNX:@is_real_norm R (restricted_space (ComplexScalars.embed R) X) NX)
    (A:set X) (f:'I_q->X->C):
  (forall x,A x ->@norm_domain_interior R (restricted_space (ComplexScalars.embed R) X) NX A x) ->
  (forall i,@is_holomorphic R X C^o NX (@complex_modulus R) hNX (@complex_modulus_real_norm R) A (f i)) ->
  @is_holomorphic R X Y NX NY hNX (complex_norm_real hNY) A (fun x=>[ffun i=>f i x]).
Proof.
move=>hOpen hF.
have hInclusion i:@is_holomorphic R C^o Y (@complex_modulus R) NY (@complex_modulus_real_norm R)
    (complex_norm_real hNY) setT (complex_coordinate_inclusion i).
  exact:(@holomorphic_bounded_linear R C^o Y (@complex_modulus R) NY (@complex_modulus_real_norm R)
    (complex_norm_real hNY) setT (complex_coordinate_inclusion i)
    (fun z _=>@norm_full_domain_interior R CR (@complex_modulus R) z)
    (complex_coordinate_inclusion_bounded i)).
have hTerms i:=@holomorphic_compose_on R X C^o Y NX (@complex_modulus R) NY hNX
  (@complex_modulus_real_norm R) (complex_norm_real hNY) A setT (f i) (complex_coordinate_inclusion i)
  (fun _ _=>Logic.I) (hF i) (hInclusion i).
have hSum:=@holomorphic_finite_sum R X Y NX NY hNX (complex_norm_real hNY) A [the finType of 'I_q]
  (fun i x=>complex_coordinate_inclusion i (f i x)) hOpen hTerms.
apply:(@holomorphic_domain_agreement R X Y NX NY hNX (complex_norm_real hNY) A
  (fun x=>\sum_i complex_coordinate_inclusion i (f i x)) (fun x=>[ffun i=>f i x]) _ hSum)=>x _.
change ((\sum_(i<q) f i x*:@coordinate_basis C q i)=[ffun i=>f i x]).
have hDual i j:@field_coordinate_functional C q i (@coordinate_basis C q j)=
    if i==j then 1 else 0.
  by rewrite /field_coordinate_functional /= /coordinate_basis ffunE eq_sym.
have hExpansion:=@field_original_given_basis_expansion C Y q (@coordinate_basis C q)
  (@coordinate_basisP C q) (fun i=>@field_coordinate_functional C q i) hDual [ffun i=>f i x].
symmetry;transitivity (\sum_(i<q)
    (@field_coordinate_functional C q i [ffun j=>f j x])*:@coordinate_basis C q i).
- exact:hExpansion.
- apply:eq_bigr=>i _;by rewrite /field_coordinate_functional /= ffunE.
Qed.
End Assembly.
