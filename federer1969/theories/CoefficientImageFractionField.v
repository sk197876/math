(** Federer (1969), 3.4.8(8), p. 330:
    clear original coefficient denominators even
    when the original coefficient map has
    a kernel. Pass through its faithful
    image and reuse the existing finite
    denominator theorem from 3.4.7. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets.
From Federer Require Import CommutativeDomainUP CommutativeSubringUP CommutativeSubringRealisationUP
  CommutativeSubringRealisationSealed CommutativeFieldKernel CommutativeRingImageQuotient
  FractionFieldUP FiniteFractionDenominators CoefficientFractionFieldUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [subring_realisation_field_domain]: the
    faithful coefficient-image carrier has no
    zero divisors, supporting denominator clearing
    in 3.4.8(8), p. 330. Apply the
    existing prime-kernel theorem and the
    specified injectivity of the inclusion. *)
Lemma subring_realisation_field_domain (D:comNzRingType) (M:fieldType)
  (S:set M) (inclusion:{rmorphism D->M}):
  is_commutative_subring_realisation S inclusion ->is_commutative_integral_domain D.
Proof.
move=>hImage a b hZero.
have hInjective:=commutative_subring_inclusion_injective hImage.
have hProduct:inclusion (a*b) = 0 by rewrite hZero rmorph0.
have [hA|hB]:=(commutative_field_kernel_prime inclusion).2.2 a b hProduct.
- left;apply:hInjective;by rewrite hA rmorph0.
- right;apply:hInjective;by rewrite hB rmorph0.
Qed.

(** Source for [coefficient_image_fraction_field]: M
    is the actual fraction field of
    the faithful original coefficient image,
    as used in 3.4.8(8), p. 330.
    The independent coefficient-field laws prove
    its exact fraction representation. *)
Theorem coefficient_image_fraction_field (A D:comNzRingType) (L M:fieldType)
  (original:{rmorphism A->L}) (eta:{rmorphism A->M}) (phi:{rmorphism M->L})
  (inclusion:{rmorphism D->M}):
  is_coefficient_fraction_field original eta phi ->
  is_commutative_subring_realisation (fun y:M=>exists a:A,y = eta a) inclusion ->
  is_commutative_fraction_field inclusion.
Proof.
move=>hCoefficient hImage.
have [rho [hRho _]]:=@commutative_ring_image_quotient A M D eta inclusion hImage.
constructor;first exact:commutative_subring_inclusion_injective hImage.
move=>x;have [a [b [hB hValue]]]:=coefficient_fraction_representation hCoefficient x.
exists (rho a),(rho b);split.
- move=>hZero;apply:hB.
  rewrite -(coefficient_fraction_scalar_triangle hCoefficient b) -hRho hZero !rmorph0;by [].
- apply:(fmorph_inj phi).
  by rewrite fmorph_div !hRho !(coefficient_fraction_scalar_triangle hCoefficient) hValue.
Qed.

(** Source for [coefficient_original_common_denominators]:
    a finite family in the original M
    has one denominator from the original
    coefficient ring whose image is nonzero,
    3.4.8(8), p. 330. Apply the existing
    finite-fraction theorem on the faithful image,
    then lift its coefficients back. *)
Theorem coefficient_original_common_denominators (A:comNzRingType) (L M:fieldType)
  (original:{rmorphism A->L}) (eta:{rmorphism A->M}) (phi:{rmorphism M->L}):
  is_coefficient_fraction_field original eta phi ->forall N (f:nat->M),
  exists delta:A,eta delta<>0 /\forall i,(i<N)%N ->exists a:A,eta delta*f i = eta a.
Proof.
move=>hCoefficient N f.
pose S:set M:=fun y=>exists a:A,y = eta a.
have hS:is_commutative_subring S:=commutative_ring_image_subring eta.
pose D:=@CommutativeSubringRealisation.space M S hS.
pose inclusion:=@CommutativeSubringRealisation.inclusion M S hS.
have hImage:=@CommutativeSubringRealisation.laws M S hS.
have hField:=@coefficient_image_fraction_field A D L M original eta phi inclusion hCoefficient hImage.
have hDomain:=@subring_realisation_field_domain D M S inclusion hImage.
have [d [hD hValues]]:=@finite_fraction_denominators D M inclusion hField hDomain N f.
have hMember:S (inclusion d).
  apply:(commutative_subring_inclusion_image hImage _).2;by exists d.
have [delta hDelta]:=hMember.
exists delta;split.
- move=>hZero;apply:hD;apply:(fraction_field_embedding_injective hField).
  by rewrite hDelta hZero rmorph0.
- move=>i hI;have [a hA]:=hValues i hI.
  have hMemberA:S (inclusion a).
    apply:(commutative_subring_inclusion_image hImage _).2;by exists a.
  have [a0 hA0]:=hMemberA;exists a0;by rewrite -hDelta hA hA0.
Qed.
