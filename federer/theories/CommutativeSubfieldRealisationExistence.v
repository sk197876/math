(** Federer (1969), 3.4.8(8), p. 329:
    realise the original subfield with an exact
    field inclusion. Reuse the already sealed
    subring carrier, fraction field and extension
    of its embedding. The existing inclusion laws
    also specify this field carrier independently. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets.
From Federer Require Import CommutativeDomainUP CommutativeIdealUP CommutativeFieldKernel
  CommutativeSubringUP CommutativeSubringRealisationUP CommutativeSubringRealisationSealed
  CommutativeSubfieldUP FractionFieldUP FractionFieldSealed FractionFieldExtensionUP
  FractionFieldExtensionSealed FractionFieldExtensionLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [commutative_subfield_realisation_exists]:
    the original subfield M in 3.4.8(8), p. 329,
    has a field carrier and precisely the original
    inclusion image. Constructions remain local witnesses
    governed by the existing independent inclusion laws. *)
Theorem commutative_subfield_realisation_exists (L:fieldType) (S:set L):
  is_commutative_subfield S ->exists (K:fieldType) (include:{rmorphism K->L}),
    is_commutative_subring_realisation S include.
Proof.
move=>hS.
pose A:=@CommutativeSubringRealisation.space L S (commutative_subfield_ring hS).
pose inclusion:=@CommutativeSubringRealisation.inclusion L S (commutative_subfield_ring hS).
have hA:=@CommutativeSubringRealisation.laws L S (commutative_subfield_ring hS).
have hInjective:=commutative_subring_inclusion_injective hA.
have hDomain:is_commutative_integral_domain A.
  move=>x y hZero.
  have hProduct:inclusion (x*y) = 0 by rewrite hZero rmorph0.
  have [hX|hY]:=(commutative_field_kernel_prime inclusion).2.2 x y hProduct.
  - left;apply:hInjective;by rewrite hX rmorph0.
  - right;apply:hInjective;by rewrite hY rmorph0.
pose K:=@FractionField.space A hDomain.
pose embed:=@FractionField.embed A hDomain.
have hFraction:=@FractionField.laws A hDomain.
pose include:=@FractionFieldExtension.map A K L embed hFraction inclusion hInjective.
have hExtension:=@FractionFieldExtension.laws A K L embed hFraction inclusion hInjective.
have hMember a:S (inclusion a).
  apply:(commutative_subring_inclusion_image hA (inclusion a)).2;by exists a.
exists K,include;constructor.
- exact:fmorph_inj.
- move=>x;split.
  + move/(commutative_subring_inclusion_image hA x).1=>[a hX].
    exists (embed a);by rewrite hExtension.
  + move=>[y <-].
    have [a [b [hB hY]]]:=fraction_field_fraction_representation hFraction y.
    rewrite hY fmorph_div !hExtension.
    apply:(@commutative_subring_multiply L S (commutative_subfield_ring hS));first exact:hMember.
    exact:(@commutative_subfield_inverse L S hS (inclusion b) (hMember b)).
Qed.
