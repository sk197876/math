(** Federer (1969), 3.4.8(8), p. 329:
    realise the coefficient-image subring, then
    apply the existing fraction field and its
    extension to the ambient field. The
    construction proves the independent laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets.
From Federer Require Import CommutativeDomainUP CommutativeSubringUP CommutativeSubringRealisationUP
  CommutativeRingImageQuotient
  CommutativeSubringRealisationSealed CommutativeSubringLiftExistence CommutativeFieldKernel
  FractionFieldUP FractionFieldSealed FractionFieldExtensionUP FractionFieldExtensionSealed
  CoefficientFractionFieldUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [coefficient_fraction_field_exists]: the
    actual coefficient subfield M in 3.4.8(8),
    p. 329. Reuse the image-subring carrier,
    fraction-field existence and extension theorem;
    all selected objects remain local witnesses. *)
Theorem coefficient_fraction_field_exists (A:comNzRingType) (L:fieldType) (original:{rmorphism A->L}):
  exists (M:fieldType) (scalar:{rmorphism A->M}) (inclusion:{rmorphism M->L}),
    is_coefficient_fraction_field original scalar inclusion.
Proof.
pose S:set L:=fun y=>exists a:A,y = original a.
have hS:is_commutative_subring S:=commutative_ring_image_subring original.
pose D:=@CommutativeSubringRealisation.space L S hS.
pose include:=@CommutativeSubringRealisation.inclusion L S hS.
have hD:=@CommutativeSubringRealisation.laws L S hS.
have hInjective:=commutative_subring_inclusion_injective hD.
have hDomain:is_commutative_integral_domain D.
  move=>a b hZero.
  have hProduct:include (a*b) = 0 by rewrite hZero rmorph0.
  have [hA|hB]:=(commutative_field_kernel_prime include).2.2 a b hProduct.
  - left;apply:hInjective;by rewrite hA rmorph0.
  - right;apply:hInjective;by rewrite hB rmorph0.
pose M:=@FractionField.space D hDomain.
pose embed:=@FractionField.embed D hDomain.
have hFraction:=@FractionField.laws D hDomain.
pose inclusion:=@FractionFieldExtension.map D M L embed hFraction include hInjective.
have hExtension:=@FractionFieldExtension.laws D M L embed hFraction include hInjective.
have hOriginal a:S (original a) by exists a.
have [lift hLift]:=@commutative_subring_ring_lift_exists A L D S include hD original hOriginal.
pose scalar:{rmorphism A->M}:=GRing.RMorphism.clone A M (embed \o lift) _.
exists M,scalar,inclusion;constructor.
- move=>a;change (inclusion (embed (lift a)) = original a);by rewrite hExtension hLift.
- move=>x;have [a [b [hB hX]]]:=fraction_field_fraction_representation hFraction x.
  have hAIn:S (include a).
    apply:(commutative_subring_inclusion_image hD (include a)).2;by exists a.
  have hBIn:S (include b).
    apply:(commutative_subring_inclusion_image hD (include b)).2;by exists b.
  have [a0 hA0]:=hAIn;have [b0 hB0]:=hBIn.
  exists a0,b0;split.
  + move=>hZero.
    have hImageZero:include b = include 0 by rewrite hB0 hZero rmorph0.
    exact:hB (@hInjective b 0 hImageZero).
  + by rewrite hX fmorph_div !hExtension hA0 hB0.
Qed.
