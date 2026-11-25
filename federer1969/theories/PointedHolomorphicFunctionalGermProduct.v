(** Supporting Federer (1969), 3.4.12, p. 339, extending 3.4.8(5), p. 328:
    multiplication by an actual pointed coordinate
    shifts divided directional coefficients by one
    order. This is the original Leibniz formula
    of 3.1.11, p. 222, with the proved
    coefficient values of the actual linear factor. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import ScalarRestriction ComplexScalarSealed ComplexNormUP Hom RealNormUP HolomorphicGermUP HolomorphicGermRing HolomorphicGermRepresentatives
  HolomorphicGermDirectionalCoefficient HolomorphicGermDirectionalProduct PointedHolomorphicFunctionalGermCoefficient.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [pointed_holomorphic_functional_product_successor_coefficient]:
    the successor coefficient of xi(x-a) times an
    original germ is xi(v) times its previous
    coefficient. This expands the radial factorisation
    argument for 3.4.8(5), p. 328. *)
Lemma pointed_holomorphic_functional_product_successor_coefficient (R:realType) (X:lmodType (ComplexScalars.C R))
  (NX:X->R) (hNX:is_complex_norm NX) a (xi:Hom X (ComplexScalars.C R)^o)
  (f:@holomorphic_representative_type R X NX (complex_norm_real hNX) a)
  (alpha:[the comNzRingType of (@holomorphic_germ_ring R X NX (complex_norm_real hNX) a)]) m v:
  (forall x,holomorphic_representative_value f x = xi (x-a)) ->
  @holomorphic_germ_directional_coefficient R X NX hNX a m.+1 ((holomorphic_germ f:@holomorphic_germ_ring R X NX (complex_norm_real hNX) a)*alpha) v =
    xi v*@holomorphic_germ_directional_coefficient R X NX hNX a m alpha v.
Proof.
move=>hValues;rewrite holomorphic_germ_directional_coefficient_product.
have hM:(m<m.+2)%N:=ltnW (ltnSn m.+1).
pose i:'I_m.+2:=Ordinal hM.
have hTerm (j:'I_m.+2):
    @holomorphic_germ_directional_coefficient R X NX hNX a (m.+1-j)%N (holomorphic_germ f) v *
      @holomorphic_germ_directional_coefficient R X NX hNX a j alpha v =
    if j==i then xi v*@holomorphic_germ_directional_coefficient R X NX hNX a m alpha v else 0.
  rewrite (@pointed_holomorphic_functional_germ_directional_coefficient R X NX hNX a xi f _ v hValues).
  case:(eqVneq j i)=>[->|hDifferent].
  - by rewrite /i /= subSn // subnn eqxx.
  - have hIndex:(m.+1-j)%N != 1%N.
      apply/eqP=>hOne.
      have hEqual:j = i.
        apply:val_inj.
        have hLe:(j<=m.+1)%N:=ltn_ord j.
        have hSum:=subnK hLe;rewrite hOne add1n in hSum.
        exact:(congr1 predn hSum).
      by rewrite hEqual eqxx in hDifferent.
    by rewrite (negbTE hIndex) mul0r.
under eq_bigr do rewrite hTerm.
rewrite (bigD1 i) //= eqxx.
have hRest:(\sum_(j<m.+2|j!=i)
    if j==i then xi v*@holomorphic_germ_directional_coefficient R X NX hNX a m alpha v else 0) = 0.
  apply:big1=>j hj;by rewrite (negbTE hj).
by rewrite hRest addr0.
Qed.

(** Source for [pointed_holomorphic_functional_product_zero_coefficient]:
    the actual coordinate germ vanishes at its centre,
    so its product has zero constant coefficient.
    This supports 3.4.8(5), p. 328. *)
Lemma pointed_holomorphic_functional_product_zero_coefficient (R:realType) (X:lmodType (ComplexScalars.C R))
  (NX:X->R) (hNX:is_complex_norm NX) a (xi:Hom X (ComplexScalars.C R)^o)
  (f:@holomorphic_representative_type R X NX (complex_norm_real hNX) a)
  (alpha:[the comNzRingType of (@holomorphic_germ_ring R X NX (complex_norm_real hNX) a)]) v:
  (forall x,holomorphic_representative_value f x = xi (x-a)) ->
  @holomorphic_germ_directional_coefficient R X NX hNX a 0%N ((holomorphic_germ f:@holomorphic_germ_ring R X NX (complex_norm_real hNX) a)*alpha) v = 0.
Proof.
move=>hValues;rewrite holomorphic_germ_directional_coefficient_product big_ord_recl big_ord0 /=.
by rewrite (@pointed_holomorphic_functional_germ_directional_coefficient R X NX hNX a xi f 0%N v hValues) mul0r addr0.
Qed.
