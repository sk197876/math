(** Supporting Federer (1969), 3.4.8(5), p. 328:
    multiplication by an actual pointed coordinate
    shifts divided directional coefficients by one
    order. This is the original Leibniz formula
    of 3.1.11, p. 222, with the proved
    coefficient values of the actual linear factor. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP AnalyticGermUP AnalyticGermRing AnalyticGermRepresentatives
  AnalyticGermDirectionalCoefficient AnalyticGermDirectionalProduct PointedFunctionalGermCoefficient.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [pointed_functional_product_successor_coefficient]:
    the successor coefficient of xi(x-a) times an
    original germ is xi(v) times its previous
    coefficient. This expands the radial factorisation
    argument for 3.4.8(5), p. 328. *)
Lemma pointed_functional_product_successor_coefficient (R:realType) (X:lmodType R)
  (NX:X->R) (hNX:is_real_norm NX) a (xi:Hom X R^o)
  (f:@analytic_representative_type R X NX hNX a)
  (alpha:[the comNzRingType of (@analytic_germ_ring R X NX hNX a)]) m v:
  (forall x,analytic_representative_value f x = xi (x-a)) ->
  @analytic_germ_directional_coefficient R X NX hNX a m.+1 ((analytic_germ f:@analytic_germ_ring R X NX hNX a)*alpha) v =
    xi v*@analytic_germ_directional_coefficient R X NX hNX a m alpha v.
Proof.
move=>hValues;rewrite analytic_germ_directional_coefficient_product.
have hM:(m<m.+2)%N:=ltnW (ltnSn m.+1).
pose i:'I_m.+2:=Ordinal hM.
have hTerm (j:'I_m.+2):
    @analytic_germ_directional_coefficient R X NX hNX a (m.+1-j)%N (analytic_germ f) v *
      @analytic_germ_directional_coefficient R X NX hNX a j alpha v =
    if j==i then xi v*@analytic_germ_directional_coefficient R X NX hNX a m alpha v else 0.
  rewrite (@pointed_functional_germ_directional_coefficient R X NX hNX a xi f _ v hValues).
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
    if j==i then xi v*@analytic_germ_directional_coefficient R X NX hNX a m alpha v else 0) = 0.
  apply:big1=>j hj;by rewrite (negbTE hj).
by rewrite hRest addr0.
Qed.

(** Source for [pointed_functional_product_zero_coefficient]:
    the actual coordinate germ vanishes at its centre,
    so its product has zero constant coefficient.
    This supports 3.4.8(5), p. 328. *)
Lemma pointed_functional_product_zero_coefficient (R:realType) (X:lmodType R)
  (NX:X->R) (hNX:is_real_norm NX) a (xi:Hom X R^o)
  (f:@analytic_representative_type R X NX hNX a)
  (alpha:[the comNzRingType of (@analytic_germ_ring R X NX hNX a)]) v:
  (forall x,analytic_representative_value f x = xi (x-a)) ->
  @analytic_germ_directional_coefficient R X NX hNX a 0%N ((analytic_germ f:@analytic_germ_ring R X NX hNX a)*alpha) v = 0.
Proof.
move=>hValues;rewrite analytic_germ_directional_coefficient_product big_ord_recl big_ord0 /=.
by rewrite (@pointed_functional_germ_directional_coefficient R X NX hNX a xi f 0%N v hValues) mul0r addr0.
Qed.
