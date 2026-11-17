(** Federer (1969), 3.4.12, p. 339, extending 3.4.8(1),(5),
    pp. 326, 328: an original pointed complex coordinate has
    only its first divided directional coefficient. Reuse exact
    real parameter lines with the same complex-valued target. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP ScalarRestriction ComplexScalarSealed ComplexNormUP ComplexModulus ComplexScalarNorm
  NormAnalyticUP AnalyticDirectionalCoefficient AnalyticDirectionalPolynomialLine
  HolomorphicGermRepresentatives HolomorphicGermUP HolomorphicGermRing HolomorphicGermDirectionalCoefficient.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [pointed_holomorphic_functional_germ_directional_coefficient]:
    the actual germ xi(x-a) has coefficient xi(v) in
    order one and zero in every other order, extending
    3.4.8(1),(5), pp. 326, 328, under 3.4.12, p. 339. *)
Lemma pointed_holomorphic_functional_germ_directional_coefficient (R:realType)
    (X:lmodType (ComplexScalars.C R)) (NX:X->R) (hNX:is_complex_norm NX) a
    (xi:Hom X (ComplexScalars.C R)^o)
    (f:@holomorphic_representative_type R X NX (complex_norm_real hNX) a) k v:
  (forall x,holomorphic_representative_value f x=xi (x-a)) ->
  @holomorphic_germ_directional_coefficient R X NX hNX a k (holomorphic_germ f) v=
    if k==1%N then xi v else 0.
Proof.
move=>hValues.
pose XR:=restricted_space (ComplexScalars.embed R) X.
pose CR:=restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o.
pose hNXR:=complex_norm_real hNX.
pose N:=@complex_modulus R.
pose hN:=@complex_modulus_real_norm R.
pose F:=holomorphic_representative_value f.
have [U [ha [hF _]]]:=holomorphic_representative_holomorphic f.
have [c [hc _]]:=@analytic_directional_coefficient_exists R XR CR NX N hNXR hN U F k v hF.
have hActual:=@holomorphic_directional_coefficient_at_germ_centre R X NX hNX a k
  (holomorphic_germ f) f U v c (erefl _) ha hF hc.
pose b:=fun j:nat=>if j==0%N then (0:CR) else xi v.
have hLine (t:R) (ht:`|t|<1):F ((a:XR)+t*:(v:XR))=\sum_(j<2) t^+j*:b j.
  rewrite /F hValues [((a:XR)+t*:(v:XR))]addrC addrK linearZ /=.
  rewrite !big_ord_recl big_ord0 /= /b expr0 expr1 scaler0 addr0 add0r.
  reflexivity.
have hValue:=@analytic_directional_polynomial_line_coefficient R XR CR NX N hNXR hN
  U F k v a c 2%N b 1 ha hF hc ltr01 hLine.
rewrite -hActual hValue /b.
clear hc hActual hValue;by case:k=>[|[|k]].
Qed.
