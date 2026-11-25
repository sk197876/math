(** Federer (1969), 4.1.7, p. 357: the
    degree-zero vector/covector identification has the
    absolute scalar dual norm. The supporting Euclidean
    result follows from 1.7.5, p. 33, in every degree. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Bilinear InnerProductUP InnerNorm InnerNormalization InnerExterior
  InnerExteriorPositivity ExteriorNorm ExteriorCovectorInner ExteriorPairingBound
  ExteriorGrading AlternatingForms AlternatingPairing PairingLinear LinearBasis RealFunctionalNormUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section ExteriorPairingFunctionalNorm.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variable V:lmodType R.
Variable B:V->V->R.
Hypothesis hB:is_inner_product B.
Variable n:nat.
Variable e:'I_n->V.
Hypothesis he:is_basis e.
Variable m:nat.
Local Notation X := (exterior_power V m).
Local Notation N := (@exterior_norm R h2 V B hB m).
Local Notation D := (@exterior_covector_norm R h2 V B hB n e he m).
Local Notation C := (@exterior_inner_form R h2 V B hB m).
Local Notation hC := (@exterior_inner_productP R h2 V B hB m).

(** Source for [exterior_pairing_unit_attained]: the
    Euclidean pairing norm is attained on the covector
    unit ball, supporting the dual identification in
    Federer 4.1.7, p. 357, from 1.7.5, p. 33. *)
Lemma exterior_pairing_unit_attained (xi:X):
  exists phi:A_m V R^o m,D phi<= 1 /\pairing xi phi=N xi.
Proof.
have [->|hx]:=eqVneq xi 0.
- exists 0; split.
  + rewrite /D /exterior_covector_norm inner_norm0; exact:ler01.
  + by rewrite (bil0l (@pairing_bilinear R V R^o m)) exterior_norm_zero.
pose y:=inner_normalize hC xi.
pose phi:=inner_exterior_form h2 hB y.
have hy:N y= 1:=inner_normalize_norm hC hx.
exists phi; split.
- by rewrite /phi inner_exterior_form_norm hy.
- rewrite -{1}(inner_normalizeK hC hx) (bilZl (@pairing_bilinear R V R^o m)).
  change (N xi*C y y=N xi).
  by rewrite -(@exterior_norm_square R h2 V B hB m y) hy expr1n mulr1.
Qed.

(** Source for [exterior_pairing_real_functional_norm]:
    exact Euclidean dual norm, including degree zero,
    supporting Federer 4.1.7, p. 357. *)
Theorem exterior_pairing_real_functional_norm (xi:X):
  is_real_functional_norm D (pairing_right xi) (N xi).
Proof.
constructor.
- exact:exterior_norm_nonnegative.
- move=>phi; exact:exterior_pairing_bound.
- move=>a ha hb.
  have [phi [hphi hp]]:=exterior_pairing_unit_attained xi.
  have h:=hb phi.
  change (is_true (`|pairing xi phi| <= a * D phi)) in h.
  rewrite hp (ger0_norm (exterior_norm_nonnegative h2 hB xi)) in h.
  apply:(le_trans h).
  have hh:=ler_wpM2l ha hphi.
  by rewrite mulr1 in hh.
Qed.
End ExteriorPairingFunctionalNorm.
