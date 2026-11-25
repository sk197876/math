(** Supporting the Steiner coefficient connection in Federer
    (1969), 3.2.45, p. 279.
    Reuse the original finite root-count theorem. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates FinitePowerEvaluationUP PolynomialCoefficientUniqueness.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [finite_power_evaluation_injective]: supporting
    finite coefficient recovery for Federer 3.2.45,
    p. 279. A polynomial with N+1
    coefficients vanishing at N+1 distinct positive
    scalars has every coefficient zero, by
    the already proved synthetic-division root count
    behind 1.10.4, p. 46.
    This law is proved from the independent
    evaluation equations before constructing any inverse. *)
Theorem finite_power_evaluation_injective (R : realType) N
    (E : {linear R_n R N.+1 -> R_n R N.+1}) :
  is_finite_power_evaluation E ->injective E.
Proof.
move=> hE c d hEqual.
pose s : seq R^o := [seq c (inord i)-d (inord i)|i<-iota 0 N.+1].
pose r : seq R := map (fun j : 'I_N.+1 => (j.+1%:R : R)) (enum 'I_N.+1).
have hSize : (size s<=N.+1)%N by rewrite /s size_map size_iota.
have hLength : size r=N.+1 by rewrite /r size_map size_enum_ord.
have hNodes : injective (fun j : 'I_N.+1 => (j.+1%:R : R)).
  move=> i j h; apply: val_inj; apply: succn_inj.
  exact: (@characteristic_zero_nat_injective R (@pchar_num R) _ _ h).
have hUnique : uniq r by rewrite /r (map_inj_uniq hNodes) enum_uniq.
have hZero x : x \in r ->coefficient_polynomial_value s x=0.
  move=> /mapP[j _ ->].
  have hExpansion : coefficient_polynomial_value s ((j.+1)%:R)=
      \sum_(i : 'I_N.+1) (c i-d i)*((j.+1)%:R)^+i.
    rewrite coefficient_polynomial_sum /s size_map size_iota.
    apply: eq_bigr=> i _.
    rewrite (nth_map 0) ?size_iota ?ltn_ord // nth_iota ?ltn_ord // add0n inord_val.
    change (((j.+1)%:R)^+i*(c i-d i)=(c i-d i)*((j.+1)%:R)^+i).
    exact: mulrC.
  rewrite hExpansion; under eq_bigr do rewrite mulrBl.
  by rewrite sumrB -(hE c j) -(hE d j) hEqual subrr.
have /allP hAll := @coefficient_polynomial_roots R R^o N.+1 s r hSize hLength hUnique hZero.
apply/ffunP=> i; apply/eqP; rewrite -subr_eq0.
apply: hAll; apply/mapP; exists (i:nat).
- by rewrite mem_iota add0n leq0n ltn_ord.
- by rewrite inord_val.
Qed.
