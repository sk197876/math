(** Federer (1969), 4.1.11, p. 365: integrate the
    original mixed time power by the scalar fundamental
    theorem of 3.1.11, pp. 220–221. A primitive is only
    an existence witness; the weight and its coefficient
    were specified independently. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals ring.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormDifferentialArithmetic
  NormHigherCurveDerivativeUP ScalarCoefficientLinearAlgebra ScalarUnitMixedPower ScalarBetaCoefficient.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section ScalarBetaPrimitive.
Variable R:realType.
Local Notation N := (fun t:R^o=>`|t|).
Local Notation hN := (@scalar_absolute_value_norm R).
Local Notation Full := (fun _:R=>True).
Local Notation W := (@scalar_unit_mixed_power R).
Local Notation B := (@scalar_beta_coefficient R).
Local Notation D := (@scalar_unit_mixed_power_derivative R).

(** Source for [scalar_beta_primitive_exists]: the original
    time weight has a primitive whose endpoint difference
    is i!j!/(i+j+1)!, supporting Federer 4.1.11, p. 365.
    The induction uses the derivative of (1-t)^(i+1)t^(j+1)
    and the already proved factorial recurrence. *)
Theorem scalar_beta_primitive_exists i j:
  exists P:R->R,
    (forall t,has_norm_differential N N Full P t
      (@scalar_coefficient_linear_map R R^o (W i j t))) /\
    P 1-P 0=B i j.
Proof.
elim:i j=>[|i IH] j.
- have hJ:(j.+1%:R:R)!=0 by rewrite pnatr_eq0.
  pose P t:=(j.+1%:R:R)^-1*t^+j.+1.
  exists P;split.
  + move=>t.
    have hPower:=@scalar_unit_right_power_differential R j.+1 t.
    have hScaled:=@norm_differential_scale R R^o R^o N N hN hN Full
      (fun s:R=>s^+j.+1) t _ (j.+1%:R:R)^-1 hPower.
    rewrite -scalar_coefficient_linear_scale in hScaled.
    change (has_norm_differential N N Full P t
      (@scalar_coefficient_linear_map R R^o ((j.+1%:R:R)^-1*(j.+1%:R*t^+j)))) in hScaled.
    rewrite mulrA (mulVf hJ) mul1r in hScaled.
    change (has_norm_differential N N Full P t
      (@scalar_coefficient_linear_map R R^o ((1-t)^+0*t^+j))).
    by rewrite expr0 mul1r.
  + by rewrite /P expr1n expr0n mulr1 mulr0 subr0 scalar_beta_coefficient_zero.
- have hJ:(j.+1%:R:R)!=0 by rewrite pnatr_eq0.
  have [P [hPD hPE]]:=IH j.+1.
  pose q:=W i.+1 j.+1.
  pose a:=(j.+1%:R:R)^-1.
  pose b:=(i.+1%:R:R)*a.
  pose F t:=a*q t+b*P t.
  exists F;split.
  + move=>t.
    have hQ:=@scalar_unit_mixed_power_differential R i.+1 j.+1 t.
    have hScaledQ:=@norm_differential_scale R R^o R^o N N hN hN Full
      q t _ a hQ.
    have hScaledP:=@norm_differential_scale R R^o R^o N N hN hN Full
      P t _ b (hPD t).
    rewrite -scalar_coefficient_linear_scale in hScaledQ hScaledP.
    have hSum:=@norm_differential_add R R^o R^o N N hN Full
      (fun s=>a*q s) (fun s=>b*P s) t _ _ hScaledQ hScaledP.
    rewrite -scalar_coefficient_linear_scale -scalar_coefficient_linear_add in hSum.
    change (has_norm_differential N N Full F t
      (@scalar_coefficient_linear_map R R^o (a*D i.+1 j.+1 t+b*W i j.+1 t))) in hSum.
    have hDQ:D i.+1 j.+1 t=j.+1%:R*W i.+1 j t-i.+1%:R*W i j.+1 t.
      rewrite /scalar_unit_mixed_power_derivative /scalar_unit_mixed_power /=;ring.
    have hCoefficient:a*D i.+1 j.+1 t+b*W i j.+1 t=W i.+1 j t.
      rewrite hDQ /b.
      have hReorder:a*(j.+1%:R*W i.+1 j t-i.+1%:R*W i j.+1 t)+
          (i.+1%:R*a)*W i j.+1 t=(a*j.+1%:R)*W i.+1 j t by ring.
      by rewrite hReorder /a mulVf // mul1r.
    by rewrite hCoefficient in hSum.
  + have hQ0:q 0=0 by rewrite /q /scalar_unit_mixed_power expr0n mulr0.
    have hQ1:q 1=0 by rewrite /q /scalar_unit_mixed_power subrr expr0n mul0r.
    rewrite /F hQ0 hQ1 !mulr0 !add0r -mulrBr hPE
      scalar_beta_coefficient_successor.
    by [].
Qed.
End ScalarBetaPrimitive.
