(** Federer (1969), 2.5.7, p. 99: the representing density is almost unique,
    by 2.4.16. The difference represents zero, so the already proved exact
    norm identity and zero-norm criterion force almost equality. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal.
From Federer Require Import MeasureUP MeasureAlmostUP MeasureAlmostBasic FunctionOperatorSeminorm
  TotalScalarLpUP TotalScalarLpLattice TotalScalarLpNormLaws TotalScalarLpFiniteSeminorm
  TotalScalarLpZeroCriterion TotalScalarPairingValue TotalLpPairingLinear LpConjugatePair RepresentingDensityNorm.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [representing_density_almost_unique]: the final
    almost-uniqueness assertion in Federer 2.5.7, p. 99 This consequence
    needs no sigma-finiteness once both representing densities exist in Lq. *)
Theorem representing_density_almost_unique (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) p q (A : (X -> R) -> R) (k l : X -> R) :
  is_lp_conjugate_pair p q -> total_scalar_lp mu q k -> total_scalar_lp mu q l ->
  (forall f, total_scalar_lp mu p f -> A f=total_scalar_pairing mu f k) ->
  (forall f, total_scalar_lp mu p f -> A f=total_scalar_pairing mu f l) ->
  measure_almost_everywhere mu [set x | k x=l x].
Proof.
move=> hpq hk hl hkr hlr.
pose d x := (k x-l x)%R.
have hd := @total_scalar_lp_subtract R X mu hm q k l hk hl.
have hrepr f : total_scalar_lp mu p f -> (0%R : R)=total_scalar_pairing mu f d.
  move=> hf; rewrite /d (@total_lp_pairing_subtract_density R X mu hm p q f k l hpq hf hk hl).
  by rewrite -(hkr f hf) -(hlr f hf) subrr.
have hnorm := @representing_density_operator_norm R X mu hm p q (fun _ => 0%R) d hpq hd hrepr.
have hbound : total_scalar_lp_norm mu q d <= 0.
  rewrite -hnorm.
  apply: (@function_operator_seminorm_least_bound R X (total_scalar_lp mu p)
    (fun _ => 0%R) (finite_total_scalar_lp_norm mu p) 0%R (lexx _))=> f hf.
  by rewrite normr0 mul0r.
have hz : total_scalar_lp_norm mu q d=0.
  apply/eqP; rewrite eq_le hbound andTb.
  exact: (@total_scalar_lp_norm_nonnegative R X mu hm q d hd.1 hd.2.1).
have he := @total_scalar_lp_zero_norm_almost_zero R X mu hm q d hd hz.
apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ he)=> x hx.
apply/eqP; rewrite -subr_eq0; exact/eqP.
Qed.
