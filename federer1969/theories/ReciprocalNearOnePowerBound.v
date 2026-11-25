(** Federer (1969), 3.2.19, p. 256: the final passage
    lambda=1+1/k to density one. Prove the scalar bound directly
    by finite-power algebra and the local Archimedean reciprocal lemma. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal lra.
From Federer Require Import ExtendedRealReciprocalBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(** Source for [inverse_near_one_power_lower_bound]: supporting finite
    scalar estimate in the final sentence of Federer 3.2.19, p. 256.
    For t>=0 the inverse pth power of 1+t is at least 1-p*t.
    This algebraic estimate includes p=0 and avoids importing a separate
    convergence theorem for the power sequence. *)
Lemma inverse_near_one_power_lower_bound (R : realType) p (t : R) :
  (0<=t)%R -> (1-p%:R*t<=((1+t)^+p)^-1)%R.
Proof.
move=> ht.
have hPos : (0<1+t)%R by lra.
have hPoly : ((1+t)^+p*(1-p%:R*t)<=1)%R.
  elim: p=> [|p ih]; first by rewrite expr0 mul1r mul0r subr0.
  have hQ : (0<=(1+t)^+p)%R := exprn_ge0 p (ltW hPos).
  have hCoeff : (0<=p%:R+1 :> R)%R by rewrite addr_ge0 // ler0n.
  have hError : ((0:R)<=(p%:R+1)*t^+2)%R := mulr_ge0 hCoeff (sqr_ge0 t).
  have hStep : ((1+t)*(1-(p%:R+1)*t)<=1-p%:R*t)%R by nra.
  rewrite exprS -natr1.
  apply: le_trans _ ih.
  rewrite [((1+t)*(1+t)^+p)%R]mulrC -mulrA; exact: (ler_wpM2l hQ hStep).
have hPow : (0<(1+t)^+p)%R := exprn_gt0 p hPos.
rewrite -div1r ler_pdivlMr // mulrC; exact hPoly.
Qed.

(** Source for [reciprocal_near_one_power_forces_one]: the final
    lambda=1+1/k argument in Federer 3.2.19, p. 256.
    An extended real bounded below by all the printed inverse-power
    constants is at least one. Infinite values and exponent zero remain
    part of the statement. *)
Theorem reciprocal_near_one_power_forces_one (R : realType) p (x : \bar R) :
  (forall k, (((1+((k.+1)%:R : R)^-1)^+p)^-1)%R%:E<=x) -> 1<=x.
Proof.
case: x=> [s| |] hBound; [|exact: leey|].
- rewrite lee_fin leNgt; apply/negP=> hs.
  pose c := (p%:R+1 : R)%R.
  have hc : (0<c)%R by rewrite /c ltr_wpDl ?ler0n //.
  have he : (0<(1-s)/c)%R by rewrite divr_gt0 // subr_gt0.
  have [k hk] := positive_reciprocal_nat_small he.
  pose t := (((k.+1)%:R : R)^-1)%R.
  have ht : (0<t)%R by rewrite /t invr_gt0 ltr0n.
  have hct : (c*t<1-s)%R.
    by move: hk; rewrite -/t ltr_pdivlMr // mulrC.
  have hp : (0<=p%:R :> R)%R by rewrite ler0n.
  have hpt : (p%:R*t<c*t)%R by rewrite /c ltr_pM2r // ltrDl ltr01.
  have hInv := @inverse_near_one_power_lower_bound R p t (ltW ht).
  have hx := hBound k; rewrite lee_fin -/t in hx.
  have hLe := le_trans hInv hx; nra.
- have hh := hBound 0%N; by rewrite leNgt ltNyr in hh.
Qed.
