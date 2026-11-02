(** Federer (1969), 3.2.11, p. 249: letting
    epsilon decrease to zero in the critical-rank estimate. *)
From mathcomp Require Import all_boot all_order all_algebra reals constructive_ereal lra ring.
From Federer Require Import ExtendedScaledErrorBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [coarea_vanishing_perturbation]: the final
    epsilon argument in Federer 3.2.11, p. 249.
    Includes zero source mass and every natural exponent. *)
Lemma coarea_vanishing_perturbation (R:realType) n (a K L M:R):
  0<=a ->0<=K ->0<=L ->0<=M ->
  (forall e,0<e ->a<=K*(e*(L+e)^+n)*M) ->a=0.
Proof.
move=>ha hK hL hM hBound.
pose C:=K*(L+1)^+n*M.
have hL1:0<=L+1 by lra.
have hC:0<=C:=mulr_ge0 (mulr_ge0 hK (exprn_ge0 n hL1)) hM.
have hError (r:R):0<r ->(a%:E<=(0+C*r)%R%:E)%E.
  move=>hr; pose e:=Num.min r (1/2)%R.
  have he:0<e by rewrite /e lt_min hr; nra.
  have her:e<=r by rewrite /e ge_min lexx.
  have heHalf:e<=1/2 by rewrite /e ge_min lexx orbT.
  have he1:e<=1 by nra.
  have hMe:0<=L+e:=addr_ge0 hL (ltW he).
  have hPow:(L+e)^+n<=(L+1)^+n:=lerXn2r n hMe hL1 (lerD (lexx L) he1).
  rewrite lee_fin add0r.
  apply:le_trans (hBound e he) _.
  have hFirst:=ler_wpM2r hM (ler_wpM2l hK (ler_wpM2l (ltW he) hPow)).
  have hStep:K*(e*(L+e)^+n)*M<=C*e.
    have hFactor:K*(e*(L+1)^+n)*M=C*e by rewrite /C; ring.
    by rewrite hFactor in hFirst.
  exact:le_trans hStep (ler_wpM2l hC her).
have hz:=(extended_upper_bound_from_scaled_errors (x:=a%:E) hC hError).
apply/eqP; rewrite eq_le ha andbT.
by move:hz; rewrite lee_fin.
Qed.
