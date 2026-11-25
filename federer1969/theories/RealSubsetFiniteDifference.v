(** Federer (1969), 4.1.5, p. 350:
    differences of the scalar ball integrals,
    by 2.4.4 and 2.4.10, pp. 82–85.
    Both finite integral values are retained
    and no undefined infinite difference is used. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals constructive_ereal topology.
From Federer Require Import MeasureUP MeasureIntegralUP MeasureSubsetIntegral RealSubsetIntegralGraph
  SummableRealFunctionUP SummableRealArithmetic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [real_subset_finite_difference_integral]: the
    finite difference of actual subset integrals,
    supporting the ball quotient argument in
    Federer 4.1.5, p. 350. *)
Lemma real_subset_finite_difference_integral (R:realType) (X:choiceType)
    (mu:set X->\bar R) (hm:is_measure mu) (A:set X) (f g:X->R) (a b:R):
  is_measure_subset_integral mu A (real_total_integrand f) a%:E ->
  is_measure_subset_integral mu A (real_total_integrand g) b%:E ->
  is_measure_subset_integral mu A (real_total_integrand (fun x=>f x-g x)) (a-b)%:E.
Proof.
move=>hF hG.
pose F x:=if pselect (A x) then f x else 0%R.
pose G x:=if pselect (A x) then g x else 0%R.
have hFOn x:A x ->F x=f x by rewrite /F; case:pselect.
have hFOff x:~A x ->F x=0 by rewrite /F; case:pselect.
have hGOn x:A x ->G x=g x by rewrite /G; case:pselect.
have hGOff x:~A x ->G x=0 by rewrite /G; case:pselect.
have hTotalF:=(@real_subset_integral_total R X mu A f F a%:E hFOn hFOff).1 hF.
have hTotalG:=(@real_subset_integral_total R X mu A g G b%:E hGOn hGOff).1 hG.
have hDifference:=@real_total_integral_subtract R X mu hm F G a b hTotalF hTotalG.
apply:(@real_subset_integral_total R X mu A (fun x=>f x-g x)
  (fun x=>F x-G x) (a-b)%:E _ _).2 hDifference.
- by move=>x hx; rewrite (hFOn x hx) (hGOn x hx).
- by move=>x hx; rewrite (hFOff x hx) (hGOff x hx) subrr.
Qed.
