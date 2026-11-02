(** Federer (1969), 3.2.13, p. 250: cancellation of a
    finite nonzero radial factor in an actual sphere integral,
    from 2.4.4(3), p. 82, and 2.4.10, p. 85. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal.
From Federer Require Import PartialFunctionUP MeasureUP MeasureIntegralUP MeasureSubsetIntegral
  RealSubsetIntegralGraph SummableRealFunctionUP SummableRealArithmetic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [real_subset_integral_cancel_finite_scale]: the
    nonzero finite scaling law on the actual integration domain,
    supporting the angular integral in Federer 3.2.13, p. 250.
    No measurability of the unscaled function is assumed. *)
Lemma real_subset_integral_cancel_finite_scale (R:realType) (X:choiceType)
    (mu:set X->\bar R) (hm:is_measure mu) (A:set X) (f g:X->R) (b c:R):
  c!=0 ->(forall x,A x->f x=c*g x) ->
  is_measure_subset_integral mu A (real_total_integrand f) b%:E ->
  is_measure_subset_integral mu A (real_total_integrand g) (c^-1*b)%:E.
Proof.
move=>hc hEq hi.
pose fA x:=if pselect (A x) then f x else 0%R.
pose gA x:=if pselect (A x) then g x else 0%R.
have hfOn x:A x->fA x=f x.
  by move=>hx; rewrite /fA; case:(pselect (A x))=>// hn; exfalso; exact:hn hx.
have hfOff x:~A x->fA x=0.
  by move=>hx; rewrite /fA; case:(pselect (A x))=>// hy; exfalso; exact:hx hy.
have hgOn x:A x->gA x=g x.
  by move=>hx; rewrite /gA; case:(pselect (A x))=>// hn; exfalso; exact:hn hx.
have hgOff x:~A x->gA x=0.
  by move=>hx; rewrite /gA; case:(pselect (A x))=>// hy; exfalso; exact:hx hy.
have hTotal:=(@real_subset_integral_total R X mu A f fA b%:E hfOn hfOff).1 hi.
have hScaled:=@real_total_integral_scale R X mu hm fA b c^-1 hTotal.
have hFun:(fun x=>c^-1*fA x)=gA.
  apply:funext=>x; case:(pselect (A x))=>hx.
  - by rewrite (hfOn x hx) (hgOn x hx) (hEq x hx) mulrA mulVf // mul1r.
  - by rewrite (hfOff x hx) (hgOff x hx) mulr0.
rewrite hFun in hScaled.
exact:(@real_subset_integral_total R X mu A g gA (c^-1*b)%:E hgOn hgOff).2 hScaled.
Qed.

(** Source for [real_subset_integral_multiply_finite_scale]: finite
    nonzero homogeneity of a subset integral, Federer 2.4.4(3),
    p. 82, used for the angular factor in 3.2.13, p. 250. *)
Lemma real_subset_integral_multiply_finite_scale (R:realType) (X:choiceType)
    (mu:set X->\bar R) (hm:is_measure mu) (A:set X) (f g:X->R) (b c:R):
  c!=0 ->(forall x,A x->f x=c*g x) ->
  is_measure_subset_integral mu A (real_total_integrand g) b%:E ->
  is_measure_subset_integral mu A (real_total_integrand f) (c*b)%:E.
Proof.
move=>hc hEq hi.
have hci:c^-1!=0 by rewrite invr_eq0.
have hBack x:A x->g x=c^-1*f x.
  by move=>hx; rewrite (hEq x hx) mulrA mulVf // mul1r.
have h:=@real_subset_integral_cancel_finite_scale R X mu hm A g f b c^-1 hci hBack hi.
by rewrite invrK in h.
Qed.
