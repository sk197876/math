(** Federer (1969), 3.2.39, p. 276: uniform
    finite scalar approximations to full radius limits. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal lra.
From Federer Require Import PositiveRadiusLimits PositiveRadiusLimitBounds ExtendedRealBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [positive_radius_upper_finite_approximation]:
    supporting the finite sum of upper limits in Federer
    3.2.39, p. 276. The bound holds at every small
    positive real radius, not only reciprocal radii. *)
Lemma positive_radius_upper_finite_approximation (R:realType) (f:R->\bar R) (b e:R):
  positive_radius_upper_limit f<=b%:E ->(0<e)%R ->
  exists d:R,(0<d)%R /\forall r:R,(0<r<d)%R ->f r<=(b+e)%R%:E.
Proof.
move=>hBound he.
have hStrict:positive_radius_upper_limit f<(b+e)%R%:E.
  apply:le_lt_trans hBound _; rewrite lte_fin ltrDl; exact he.
have [d [hd hSup]]:=(positive_radius_upper_lt_iff f _).1 hStrict.
exists d; split=>// r hr; apply:ltW.
apply:le_lt_trans _ hSup; apply:extended_real_sup_upper.
by exists r.
Qed.

(** Source for [positive_radius_lower_finite_approximation]:
    supporting the finite sum of lower limits in Federer
    3.2.39, p. 276. The infimum/supremum laws give
    a common real-radius neighbourhood without assuming any
    convergence or finiteness of the function values. *)
Lemma positive_radius_lower_finite_approximation (R:realType) (f:R->\bar R) (b e:R):
  b%:E<=positive_radius_lower_limit f ->(0<e)%R ->
  exists d:R,(0<d)%R /\forall r:R,(0<r<d)%R ->(b-e)%R%:E<=f r.
Proof.
move=>hBound he; apply:contrapT=>hNo.
have hUpper:positive_radius_lower_limit f<=(b-e)%R%:E.
  apply:extended_real_sup_least=>y [d [hd ->]].
  rewrite leNgt; apply/negP=>hInf.
  apply:hNo; exists d; split=>// r hr; apply:ltW.
  apply:lt_le_trans hInf _; apply:extended_real_inf_lower.
  by exists r.
have hFalse:=le_trans hBound hUpper.
rewrite lee_fin in hFalse.
have hStrict:(b-e<b)%R by rewrite ltrBlDr ltrDl.
have hBad:=lt_le_trans hStrict hFalse; by rewrite ltxx in hBad.
Qed.
