(** Federer (1969), 3.2.40, p. 276: supporting full-radius
    order-limit arguments for the Cantor square and the cited
    compact triangular surface. These lemmas do not assume
    existence or geometry of either example. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal.
From Federer Require Import PositiveRadiusLimits PositiveRadiusLimitBounds
  PositiveRadiusLowerApproximation ExtendedRealBounds ExtendedNaturalMultiples
  ExtendedScaledErrorBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [positive_radius_upper_infinite_from_spikes]: supporting
    upper-content infinity in Federer 3.2.40, p. 276. Arbitrarily
    large values occur at arbitrarily small positive real radii;
    no convergence along all radii is inferred from this alone. *)
Lemma positive_radius_upper_infinite_from_spikes (R:realType) (f:R->\bar R):
  (forall (b d:R),(0<d)%R ->exists r:R,(0<r<d)%R /\b%:E<=f r) ->
  positive_radius_upper_limit f=+oo.
Proof.
move=>hSpikes.
have hAll (b:R):b%:E<=positive_radius_upper_limit f.
  rewrite leNgt; apply/negP=>hSmall.
  have [d [hd hSup]]:=(positive_radius_upper_lt_iff f b%:E).1 hSmall.
  have [r [hr hb]]:=hSpikes b d hd.
  have hValue:positive_radius_values f d (f r) by exists r.
  have hBad:=le_lt_trans (le_trans hb (extended_real_sup_upper hValue)) hSup.
  by rewrite ltxx in hBad.
have hOne:0<(1:R)%:E by rewrite lte_fin.
apply:(@positive_natural_multiples_force_infinity R (1:R)%:E _ hOne).
move=>n; rewrite mule1; exact:hAll.
Qed.

(** Source for [positive_radius_lower_infinite_from_eventual_bounds]:
    supporting the common infinite surface content cited in Federer
    3.2.40, p. 276. Every finite bound holds at every sufficiently
    small positive real radius, rather than just on a subsequence. *)
Lemma positive_radius_lower_infinite_from_eventual_bounds (R:realType) (f:R->\bar R):
  (forall b:R,exists d:R,(0<d)%R /\forall r:R,(0<r<d)%R ->b%:E<=f r) ->
  positive_radius_lower_limit f=+oo.
Proof.
move=>hBounds.
have hOne:0<(1:R)%:E by rewrite lte_fin.
apply:(@positive_natural_multiples_force_infinity R (1:R)%:E _ hOne).
move=>n; rewrite mule1.
have [d [hd hBound]]:=hBounds n%:R.
exact:positive_radius_lower_eventual_bound hd hBound.
Qed.

(** Source for [positive_radius_lower_bound_from_small_values]: supporting
    the finite or zero lower content in Federer 3.2.40, p. 276.
    Approximate upper bounds attained at arbitrarily small radii give
    a lower-limit upper bound; all other radii remain unrestricted. *)
Lemma positive_radius_lower_bound_from_small_values (R:realType)
    (f:R->\bar R) (b:R):
  (forall (e d:R),(0<e)%R ->(0<d)%R ->
    exists r:R,(0<r<d)%R /\f r<=(b+e)%R%:E) ->
  positive_radius_lower_limit f<=b%:E.
Proof.
move=>hSmall; apply:extended_real_sup_least=>y [d [hd ->]].
apply:(@extended_upper_bound_from_scaled_errors R _ b 1 ler01)=>e he.
rewrite mul1r.
have [r [hr hValue]]:=hSmall e d he hd.
apply:le_trans _ hValue; apply:extended_real_inf_lower.
by exists r.
Qed.

(** Source for [positive_radius_lower_zero_from_small_values]: supporting
    the strict subcritical Cantor-square case of Federer 3.2.40,
    p. 276. Actual nonnegativity plus the small-radius upper
    estimates proves zero; no real-degree normalization is assumed. *)
Lemma positive_radius_lower_zero_from_small_values (R:realType) (f:R->\bar R):
  (forall r:R,(0<r)%R ->0<=f r) ->
  (forall (e d:R),(0<e)%R ->(0<d)%R ->
    exists r:R,(0<r<d)%R /\f r<=e%:E) ->
  positive_radius_lower_limit f=0.
Proof.
move=>hNonnegative hSmall; apply/eqP; rewrite eq_le.
apply/andP; split; last exact:positive_radius_lower_nonnegative.
apply:(@positive_radius_lower_bound_from_small_values R f 0)=>e d he hd.
by rewrite add0r; exact:hSmall.
Qed.
