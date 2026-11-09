(** Order algebra supporting Federer (1969),
    3.3.4, p. 291: a finite positive
    aperture weight commutes with the actual
    arbitrary radius supremum. Both infinities
    and an empty family are retained. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal.
From Federer Require Import ExtendedRealBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [extended_real_sup_positive_scalar]:
    supporting the displayed psi_v radius
    supremum and aperture normalization in
    Federer 3.3.4, p. 291. Multiplication
    by a positive finite scalar preserves
    both least-upper-bound laws on the
    original family, including infinite values. *)
Theorem extended_real_sup_positive_scalar (R:realType) (A:set (\bar R)) (c:R):
  0<c ->extended_real_sup ((fun z: \bar R=>(c%:E*z)%E) @` A)=
    (c%:E*extended_real_sup A)%E.
Proof.
move=>hc.
pose S:=extended_real_sup ((fun z: \bar R=>(c%:E*z)%E) @` A).
have hcE:(0<=c%:E)%E by rewrite lee_fin ltW.
have hUpper:(S<=c%:E*extended_real_sup A)%E.
  apply:extended_real_sup_least=>z [x hx <-].
  change ((c%:E*x<=c%:E*extended_real_sup A)%E).
  apply:lee_wpmul2l=>//; exact:extended_real_sup_upper hx.
have hUnscaled:(extended_real_sup A<=(c^-1)%:E*S)%E.
  apply:extended_real_sup_least=>z hz.
  rewrite (lee_pdivlMl _ _ hc).
  apply:extended_real_sup_upper; by exists z.
have hLower: (c%:E*extended_real_sup A<=S)%E.
  have h:=lee_wpmul2l hcE hUnscaled.
  by rewrite muleA -EFinM mulfV ?gt_eqF // mul1e in h.
apply/eqP; by rewrite eq_le hUpper hLower.
Qed.
