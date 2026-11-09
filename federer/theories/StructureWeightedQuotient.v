(** Federer (1969), 3.3.4, p. 291:
    positive finite denominator comparisons used to
    replace the actual reference ball quotient by
    the original unnormalized ball costs. Infinite
    numerator values remain permitted throughout. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [structure_weighted_quotient_upper]:
    supporting the zero-limit comparison in Federer
    3.3.4, p. 291. If the finite denominator
    times the original positive weight is at most
    K, an actual smaller numerator has weighted
    cost at most K times the reference quotient. *)
Lemma structure_weighted_quotient_upper (R:realType)
    (A B: \bar R) (b w K:R):
  (0<=B)%E ->(A<=B)%E ->0<b ->0<w ->b*w<=K ->
  (A*w%:E<=K%:E*(B/b%:E))%E.
Proof.
move=>hB hAB hb hw hCoefficient.
have hCancel:((b*w)%:E*(B/b%:E)=B*w%:E)%E.
  rewrite inver (gt_eqF hb) [b*w]mulrC EFinM -muleA.
  rewrite [(b%:E*(B*(b^-1)%:E))%E]muleCA.
  by rewrite -EFinM mulfV ?gt_eqF // mule1 muleC.
have hwE:(0<=w%:E)%E by rewrite lee_fin ltW.
apply:le_trans (lee_wpmul2r hwE hAB) _.
rewrite -hCancel; apply:lee_wpmul2r=>//.
by rewrite mule_ge0 // inve_ge0 lee_fin ltW.
Qed.

(** Source for [structure_weighted_quotient_lower]:
    supporting the infinite-upper-limit comparison in
    Federer 3.3.4, p. 291. A closed-ball
    numerator lies below that of a larger open
    ball. A finite inverse-denominator bound gives
    the corresponding weighted larger-ball bound. *)
Lemma structure_weighted_quotient_lower (R:realType)
    (A B: \bar R) (b w K:R):
  (0<=A)%E ->(B<=A)%E ->0<b ->0<w ->b^-1<=K*w ->
  (B/b%:E<=K%:E*(A*w%:E))%E.
Proof.
move=>hA hBA hb hw hCoefficient.
rewrite inver (gt_eqF hb).
apply:le_trans (lee_wpmul2r _ hBA) _; first by rewrite lee_fin invr_ge0 ltW.
have hBound:(A*(b^-1)%:E<=A*(K*w)%:E)%E.
  apply:lee_wpmul2l=>//; by rewrite lee_fin.
by rewrite EFinM [(A*(K%:E*w%:E))%E]muleCA in hBound.
Qed.
