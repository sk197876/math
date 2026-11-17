(** Supporting algebra for Federer (1969), 3.4.8(5), p. 328.
    Compare finite-jet growth in two original coordinate dimensions.
    Only natural-number arithmetic is needed. *)
From mathcomp Require Import all_boot all_order all_algebra.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope nat_scope.

(** Source for [natural_polynomial_growth_dimension]: supporting
    finite-jet count comparison for the auxiliary sentence in Federer
    3.4.8(5), p. 328. If r^m is bounded by C*(a*r+b)^d at every
    positive integer r, then m<=d, including both zero dimensions. *)
Theorem natural_polynomial_growth_dimension (m d C a b:nat):
  (forall r, 0 < r -> r ^ m <= C * (a * r + b) ^ d) -> m <= d.
Proof.
move=>hGrowth;case:(leqP m d)=>// hDM.
pose D:=a+b.
pose r:=(C * D ^ d).+2.
have hr:0 < r by rewrite /r.
have hAffine:a * r + b <= D * r.
  rewrite /D mulnDl;apply:leq_add;first exact:leqnn.
  have hh:=leq_mul (leqnn b) hr;by rewrite muln1 in hh.
have hPower:(a * r + b) ^ d <= (D * r) ^ d.
  case:(posnP d)=>[hD|hD].
  - by rewrite hD !expn0.
  - by rewrite leq_exp2r.
have hUpper:r ^ m <= C * D ^ d * r ^ d.
  have hh:=leq_trans (hGrowth r hr) (leq_mul (leqnn C) hPower).
  by rewrite expnMn mulnA in hh.
have hLower:r ^ d.+1 <= r ^ m:=leq_pexp2l hr hDM.
have hCompare:=leq_trans hLower hUpper.
rewrite expnS in hCompare.
have hPositive:0 < r ^ d by rewrite expn_gt0 hr.
have hTooSmall:r <= C * D ^ d by move:hCompare;rewrite leq_pmul2r.
have hStrict:C * D ^ d < r:=ltn_trans (ltnSn (C * D ^ d)) (ltnSn (C * D ^ d).+1).
have hImpossible:=leq_ltn_trans hTooSmall hStrict.
by rewrite ltnn in hImpossible.
Qed.
