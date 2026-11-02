(** Federer (1969), 3.2.22, p. 259:
    the source-area Jacobian factor adds m to the
    two mu powers in the local integral comparison. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import PositiveFactorSandwich.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [coarea_parameter_product_bounds]: supporting
    the last display of Federer 3.2.22, p. 259.
    Combine p inverse times j <=f<=p times j
    and t inverse <=s<=t to compare j times s
    with f by the factor p times t. All densities
    may vanish; positivity is required only for the
    two distortion constants. *)
Lemma coarea_parameter_product_bounds (R:realType) (p t j s f:R):
  0<p ->0<t ->0<=j ->p^-1*j<=f ->f<=p*j ->t^-1<=s ->s<=t ->
  j*s<=(p* t)*f /\ f<=(p* t)*(j*s).
Proof.
move=>hp ht hj hLower hUpper hsLower hsUpper.
have [hProdLower hProdUpper]:=positive_factor_sandwich ht hj hsLower hsUpper (erefl (s*j)).
have hjF:j<=p*f.
  have hScaled:=ler_wpM2l (ltW hp) hLower.
  have hNe:p!=0 by rewrite(gt_eqF hp).
  by rewrite mulrA (mulfV hNe) mul1r in hScaled.
have hJs:j*s<=t*j by rewrite mulrC; exact:(ler_wpM2r hj hsUpper).
have hJBack:j<=t*(j*s) by rewrite [j*s]mulrC; exact hProdUpper.
split.
- have hScaled:=ler_wpM2l (ltW ht) hjF.
  have hRearrange:t*(p*f)=(p* t)*f by rewrite mulrA [t* p]mulrC.
  rewrite hRearrange in hScaled; exact:(le_trans hJs hScaled).
- apply:(le_trans hUpper); rewrite -mulrA.
  exact:(ler_wpM2l (ltW hp) hJBack).
Qed.
