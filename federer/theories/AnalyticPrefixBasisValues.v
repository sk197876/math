(** Federer (1969), 3.4.8(1),(6), pp. 326, 329:
    the exact prefix equations on the original dual
    bases identify the fixed tail with the kernel.
    These are supporting coordinate identities. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import Hom TensorUP LinearBasis GrassmannAbbreviations FiniteCoordinates
  AnalyticPrefixCoordinatesUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section BasisValues.
Variable R:realType.
Variable X:lmodType R.
Variable n:nat.
Variable e:'I_n->X.
Variable omega:'I_n->Hom X R^o.
Variable p:nat.
Variable hPN:(p<=n)%N.
Variable P:Hom X (R_n R p).
Hypothesis hP:is_analytic_prefix_projection omega hPN P.
Hypothesis hDual:forall i k,omega i (e k) = if i==k then 1 else 0.

(** Source for [analytic_prefix_basis_inside]: the first
    p basis vectors map to the original coordinate
    basis of R^p, 3.4.8(1), p. 326. *)
Lemma analytic_prefix_basis_inside (i:'I_p):
  P (e (widen_ord hPN i)) = @coordinate_basis R p i.
Proof.
apply/ffunP=>j;rewrite hP hDual /coordinate_basis ffunE.
by rewrite -!val_eqE /=.
Qed.

(** Source for [analytic_prefix_basis_outside]: all original
    tail basis vectors have zero prefix,
    3.4.8(1), p. 326. *)
Lemma analytic_prefix_basis_outside (i:'I_n):
  (p<=i)%N ->P (e i) = 0.
Proof.
move=>hPI;apply/ffunP=>j;rewrite hP hDual ffunE.
have hDiff:widen_ord hPN j != i.
  apply/eqP=>hEqual.
  have hValues:(j:nat) = (i:nat):=congr1 (fun t:'I_n=>(t:nat)) hEqual.
  have hTooSmall:(i<p)%N by rewrite -hValues;exact:ltn_ord.
  have hFalse:=leq_ltn_trans hPI hTooSmall.
  by rewrite ltnn in hFalse.
by rewrite (negbTE hDiff).
Qed.
End BasisValues.
