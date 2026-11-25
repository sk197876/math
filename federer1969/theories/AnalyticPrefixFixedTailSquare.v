(** Federer (1969), 3.4.8(6), p. 329:
    fixing the tail basis vectors makes the prefix
    of h(x) depend only on the original prefix
    of x. This exact square supplies coordinate
    subring invariance; no invariance is assumed. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import Hom TensorUP LinearBasis GrassmannAbbreviations FiniteCoordinates
  BasisInterpolation AnalyticPrefixCoordinatesUP AnalyticPrefixBasisValues.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [analytic_prefix_fixed_tail_square]: the
    actual coordinate identity supporting Q_j invariance
    under H_j in 3.4.8(6), p. 329. The
    proof checks exactly the original dual basis. *)
Theorem analytic_prefix_fixed_tail_square (R:realType) (X:lmodType R)
  n (e:'I_n->X) (he:is_basis e) (omega:'I_n->Hom X R^o)
  p (hPN:(p<=n)%N) (P:Hom X (R_n R p)) (S:Hom (R_n R p) X) (H:Hom X X):
  (forall i k,omega i (e k) = if i==k then 1 else 0) ->
  is_analytic_prefix_projection omega hPN P ->is_analytic_prefix_section e hPN S ->
  (forall i:'I_n,(p<=i)%N ->H (e i) = e i) ->
  forall x,P (H (S (P x))) = P (H x).
Proof.
move=>hDual hP hS hFixed.
apply:(@basis_linear_ext R (Choice.clone 'I_n _) X e he (R_n R p)
  (hom_as_linear (hom_comp P (hom_comp H (hom_comp S P))))
  (hom_as_linear (hom_comp P H)))=>i.
rewrite !hom_as_linearE !hom_compE.
case:(ltnP i p)=>hIP.
- pose k:'I_p:=Ordinal hIP.
  have hIndex:widen_ord hPN k = i by apply:val_inj.
  rewrite -hIndex (@analytic_prefix_basis_inside R X n e omega p hPN P hP hDual k) hS.
  by [].
- have hZero:=@analytic_prefix_basis_outside R X n e omega p hPN P hP hDual i hIP.
  by rewrite hZero !linear0 /= (hFixed i hIP) hZero.
Qed.
