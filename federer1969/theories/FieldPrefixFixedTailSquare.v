(** Federer (1969), 3.4.12, pp. 338–339: complex extension
    of the passages identified below. Earlier real and algebraic
    source locators are retained for the results reused here. *)
(** Federer (1969), 3.4.8(6), p. 329:
    fixing the tail basis vectors makes the prefix
    of h(x) depend only on the original prefix
    of x. This exact square supplies coordinate
    subring invariance; no invariance is assumed. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import Hom TensorUP LinearBasis GrassmannAbbreviations FiniteCoordinates
  BasisInterpolation FieldPrefixCoordinatesUP FieldPrefixBasisValues.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [field_prefix_fixed_tail_square]: the
    actual coordinate identity supporting Q_j invariance
    under H_j in 3.4.8(6), p. 329. The
    proof checks exactly the original dual basis. *)
Theorem field_prefix_fixed_tail_square (K:fieldType) (X:lmodType K)
  n (e:'I_n->X) (he:is_basis e) (omega:'I_n->Hom X K^o)
  p (hPN:(p<=n)%N) (P:Hom X (coordinate_space K p)) (S:Hom (coordinate_space K p) X) (H:Hom X X):
  (forall i k,omega i (e k) = if i==k then 1 else 0) ->
  is_field_prefix_projection omega hPN P ->is_field_prefix_section e hPN S ->
  (forall i:'I_n,(p<=i)%N ->H (e i) = e i) ->
  forall x,P (H (S (P x))) = P (H x).
Proof.
move=>hDual hP hS hFixed.
apply:(@basis_linear_ext K (Choice.clone 'I_n _) X e he (coordinate_space K p)
  (hom_as_linear (hom_comp P (hom_comp H (hom_comp S P))))
  (hom_as_linear (hom_comp P H)))=>i.
rewrite !hom_as_linearE !hom_compE.
case:(ltnP i p)=>hIP.
- pose k:'I_p:=Ordinal hIP.
  have hIndex:widen_ord hPN k = i by apply:val_inj.
  rewrite -hIndex (@field_prefix_basis_inside K X n e omega p hPN P hP hDual k) hS.
  by [].
- have hZero:=@field_prefix_basis_outside K X n e omega p hPN P hP hDual i hIP.
  by rewrite hZero !linear0 /= (hFixed i hIP) hZero.
Qed.
