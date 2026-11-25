(** Federer (1969), 4.1.24, p. 382: the
    mass distance and rectifiable decomposition costs are
    unchanged by inversion. This narrow supporting adapter
    applies the already proved finite mass scaling bound
    twice. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals constructive_ereal.
From Federer Require Import Hom RealNormUP NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  CurrentSpaces CurrentMassSealed CurrentMassBasic CurrentFiniteMassLinearBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Section CurrentFiniteMassNegation.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Variable U:set (R_n R n).
Hypothesis hU:forall x,U x->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) U x.
Local Notation C:=(@current_space R h2 n U hU m).
Local Notation M:=(@CurrentMass.value R h2 n m U hU).

(** Source for [current_finite_mass_negation]: the equality
    M(-T)=M(T), used for the original metrics of
    4.1.24, p. 382. Only the finite case needed
    here is asserted; no representation witness is required. *)
Theorem current_finite_mass_negation (T:C):
  (M T< +oo)%E->M (-T)=M T.
Proof.
move=>hFinite.
have[a [ha hA]]:=@current_finite_mass_value R h2 n m U hU T hFinite.
have hAUpper:(M T<=a%:E)%E by rewrite hA.
have hNegUpper:=@current_finite_mass_scale_bound R h2 n m U hU (-1) T a hAUpper.
rewrite scaleN1r normrN normr1 mul1r in hNegUpper.
have hNegFinite:(M (-T)< +oo)%E:=le_lt_trans hNegUpper (ltry a).
have[b [hb hB]]:=@current_finite_mass_value R h2 n m U hU (-T) hNegFinite.
have hBUpper:(M (-T)<=b%:E)%E by rewrite hB.
have hReverse:=@current_finite_mass_scale_bound R h2 n m U hU (-1) (-T) b hBUpper.
rewrite scaleN1r opprK normrN normr1 mul1r in hReverse.
apply/eqP;rewrite eq_le;apply/andP;split.
- rewrite hA;exact:hNegUpper.
- rewrite hB;exact:hReverse.
Qed.
End CurrentFiniteMassNegation.
