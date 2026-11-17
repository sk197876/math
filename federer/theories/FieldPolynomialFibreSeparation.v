(** Federer (1969), 3.4.12, p. 339, extending 3.4.8(10), p. 332:
    the first transverse coordinate determines a
    point in each original fibre. Apply
    the exact numerator equations and the
    original prefix/suffix separation theorem. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom Bilinear LinearBasis GrassmannAbbreviations FiniteCoordinates
  FieldPrefixCoordinatesUP OrdinalCoordinateTail FieldPrefixSuffixSeparation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section FibreSeparation.
Variable R:fieldType.
Variable X:lmodType R.
Variables n m:nat.
Variable e:'I_n->X.
Hypothesis he:is_basis e.
Variable omega:'I_n->Hom X R^o.
Hypothesis hDual:forall i j,omega i (e j) = if i==j then 1 else 0.
Hypothesis hMN:(m<=n)%N.
Variable P:Hom X (coordinate_space R m).
Hypothesis hP:is_field_prefix_projection omega hMN P.
Variable first:'I_(n-m).
Local Notation tail:=(ordinal_coordinate_tail_index hMN).

(** Source for [field_polynomial_fibre_separation]:
    the separation by omega_(m+1)
    in 3.4.8(10), p. 332,
    is well defined: equal first coordinates
    in one original fibre give equal
    points. No assertion of global projection
    injectivity is imposed. *)
Theorem field_polynomial_fibre_separation (x y:X) (delta:R)
    (t:'I_(n-m)->R):
  delta!=0 ->P x = P y ->omega (tail first) x=omega (tail first) y ->
  (forall j,j!=first ->delta*omega (tail j) x=t j) ->
  (forall j,j!=first ->delta*omega (tail j) y=t j) ->x=y.
Proof.
move=>hDelta hPrefix hFirst hX hY.
have hSuffix j:omega (tail j) x=omega (tail j) y.
  case:(eqVneq j first)=>[->|hJ];first exact:hFirst.
  apply:(mulfI hDelta).
  by rewrite (hX j hJ) (hY j hJ).
have hPrefixZero:P (x-y)=0 by rewrite (linB (hom_linear P)) hPrefix subrr.
have hSuffixZero j:omega (tail j) (x-y)=0.
  by rewrite (linB (hom_linear (omega (tail j)))) hSuffix subrr.
have hZero:=@field_prefix_suffix_separate R X n e he omega hDual m hMN P hP
  (x-y) hPrefixZero hSuffixZero.
by apply/eqP;rewrite -subr_eq0 hZero eqxx.
Qed.
End FibreSeparation.
