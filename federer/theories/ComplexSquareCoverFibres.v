(** Federer (1969), 3.4.12, p. 339: the original complex
    equation z squared equals w has exactly two points over each
    nonzero w. Apply the proved square-root theorem to the actual
    connected polynomial graph used in the covering qualification. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import ScalarRestriction ComplexScalarSealed ComplexScalarNorm ComplexModulus RealNormUP NormMetric
  ComplexSquareRoots ComplexSquareCoverObstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Fibres.
Variable R:realType.
Local Notation C:=(ComplexScalars.C R).
Local Notation M:=(real_norm_metric_space (@complex_modulus_real_norm R)).
Local Notation V:=(@complex_square_punctured_graph R).
(** Source for [complex_square_graph_two_point_fibre]: every actual
    nonzero base point has exactly two distinct original graph points,
    supporting the finite-covering qualification of 3.4.12, p. 339. *)
Theorem complex_square_graph_two_point_fibre (w:C):
  w<>0 ->exists a b:M*M,a<>b /\
    V a /\V b /\a.1=w /\b.1=w /\
    forall p:M*M,V p /\p.1=w <->p=a \/p=b.
Proof.
move=>hW.
have [z [hZ [hDifferent [hRoot hRoots]]]]:=@original_complex_nonzero_square_roots R w hW.
pose a:M*M:=(w,z).
pose b:M*M:=(w,-z).
have hA:V a by split;first exact:hZ;exact:esym hRoot.
have hNegative:(-z:C)<>0 by move=>hZero;apply:hZ;by rewrite -[z]opprK hZero oppr0.
have hB:V b.
  split;first exact:hNegative.
  change (w=(-z)^+2).
  by rewrite expr2 mulNr mulrN opprK -expr2 hRoot.
exists a,b;split.
- move=>hEqual;apply:hDifferent;exact:(congr1 (fun p:M*M=>p.2) hEqual).
- split;first exact:hA.
  split;first exact:hB.
  split;first by [].
  split;first by [].
  move=>p;split.
  + move=>[[hNonzero hEquation] hPrefix].
    have hSquare:p.2^+2=w by rewrite -hEquation hPrefix.
    have [hFirst|hSecond]:=(hRoots p.2).1 hSquare.
    * left;change (p=(w,z));have hPair:=surjective_pairing p;by rewrite hPrefix hFirst in hPair.
    * right;change (p=(w,-z));have hPair:=surjective_pairing p;by rewrite hPrefix hSecond in hPair.
  + move=>[->|->];split=>//.
Qed.
End Fibres.
