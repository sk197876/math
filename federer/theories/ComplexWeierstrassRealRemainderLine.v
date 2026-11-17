(** Federer (1969), 3.4.12, p. 339: the original
    complex finite remainder restricts to a real polynomial on
    every distinguished real line. Retain its actual complex
    coefficients and use the original embedding for the parameter. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom ScalarRestriction ComplexScalarSealed ComplexWeierstrassTransverseUP
  ComplexWeierstrassFiniteRemainderLine.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section Lines.
Variable R:realType.
Variables X K:lmodType (ComplexScalars.C R).
Variables (NX:X->R) (NK:K->R).
Variable v:X.
Variable xi:Hom X (ComplexScalars.C R)^o.
Variable inclusion:Hom K X.
Variable projection:Hom X K.
Variable k:nat.
Variable D:nat->X->ComplexScalars.C R.
Hypothesis hSplit:is_complex_weierstrass_transverse_space NX NK v xi inclusion projection.
Local Notation XR:=(restricted_space (ComplexScalars.embed R) X).
Local Notation CR:=(restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o).
Local Notation F:=(fun x=>\sum_(i<k) (xi x)^+i*D i (inclusion (projection x))).

(** Source for [complex_weierstrass_real_transverse_line]: the actual
    low coefficients on the original transverse real line, extending
    3.4.6, pp. 322–324, under 3.4.12, p. 339. *)
Lemma complex_weierstrass_real_transverse_line z (t:R):
  F ((inclusion z:XR)+t*:(v:XR))=\sum_(i<k) t^+i*:(D i (inclusion z):CR).
Proof.
have h:=@complex_weierstrass_finite_remainder_transverse_line R X K NX NK v xi inclusion projection k D
  hSplit z (ComplexScalars.embed R t).
rewrite h;apply:eq_bigr=>i _.
change ((ComplexScalars.embed R t)^+i*D i (inclusion z)=
  ComplexScalars.embed R (t^+i)*D i (inclusion z)).
by rewrite rmorphXn.
Qed.

(** Source for [complex_weierstrass_real_shifted_line]: the original
    finite degree bound survives every real line translation,
    supporting the neighbourhood derivative condition in 3.4.12,
    p. 339, extending 3.4.6(1), pp. 321–322. *)
Theorem complex_weierstrass_real_shifted_line (a:X):
  exists b:nat->ComplexScalars.C R,forall t:R,
    F ((a:XR)+t*:(v:XR))=\sum_(i<k) t^+i*:(b i:CR).
Proof.
have [b hb]:=@complex_weierstrass_finite_remainder_shifted_line R X K NX NK v xi inclusion projection
  k D hSplit a.
exists b=>t;rewrite (hb (ComplexScalars.embed R t));apply:eq_bigr=>i _.
change ((ComplexScalars.embed R t)^+i*b i=ComplexScalars.embed R (t^+i)*b i).
by rewrite rmorphXn.
Qed.
End Lines.
