(** Federer (1969), 3.4.12, p. 339: a real functional
    supplies an actual complex functional through its imaginary
    rotation. Reuse the original linear embedding and rotation
    maps; this algebraic connection assumes no boundedness or norm. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals ring.
From Federer Require Import Hom ScalarRestriction ComplexScalarUP ComplexScalarSealed ComplexScalarLaws
  ComplexCoefficientAlgebra HermitianRotation ComplexRealLinearMap ComplexLinearImaginaryCriterion.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory ComplexScalarTheory.
Local Open Scope ring_scope.
Section Functionals.
Variable R:realType.
Variable X:lmodType (ComplexScalars.C R).
Local Notation XR:=(restricted_space (ComplexScalars.embed R) X).
Local Notation C:=(ComplexScalars.C R).
Local Notation CR:=(restricted_space (ComplexScalars.embed R) C^o).
Local Notation e:=(ComplexScalars.embed R).
Local Notation ii:=(ComplexScalars.ii R).

(** Source for [complex_functional_from_real_exists]: the actual
    functional f(x)-i f(ix), supporting the original complex
    transverse splitting of 3.4.6, p. 322, extended in
    3.4.12, p. 339. Its original real part is f. *)
Theorem complex_functional_from_real_exists (f:Hom XR R^o):
  exists L:Hom X C^o,
    (forall x,L x=e (f x)-ii*e (f (ii*:x))) /\forall x,ComplexScalars.re (L x)=f x.
Proof.
pose J:Hom XR XR:=hom_of_linear (GRing.Linear.clone R XR XR *:%R (@hermitian_rotation R X) _).
pose E:Hom R^o CR:=hom_of_linear (GRing.Linear.clone R R^o CR *:%R (@complex_scalar_embedding R) _).
pose I:Hom CR CR:=hom_of_linear (@complex_left_multiply_map R ii).
pose P:=hom_comp E f.
pose Q:=hom_comp I (hom_comp P J).
pose M:Hom XR CR:=P+(-1:R)*:Q.
have hValues x:M x=e (f x)-ii*e (f (ii*:x)).
  by rewrite /M hom_addE hom_scaleE scaleN1r /P /Q !hom_compE.
have hImaginary x:M (ii*:x)=ii*:(M x:C^o).
  rewrite !hValues scalerA (complex_i_square (ComplexScalars.laws R)) scaleN1r.
  change (e (f (ii*:x))-ii*e (f (-x))=ii*(e (f x)-ii*e (f (ii*:x)))).
  rewrite (linearN f) rmorphN mulrN opprK mulrBr mulrA
    (complex_i_square (ComplexScalars.laws R)) mulN1r opprK.
  exact:addrC.
have [L hL]:=complex_real_linear_map_exists (complex_real_linear_imaginary_criterion hImaginary).
exists L;split;first by move=>x;rewrite hL hValues.
move=>x;rewrite hL hValues (complex_re_add (ComplexScalars.laws R)) re_neg re_embed re_i_real.
by rewrite oppr0 addr0.
Qed.
End Functionals.
