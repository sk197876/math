(** Federer (1969), 1.6.6, pp. 26-27: the complex basis formed by one-forms
    and their conjugates. This supporting scalar inverse recovers the two
    coefficients from values on e and i e. Source context are recorded in
    ComplexScalarUP.v. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import ComplexScalarUP ComplexScalarSealed ComplexCharacteristic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section Coordinates.
Variable R : realFieldType.
Local Notation C := (ComplexScalars.C R).
Local Notation ii := (ComplexScalars.ii R).
Local Notation H := (ComplexScalars.laws R).

(** Source for [holomorphic_coefficient]: Federer 1.6.6,
    p. 27, mixed complex/conjugate basis. Supporting coordinate
    (u-i v)/2 for the unbarred basis member. *)
Definition holomorphic_coefficient (u v : C) := (u - ii * v) / (1+1).

(** Source for [antiholomorphic_coefficient]: Federer 1.6.6,
    p. 27, mixed complex/conjugate basis. Supporting coordinate
    (u+i v)/2 for the conjugate basis member. *)
Definition antiholomorphic_coefficient (u v : C) := (u + ii * v) / (1+1).

(** Source for [complex_pair_coordinate_sum]: Federer 1.6.6,
    p. 27, mixed basis. The two coefficients reconstruct the value at e. *)
Lemma complex_pair_coordinate_sum u v :
  holomorphic_coefficient u v + antiholomorphic_coefficient u v = u.
Proof.
rewrite /holomorphic_coefficient /antiholomorphic_coefficient -mulrDl addrACA addNr addr0.
have hu : u+u = u * (1+1) by rewrite mulrDr !mulr1.
by rewrite hu mulfK ?complex_two_nonzero.
Qed.

(** Source for [complex_pair_coordinate_difference]: Federer
    1.6.6, p. 27, mixed basis. The imaginary multiple of the difference
    reconstructs the value at i e. *)
Lemma complex_pair_coordinate_difference u v :
  ii * (holomorphic_coefficient u v - antiholomorphic_coefficient u v) = v.
Proof.
rewrite /holomorphic_coefficient /antiholomorphic_coefficient -mulrBl opprD addrACA subrr add0r.
have hv : -(ii*v) - ii*v = (- (ii*v)) * (1+1) by rewrite mulrDr !mulr1.
rewrite hv mulfK ?complex_two_nonzero // mulrN mulrA (complex_i_square H).
by rewrite mulN1r opprK.
Qed.

(** Source for [holomorphic_coefficient_pair]: Federer 1.6.6,
    p. 27, mixed basis. The first inverse coordinate recovers the
    coefficient of an unbarred one-form. *)
Lemma holomorphic_coefficient_pair c d :
  holomorphic_coefficient (c+d) (ii * (c-d)) = c.
Proof.
rewrite /holomorphic_coefficient mulrA (complex_i_square H) mulN1r opprK.
rewrite addrACA subrr addr0.
have hc : c+c = c * (1+1) by rewrite mulrDr !mulr1.
by rewrite hc mulfK ?complex_two_nonzero.
Qed.

(** Source for [antiholomorphic_coefficient_pair]: Federer
    1.6.6, p. 27, mixed basis. The second inverse coordinate recovers
    the coefficient of a conjugate one-form. *)
Lemma antiholomorphic_coefficient_pair c d :
  antiholomorphic_coefficient (c+d) (ii * (c-d)) = d.
Proof.
rewrite /antiholomorphic_coefficient mulrA (complex_i_square H) mulN1r opprD opprK.
rewrite addrACA subrr add0r.
have hd : d+d = d * (1+1) by rewrite mulrDr !mulr1.
by rewrite hd mulfK ?complex_two_nonzero.
Qed.
End Coordinates.
