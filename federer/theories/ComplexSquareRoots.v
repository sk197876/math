(** Federer (1969), 3.4.12, p. 339: algebraic closedness
    gives exactly two distinct square roots of each nonzero original
    complex scalar. This supplies the fibres of the actual square
    covering model, without a selected branch of the square root. *)
From mathcomp Require Import all_boot all_order all_algebra boolp ring reals.
From Federer Require Import ScalarRestriction ComplexScalarSealed ComplexScalarAlgebraicClosure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [original_complex_nonzero_square_roots]: every
    original nonzero w has the two distinct roots z and -z,
    with no other roots, supporting 3.4.12, p. 339. *)
Theorem original_complex_nonzero_square_roots (R:realType) (w:ComplexScalars.C R):
  w<>0 ->exists z:ComplexScalars.C R,z<>0 /\z<> -z /\z^+2=w /\
    forall y:ComplexScalars.C R,y^+2=w <->y=z \/y= -z.
Proof.
move=>hW.
have hPositive:(0<2)%N by [].
have [z hZ]:=@complex_scalar_algebraically_closed R 2%N (fun i=>if i==0%N then w else 0) hPositive.
have hRoot:z^+2=w.
  move:hZ;by rewrite !big_ord_recr big_ord0 /= expr0 mulr1 mul0r !addr0 !add0r.
have hNonzero:z<>0.
  move=>hZero;apply:hW;by rewrite -hRoot hZero expr0n.
have hTwo:(2:ComplexScalars.C R)!=0.
  rewrite -(@rmorph_nat R (ComplexScalars.C R) (ComplexScalars.embed R) 2) fmorph_eq0.
  by rewrite pnatr_eq0.
have hDifferent:z<> -z.
  move=>hEqual;have hProduct:(2:ComplexScalars.C R)*z=0.
    change ((1+1)*z=0);by rewrite mulrDl !mul1r {1}hEqual addNr.
  move/eqP:hProduct;rewrite mulf_eq0 (negbTE hTwo) /= =>/eqP hZero.
  exact:hNonzero hZero.
exists z;split;first exact:hNonzero.
split;first exact:hDifferent.
split;first exact:hRoot.
move=>y;split.
- move=>hY.
  have hFactor:(y-z)*(y+z)=y^+2-z^+2 by ring.
  have hProduct:(y-z)*(y+z)=0 by rewrite hFactor hY hRoot subrr.
  move/eqP:hProduct;rewrite mulf_eq0 subr_eq0 addr_eq0=>/orP[/eqP h|/eqP h];[by left|by right].
- move=>[->|->];first exact:hRoot.
  by rewrite expr2 mulNr mulrN opprK -expr2 hRoot.
Qed.
