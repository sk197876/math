(** Supporting algebra for Federer (1969), 3.4.8(8),
    pp. 329–330: the actual roots of a split
    polynomial are precisely the listed roots.
    Reuse its independent product-evaluation law and
    ordinary field product arithmetic. Source:
    Bourbaki, Algebra II (1990), Chapter V,
    section 4, no. 2, pp. V.21–22. *)
From mathcomp Require Import all_boot all_order all_algebra boolp.
From Federer Require Import CommutativePolynomialEvaluationUP PolynomialLinearSplitUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [linear_polynomial_split_root_criterion]:
    the roots of the original product are its
    listed linear roots, counted with multiplicity
    in the cited splitting-factorisation definition.
    The criterion remains exact in each further
    field extension used for 3.4.8(8), pp. 329–330. *)
Theorem linear_polynomial_split_root_criterion (K:fieldType) (B:comNzRingType)
  (embed:{rmorphism K->B}) (variable P:B) d (L:fieldType)
  (phi:{rmorphism K->L}) (c:L) (roots:seq L)
  (hSplit:is_linear_polynomial_split embed variable P d phi c roots)
  (Z:fieldType) (psi:{rmorphism L->Z}) (chi:{rmorphism K->Z})
  (z:Z) (E:{rmorphism B->Z}):
  (forall a:K,chi a = psi (phi a)) ->
  is_commutative_polynomial_evaluation embed variable chi z E ->
  (E P = 0 <->exists r:L,r \in roots /\z = psi r).
Proof.
move=>hChi hE.
have hValue:=@linear_split_evaluation K B embed variable P d L phi c roots hSplit Z psi chi z E hChi hE.
have hC:psi c!=0.
  rewrite fmorph_eq0;apply/eqP;exact:linear_split_scalar_nonzero hSplit.
split.
- move=>hZero.
  have hProduct:(\prod_(r<-roots) (z-psi r)) = 0.
    apply:(mulfI hC);by rewrite mulr0 -hValue.
  move/eqP:hProduct;rewrite prodf_seq_eq0 /=.
  move/hasP=>[r hR hMatch];exists r;split;first exact:hR.
  apply/eqP;move:hMatch;by rewrite subr_eq0.
- move=>[r [hR hMatch]].
  have hProduct:(\prod_(a<-roots) (z-psi a)) = 0.
    apply/eqP;rewrite prodf_seq_eq0;apply/hasP;exists r;first exact:hR.
    by rewrite /= hMatch subrr eqxx.
  by rewrite hValue hProduct mulr0.
Qed.
