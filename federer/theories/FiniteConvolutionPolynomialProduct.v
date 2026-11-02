(** Federer (1969), 3.2.36, p. 273: the actual
    convolution of coefficients multiplies their finite generating polynomials. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import FinitePolynomialDegreeGrouping.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [finite_degree_polynomial_grouping]: finite grouping
    by i+j in the elementary symmetric-function consequence of
    Federer 3.2.36, p. 273. Partitioning by the actual natural
    degree proves the polynomial identity without positivity or a
    new polynomial implementation. *)
Lemma finite_degree_polynomial_grouping (R:realType) m n
    (c:'I_m.+1->'I_n.+1->R) (t:R):
  \sum_(i:'I_m.+1) \sum_(j:'I_n.+1) c i j*t^+(i+j)=
    \sum_(d:'I_(m+n).+1) (\sum_(i:'I_m.+1) \sum_(j:'I_n.+1|(i+j==d)%N) c i j)*t^+d.
Proof.
pose I:=[the finType of ('I_m.+1*'I_n.+1)%type].
have hBound (p:I):(p.1+p.2<(m+n).+1)%N.
  rewrite ltnS; apply:leq_add; by have:=ltn_ord p.1; have:=ltn_ord p.2; rewrite !ltnS.
pose degree (p:I):'I_(m+n).+1:=Ordinal (hBound p).
have h:=@finite_polynomial_degree_grouping R I (m+n) degree (fun p=>c p.1 p.2) t.
rewrite pair_bigA h; apply:eq_bigr=>d _; congr (_*t^+d).
rewrite pair_big_dep; apply:eq_bigl=>p.
by rewrite andTb -val_eqE /degree.
Qed.

(** Source for [finite_convolution_polynomial_product]: the generating
    polynomial form of the convolution in Federer 3.2.36,
    p. 273. Distributivity, the natural power addition law and
    finite degree grouping prove the complete identity, including
    zeroth-degree factors and arbitrary real coefficient values. *)
Lemma finite_convolution_polynomial_product (R:realType) m n
    (a:'I_m.+1->R) (b:'I_n.+1->R) (t:R):
  (\sum_(i:'I_m.+1) a i*t^+i)*(\sum_(j:'I_n.+1) b j*t^+j)=
    \sum_(d:'I_(m+n).+1) (\sum_(i:'I_m.+1) \sum_(j:'I_n.+1|(i+j==d)%N) a i*b j)*t^+d.
Proof.
rewrite mulr_suml.
have hExpand:(\sum_(i:'I_m.+1) a i*t^+i*(\sum_(j:'I_n.+1) b j*t^+j))=
    \sum_(i:'I_m.+1) \sum_(j:'I_n.+1) (a i*b j)*t^+(i+j).
  apply:eq_bigr=>i _; rewrite mulr_sumr; apply:eq_bigr=>j _.
  by rewrite exprD mulrACA.
rewrite hExpand; exact:finite_degree_polynomial_grouping.
Qed.
