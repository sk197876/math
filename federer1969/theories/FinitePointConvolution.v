(** Federer (1969), 3.2.36, p. 273: a point factor
    removes all but one term of the product convolution. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(** Source for [finite_point_convolution_inner]: the singleton-factor
    specialization of the product sum in Federer 3.2.36, p. 273.
    An actual point has coefficient one in degree zero and zero in
    every positive degree, so its entire inner finite convolution is
    the single Kronecker term. Empty coordinate blocks are retained. *)
Lemma finite_point_convolution_inner (R:realType) n (h:'I_n.+1->\bar R) (g: \bar R) i l:
  h ord0= 1 ->(forall j:'I_n.+1,(0<j)%N ->h j=0) ->
  (\sum_(j:'I_n.+1|(i+j==l)%N) g*h j)=if i==l then g else 0.
Proof.
move=>hZero hPositive.
rewrite big_mkcond (bigD1 ord0) //=.
have hRest:(\sum_(j:'I_n.+1|j!=ord0) (if (i+j==l)%N then g*h j else 0))=0.
  apply:big1=>j hj; case:ifP=>hij; last by [].
  rewrite hPositive ?mule0 //.
  rewrite lt0n; apply/eqP=>hJ.
  have hEq:j=ord0 by apply:val_inj; exact hJ.
  by rewrite hEq eqxx in hj.
by rewrite hRest adde0 hZero addn0 mule1.
Qed.

(** Source for [finite_point_convolution]: the canonical point-product
    consequence of the finite convolution in Federer 3.2.36,
    p. 273. The supplied degree lies in the first factor's range;
    its single surviving coefficient is identified by finite equality
    filtering, with all zero-dimensional endpoint cases retained. *)
Lemma finite_point_convolution (R:realType) m n (g:'I_m.+1->\bar R)
    (h:'I_n.+1->\bar R) (l:'I_m.+1):
  h ord0= 1 ->(forall j:'I_n.+1,(0<j)%N ->h j=0) ->
  (\sum_(i:'I_m.+1) \sum_(j:'I_n.+1|(i+j==l)%N) g i*h j)=g l.
Proof.
move=>hZero hPositive.
under eq_bigr do rewrite (@finite_point_convolution_inner R n h _ _ _ hZero hPositive) val_eqE.
rewrite (bigD1 l) //= eqxx.
have hRest:(\sum_(i:'I_m.+1|i!=l) (if i==l then g i else 0))=0.
  by apply:big1=>i hi; rewrite (negbTE hi).
by rewrite hRest adde0.
Qed.
