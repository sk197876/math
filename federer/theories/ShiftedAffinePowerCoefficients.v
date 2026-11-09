(** Federer (1969), 3.4.5, p. 321: actual
    finite coefficients of the powers occurring in the
    quadratic substitution, supporting the real counterexample proof. *)
From mathcomp Require Import all_boot all_order all_algebra ring.
From Federer Require Import FiniteHornerCoefficientEquality.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section Coefficients.
Variable K:fieldType.

(** Source for [shifted_affine_power_coefficient]: the
    coefficient of x^n in x^j*(-1+lambda*x)^m,
    supporting the finite quadratic remainder in
    3.4.5, p. 321. Only finite sums occur. *)
Definition shifted_affine_power_coefficient (j m:nat) (lambda:K) (n:nat):K:=
  \sum_(ell<m.+1 | (j+ell==n)%N) ('C(m,ell))%:R*(-1)^+(m-ell)*lambda^+ell.

(** Source for [shifted_affine_power_coefficient_above]: coefficients
    above the original finite degree vanish, supporting
    3.4.5, p. 321. *)
Lemma shifted_affine_power_coefficient_above j m lambda n:
  (j+m<n)%N ->shifted_affine_power_coefficient j m lambda n=0.
Proof.
move=>hN;rewrite /shifted_affine_power_coefficient;apply:big1=>ell /eqP hEqual.
have hLe:(j+ell<=j+m)%N by rewrite leq_add2l;have:=ltn_ord ell;rewrite ltnS.
have hImpossible:=leq_ltn_trans hLe hN;by rewrite hEqual ltnn in hImpossible.
Qed.

(** Source for [shifted_affine_power_coefficient_below]: coefficients
    below the original leading power vanish, supporting
    3.4.5, p. 321. *)
Lemma shifted_affine_power_coefficient_below j m lambda n:
  (n<j)%N ->shifted_affine_power_coefficient j m lambda n=0.
Proof.
move=>hN;rewrite /shifted_affine_power_coefficient;apply:big1=>ell /eqP hEqual.
have hLe:(j<=j+ell)%N:=leq_addr ell j.
have hImpossible:=leq_trans hN hLe;by rewrite hEqual ltnn in hImpossible.
Qed.

(** Source for [shifted_affine_power_expansion]: the original
    finite binomial coefficients give the actual polynomial
    on every scalar input, supporting 3.4.5, p. 321. *)
Theorem shifted_affine_power_expansion j m lambda L (x:K):
  (j+m<L)%N ->
  \sum_(n<L) shifted_affine_power_coefficient j m lambda n*x^+n=
    x^+j*(-1+lambda*x)^+m.
Proof.
move=>hL;rewrite /shifted_affine_power_coefficient.
have hExpand:(\sum_(n<L) (\sum_(ell<m.+1 | (j+ell==n)%N)
    ('C(m,ell))%:R*(-1)^+(m-ell)*lambda^+ell)*x^+n)=
    \sum_(ell<m.+1) (('C(m,ell))%:R*(-1)^+(m-ell)*lambda^+ell)*x^+(j+ell).
  under eq_bigr do rewrite mulr_suml big_mkcond.
  rewrite exchange_big;apply:eq_bigr=>ell _.
  have hDegree:(j+ell<L)%N.
    apply:leq_ltn_trans _ hL;rewrite leq_add2l;by have:=ltn_ord ell;rewrite ltnS.
  pose q:'I_L:=Ordinal hDegree.
  rewrite (bigD1 q) //= eqxx.
  have hOthers:(\sum_(n<L | n!=q) if (j+ell==n)%N then
      (('C(m,ell))%:R*(-1)^+(m-ell)*lambda^+ell)*x^+n else 0)=0.
    apply:big1=>n hDifferent.
    have hNe:(j+ell!=n)%N by move:hDifferent;rewrite -val_eqE /q /= eq_sym.
    by rewrite (negbTE hNe).
  by rewrite hOthers addr0.
rewrite hExpand exprDn mulr_sumr.
apply:eq_bigr=>ell _;rewrite exprD exprMn;ring.
Qed.

(** Source for [shifted_affine_power_coefficient_successor]:
    multiplying by the original affine factor gives the
    exact coefficient recurrence, supporting 3.4.5, p. 321.
    The proof compares actual polynomials by the internal
    coefficient uniqueness theorem of 1.10.4, p. 46. *)
Theorem shifted_affine_power_coefficient_successor (h0:[pchar K]=i pred0) j m lambda n:
  shifted_affine_power_coefficient j m.+1 lambda n=
    lambda*shifted_affine_power_coefficient j.+1 m lambda n-
    shifted_affine_power_coefficient j m lambda n.
Proof.
pose d:=(j+m).+1.
pose L:=(maxn n d).+1.
have hDL:(d<L)%N by rewrite /L ltnS;exact:leq_maxr.
have hFirst:(j+m.+1<L)%N by rewrite addnS;exact:hDL.
have hSecond:(j+m<L)%N:=leq_ltn_trans (leqnSn _) hDL.
have hThird:(j.+1+m<L)%N by rewrite addSn;exact:hDL.
have hN:(n<L)%N by rewrite /L ltnS;exact:leq_maxl.
have hValues (x:K):
    (\sum_(i<L) x^+i*:(shifted_affine_power_coefficient j m.+1 lambda i:K^o))=
    \sum_(i<L) x^+i*:((lambda*shifted_affine_power_coefficient j.+1 m lambda i-
      shifted_affine_power_coefficient j m lambda i):K^o).
  have hSum (a:nat->K):(\sum_(i<L) x^+i*:(a i:K^o))=\sum_(i<L) a i*x^+i.
    apply:eq_bigr=>i _;change (x^+i*a i=a i*x^+i);exact:mulrC.
  rewrite (hSum (fun i=>shifted_affine_power_coefficient j m.+1 lambda i))
    (hSum (fun i=>lambda*shifted_affine_power_coefficient j.+1 m lambda i-
      shifted_affine_power_coefficient j m lambda i)).
  have hRight:(\sum_(i<L) (lambda*shifted_affine_power_coefficient j.+1 m lambda i-
      shifted_affine_power_coefficient j m lambda i)*x^+i)=
      lambda*(\sum_(i<L) shifted_affine_power_coefficient j.+1 m lambda i*x^+i)-
      \sum_(i<L) shifted_affine_power_coefficient j m lambda i*x^+i.
    under eq_bigr do rewrite mulrBl -mulrA.
    by rewrite sumrB -mulr_sumr.
  rewrite hRight (@shifted_affine_power_expansion j m.+1 lambda L x hFirst)
    (@shifted_affine_power_expansion j m lambda L x hSecond) (@shifted_affine_power_expansion j.+1 m lambda L x hThird) !exprS.
  ring.
exact:(@finite_power_coefficients_equal K h0 K^o L
  (fun i=>shifted_affine_power_coefficient j m.+1 lambda i)
  (fun i=>lambda*shifted_affine_power_coefficient j.+1 m lambda i-
    shifted_affine_power_coefficient j m lambda i) hValues n hN).
Qed.
End Coefficients.
