(** Federer (1969), 3.4.7, p. 325: original
    first nonzero coefficient orders exist, are unique,
    and add under products. These supporting facts
    expand the comparison with the distinguished power. *)
From mathcomp Require Import all_boot all_order ssralg boolp.
From Federer Require Import CommutativeDomainUP CommutativeDomainCancellation
  CommutativePolynomialUP CommutativePolynomialBasicLaws CommutativePolynomialDegreeUP
  CommutativePolynomialOrderUP NaturalConvolution NaturalConvolutionOrder.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section Order.
Variables A B:comNzRingType.
Variable embed:{rmorphism A->B}.
Variable variable:B.
Variable coefficient:B->nat->A.
Hypothesis hP:is_commutative_polynomial_ring embed variable coefficient.

(** Source for [polynomial_order_exists]: a nonzero
    original polynomial has a first nonzero coefficient,
    supporting the factor comparison in 3.4.7, p. 325. *)
Theorem polynomial_order_exists (P:B):P<>0 ->exists n,is_polynomial_order coefficient P n.
Proof.
move=>hNonzero.
have hExists:exists i,coefficient P i!=0.
  apply:contrapT=>hNone;apply:hNonzero.
  apply/(@polynomial_zero_coefficients A B embed variable coefficient hP)=>i.
  case:(eqVneq (coefficient P i) 0)=>[h|h];first exact:h.
  exfalso;apply:hNone;by exists i.
have [n hn hMinimum]:=ex_minnP hExists.
exists n;split;first by apply/eqP.
move=>i hi;case:(eqVneq (coefficient P i) 0)=>[h|h];first exact:h.
have hBound:=hMinimum i h.
have hContradiction:=leq_ltn_trans hBound hi.
by rewrite ltnn in hContradiction.
Qed.

(** Source for [polynomial_order_unique]: the original
    first nonzero coefficient index is unique,
    supporting 3.4.7, p. 325. *)
Lemma polynomial_order_unique (P:B) m n:
  is_polynomial_order coefficient P m ->is_polynomial_order coefficient P n ->m = n.
Proof.
move=>[hm hM] [hn hN];case:(ltngtP m n)=>[h|h|h];last exact:h.
- exfalso;exact:hm (hN m h).
- exfalso;exact:hn (hM n h).
Qed.

(** Source for [polynomial_order_at_most_degree]: the
    first nonzero coefficient precedes or equals the
    last, supporting the distinguished-factor argument
    in 3.4.7, p. 325. *)
Lemma polynomial_order_at_most_degree (P:B) m n:
  is_polynomial_order coefficient P m ->is_polynomial_degree coefficient P n ->(m<=n)%N.
Proof.
move=>[_ hLower] [hLeading _];case:(leqP m n)=>h;first by [].
exfalso;exact:hLeading (hLower n h).
Qed.

(** Source for [polynomial_variable_power_order]: the
    distinguished original power has exactly its printed
    order, supporting the equation t^k in 3.4.7, p. 325. *)
Lemma polynomial_variable_power_order n:is_polynomial_order coefficient (variable^+n) n.
Proof.
split.
- rewrite (@polynomial_power_coefficient A B embed variable coefficient hP) eqxx.
  by apply/eqP;exact:oner_neq0.
- move=>i hi;rewrite (@polynomial_power_coefficient A B embed variable coefficient hP).
  have hDifferent:(i==n) = false by apply/negP=>/eqP h;by rewrite h ltnn in hi.
  by rewrite hDifferent.
Qed.

(** Source for [polynomial_product_order]: first nonzero
    original coefficient orders add under multiplication
    over a domain, supporting 3.4.7, p. 325. *)
Theorem polynomial_product_order (hDomain:is_commutative_integral_domain A) (P Q:B) m n:
  is_polynomial_order coefficient P m ->is_polynomial_order coefficient Q n ->
  is_polynomial_order coefficient (P*Q) (m+n)%N.
Proof.
move=>[hPm hPLower] [hQn hQLower].
have hConvolution k:coefficient (P*Q) k =
    natural_coefficient_convolution (coefficient P) (coefficient Q) k.
  rewrite (@polynomial_coefficient_multiply A B embed variable coefficient hP).
  by rewrite /natural_coefficient_convolution big_mkord.
split.
- rewrite hConvolution (natural_convolution_initial_coefficient hPLower hQLower).
  exact:(@commutative_domain_product_nonzero A hDomain (coefficient P m) (coefficient Q n) hPm hQn).
- move=>i hi;rewrite hConvolution.
  exact:(@natural_convolution_below_order A (coefficient P) (coefficient Q) m n i hPLower hQLower hi).
Qed.
End Order.
