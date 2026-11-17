(** Federer (1969), 3.4.7, p. 325: the coefficient
    argument for Gauss's primitive-product lemma. No quotient-ring
    primality or polynomial factorization theorem is assumed. *)
From mathcomp Require Import all_boot all_order ssralg boolp.
From Federer Require Import CommutativeFactorizationUP CommutativeDivisibility
  CommutativeDivisibilitySums NaturalConvolution.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [prime_convolution_first_coefficient]: the
    convolution coefficient at the sum of the first
    nondivisible indices is not divisible by the original
    prime, supporting the Gauss lemma in 3.4.7, p. 325. *)
Theorem prime_convolution_first_coefficient (A:comNzRingType) (p:A)
    (f g:nat->A) i j:
  is_commutative_prime_element p ->
  (~commutative_divides p (f i)) ->(~commutative_divides p (g j)) ->
  (forall h,(h<i)%N ->commutative_divides p (f h)) ->
  (forall h,(h<j)%N ->commutative_divides p (g h)) ->
  ~commutative_divides p (natural_coefficient_convolution f g (i+j)%N).
Proof.
move=>hPrime hF hG hFLower hGLower hTotal.
have hi:(i<(i+j).+1)%N by rewrite ltnS leq_addr.
pose index:'I_(i+j).+1:=Ordinal hi.
have hRemainder:commutative_divides p
    (\sum_(h<(i+j).+1|h!=index) f h*g (i+j-h)%N).
  apply:commutative_divides_finite_sum=>h _ hDifferent.
  case:(ltngtP (h:nat) i)=>[hH|hH|hH].
  - rewrite mulrC;apply:commutative_divides_multiply;exact:hFLower h hH.
  - have hBound:(h<=i+j)%N by have:=ltn_ord h;rewrite ltnS.
    have hSmall:(i+j-h<j)%N by rewrite (@ltn_subLR (i+j)%N h j hBound) ltn_add2r.
    apply:commutative_divides_multiply;exact:hGLower _ hSmall.
  - move:hDifferent;by rewrite -val_eqE /= hH eqxx.
rewrite /natural_coefficient_convolution big_mkord (bigD1 index) //= addKn in hTotal.
have hMain:=commutative_divides_sum_remainder hTotal hRemainder.
exact:(@commutative_prime_product_not_divisible A p (f i) (g j) hPrime hF hG hMain).
Qed.
