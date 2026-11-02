(** Federer (1969), 1.10.4, p. 46: uniqueness of the coefficient forms,
    deduced by restricting a polynomial to t*x. It uses Horner evaluation
    and synthetic division, without importing a polynomial root-counting
    theorem. *)
From mathcomp Require Import all_boot all_order all_algebra.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section Coefficients.
Variable K : fieldType.
Variable W : lmodType K.

(** Source for [coefficient_polynomial_value]: Federer 1.10.4,
    p. 46, the expansion of P(t*x) in scalar powers of t. Supporting
    Horner evaluation of a finite list of vector coefficients. *)
Definition coefficient_polynomial_value (s : seq W) (x : K) :=
  foldr (fun c y => c + x *: y) 0 s.

(** Source for [coefficient_quotient_tail]: Federer 1.10.4,
    p. 46, supporting synthetic-division coefficient list. Each entry
    is the Horner value at a of the remaining tail. *)
Fixpoint coefficient_quotient_tail (s : seq W) (a : K) : seq W :=
  if s is c::t then coefficient_polynomial_value s a :: coefficient_quotient_tail t a
  else [::].

(** Source for [coefficient_quotient]: Federer 1.10.4, p. 46,
    supporting synthetic quotient of P(x)-P(a) by x-a. *)
Definition coefficient_quotient s a := coefficient_quotient_tail (behead s) a.

(** Source for [coefficient_quotient_size]: Federer 1.10.4,
    p. 46, supporting degree descent: the quotient has one fewer
    coefficient than a nonempty polynomial list. *)
Lemma coefficient_quotient_size s a : size (coefficient_quotient s a) = (size s).-1.
Proof.
rewrite /coefficient_quotient.
have h t : size (coefficient_quotient_tail t a) = size t.
  by elim: t=> [|c t ih] //=; rewrite ih.
by rewrite h size_behead.
Qed.

(** Source for [coefficient_synthetic_step]: Federer 1.10.4,
    p. 46, supporting scalar identity in the local synthetic-division
    proof of uniqueness of the polynomial coefficients. *)
Lemma coefficient_synthetic_step (a x : K) (u v : W) :
  x *: (u + (x-a) *: v) = a *: u + (x-a) *: (u+x *: v).
Proof.
rewrite !scalerDr !scalerA [x*(x-a)]mulrC addrA -scalerDl.
by rewrite [a+(x-a)]addrC subrK.
Qed.

(** Source for [coefficient_synthetic_identity]: Federer 1.10.4,
    p. 46, supporting algebraic identity P(x)=P(a)+(x-a)Q(x).
    This proves the root-count induction for vector coefficients. *)
Lemma coefficient_synthetic_identity s a x :
  coefficient_polynomial_value s x = coefficient_polynomial_value s a +
    (x-a) *: coefficient_polynomial_value (coefficient_quotient s a) x.
Proof.
elim: s=> [|c s ih]; first by rewrite /coefficient_polynomial_value /= scaler0 addr0.
case: s ih=> [|d t] ih.
- by rewrite /coefficient_polynomial_value /coefficient_quotient /= !scaler0 !addr0.
- change (c + x *: coefficient_polynomial_value (d::t) x =
    (c + a *: coefficient_polynomial_value (d::t) a) +
    (x-a) *: (coefficient_polynomial_value (d::t) a +
      x *: coefficient_polynomial_value (coefficient_quotient (d::t) a) x)).
  rewrite {1}ih -[RHS]addrA.
  congr (c + _); exact: coefficient_synthetic_step.
Qed.

(** Source for [coefficient_quotient_zero]: Federer 1.10.4,
    p. 46, supporting reverse synthetic division: if the quotient
    and the value at a vanish, every coefficient vanishes. *)
Lemma coefficient_quotient_zero s a :
  all (pred1 0) (coefficient_quotient s a) -> coefficient_polynomial_value s a = 0 ->
  all (pred1 0) s.
Proof.
elim: s=> [|c s ih] //.
case: s ih=> [|d t] ih.
- rewrite /coefficient_polynomial_value /= scaler0 addr0; move=> _ ->.
  by rewrite /= eqxx.
- change ((coefficient_polynomial_value (d::t) a == 0) &&
    all (pred1 0) (coefficient_quotient (d::t) a) ->
    c + a *: coefficient_polynomial_value (d::t) a = 0 ->
    (c == 0) && all (pred1 0) (d::t)).
  move/andP=> [/eqP ht hq].
  rewrite ht scaler0 addr0=> ->.
  rewrite eqxx /=; exact: ih hq ht.
Qed.

(** Source for [coefficient_polynomial_roots]: Federer 1.10.4,
    p. 46, supporting root-count theorem: a list of at most N
    coefficients vanishes if its polynomial vanishes on N distinct scalars.
    The coefficient space may have arbitrary dimension. *)
Theorem coefficient_polynomial_roots (N : nat) (s : seq W) (r : seq K) :
  (size s <= N)%N -> size r = N -> uniq r ->
  (forall x, x \in r -> coefficient_polynomial_value s x = 0) -> all (pred1 0) s.
Proof.
elim: N s r=> [s r hs hr hu hz|N ih s r hs hr hu hz].
- have hs0 : s=[::].
    apply/eqP; rewrite -size_eq0 -leqn0; exact: hs.
  by rewrite hs0.
- case: r hr hu hz=> [//|a r] /= hr /andP [har hur] hz.
  have hpa : coefficient_polynomial_value s a = 0 := hz a (mem_head _ _).
  have hqs : (size (coefficient_quotient s a) <= N)%N.
    rewrite coefficient_quotient_size; by case: (size s) hs=> [|k].
  have hqr : forall x, x \in r -> coefficient_polynomial_value (coefficient_quotient s a) x = 0.
    move=> x hx.
    have hxa : x != a.
      apply/eqP=> hxa; move: har; by rewrite -hxa hx.
    have hxr : x \in a::r by rewrite in_cons hx orbT.
    have h := coefficient_synthetic_identity s a x.
    rewrite (hz x hxr) hpa add0r in h.
    move/eqP: (esym h); rewrite scaler_eq0 subr_eq0 (negbTE hxa) /=.
    exact: eqP.
  apply: coefficient_quotient_zero hpa.
  exact: ih hqs (congr1 predn hr) hur hqr.
Qed.
End Coefficients.

(** Source for [characteristic_zero_nat_injective]: Federer
    1.10.4, p. 46, supporting existence of enough distinct scalar
    evaluation points. In characteristic zero, distinct natural numbers
    give distinct scalars. *)
Lemma characteristic_zero_nat_injective (K : fieldType) (h0 : [pchar K] =i pred0) :
  injective (fun n : nat => (n%:R : K)).
Proof.
move/pcharf0P: h0=> hnat.
have ordered m n : (m<=n)%N -> (m%:R : K)=n%:R -> m=n.
  move=> hmn he.
  have hz : ((n-m)%:R : K)=0 by rewrite natrB // -he subrr.
  have hnm : (n<=m)%N.
    move/eqP: hz; by rewrite hnat subn_eq0.
  apply/eqP; by rewrite eqn_leq hmn hnm.
move=> m n he; case: (leqP m n)=> hmn.
- exact: ordered hmn he.
- symmetry; exact: ordered (ltnW hmn) (esym he).
Qed.

(** Source for [coefficient_polynomial_zero]: Federer 1.10.4,
    p. 46, uniqueness of the vector coefficients of P(t*x).
    If a finite vector-valued polynomial vanishes for every scalar t,
    every coefficient is zero. The proof uses distinct natural scalars
    and the preceding local root-count induction. *)
Theorem coefficient_polynomial_zero (K : fieldType) (h0 : [pchar K] =i pred0)
    (W : lmodType K) (s : seq W) :
  (forall t, coefficient_polynomial_value s t = 0) -> all (pred1 0) s.
Proof.
move=> hs.
pose r := [seq (i%:R : K) | i <- iota 0 (size s)].
apply: (@coefficient_polynomial_roots K W (size s) s r) => //.
- by rewrite /r size_map size_iota.
- by rewrite /r (map_inj_uniq (characteristic_zero_nat_injective h0)) iota_uniq.
Qed.

(** Source for [coefficient_polynomial_sum]: Federer 1.10.4,
    p. 46, supporting equality between Horner evaluation and
    the printed sum of scalar powers times vector coefficients. *)
Lemma coefficient_polynomial_sum (K : fieldType) (W : lmodType K) (s : seq W) t :
  coefficient_polynomial_value s t = \sum_(i < size s) t^+i *: nth 0 s i.
Proof.
elim: s=> [|c s ih]; first by rewrite big_ord0.
rewrite big_ord_recl /= expr0 scale1r.
change (c + t *: coefficient_polynomial_value s t =
  c + \sum_(i < size s) t^+i.+1 *: nth 0 s i).
rewrite ih scaler_sumr.
congr (c + _); apply: eq_bigr=> i _.
by rewrite exprS scalerA.
Qed.

(** Source for [finite_power_coefficients_zero]: Federer 1.10.4,
    p. 46, the coefficient uniqueness used after evaluating at t*x,
    in the same finite-sum notation as the book. *)
Theorem finite_power_coefficients_zero (K : fieldType) (h0 : [pchar K] =i pred0)
    (W : lmodType K) N (c : nat -> W) :
  (forall t, \sum_(i < N) t^+i *: c i = 0) ->
  forall i, (i<N)%N -> c i = 0.
Proof.
move=> hz.
pose s := [seq c i | i <- iota 0 N].
have hs : forall t, coefficient_polynomial_value s t = 0.
  move=> t; rewrite coefficient_polynomial_sum /s size_map size_iota.
  rewrite -[RHS](hz t); apply: eq_bigr=> i _.
  by rewrite (nth_map 0) ?size_iota ?ltn_ord // nth_iota ?ltn_ord // add0n.
have /allP ha := coefficient_polynomial_zero h0 hs.
move=> i hi; apply/eqP; apply: ha.
apply/mapP; exists i=> //.
by rewrite mem_iota add0n leq0n hi.
Qed.
