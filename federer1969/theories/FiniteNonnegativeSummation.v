(** Federer (1969), 2.1.1, p. 52, paragraph preceding (1) and properties
    (1)-(2): existence and uniqueness of finite nonnegative summation.
    Source context: NonnegativeSumUP.v. Finite domains are represented by
    finite types, including the empty type. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(** Source for [is_finite_nonnegative_summation]: Federer
    2.1.1(1)-(2), p. 52; zero, single-support and additivity laws
    on a finite domain. The zero law includes the empty domain. *)
Record is_finite_nonnegative_summation (R : realType) (I : finType)
    (S : (I -> \bar R) -> \bar R) : Prop := {
  finite_summation_zero : forall f, (forall x, f x = 0) -> S f = 0;
  finite_summation_single : forall f a, 0 <= f a ->
    (forall x, x != a -> f x = 0) -> S f = f a;
  finite_summation_add : forall f g, (forall x, 0 <= f x) ->
    (forall x, 0 <= g x) -> S (fun x => f x+g x) = S f+S g
}.

(** Source for [finite_nonnegative_summation_exists]: Federer
    2.1.1, p. 52, paragraph before (1); ordinary finite addition
    supplies a witness to the abstract finite summation laws. *)
Lemma finite_nonnegative_summation_exists (R : realType) (I : finType) :
  is_finite_nonnegative_summation (fun f : I -> \bar R => \sum_x f x).
Proof.
constructor.
- move=> f hf; by apply: big1=> x _; exact: hf.
- move=> f a ha hz; rewrite (bigD1 a) //=.
  have he : (\sum_(x | x != a) f x) = 0 by apply: big1=> x hx; exact: hz.
  by rewrite he adde0.
- move=> f g hf hg; exact: big_split.
Qed.

(** Source for [finite_summation_sequence]: Federer 2.1.1(2),
    p. 52; supporting finite iteration of the additivity law. *)
Lemma finite_summation_sequence (R : realType) (I : finType)
    (S : (I -> \bar R) -> \bar R) (hS : is_finite_nonnegative_summation S)
    (J : eqType) (s : seq J) (F : J -> I -> \bar R) :
  (forall j, j \in s -> forall x, 0 <= F j x) ->
  S (fun x => \sum_(j <- s) F j x) = \sum_(j <- s) S (F j).
Proof.
elim: s=> [|j s ih] hF.
- rewrite big_nil; apply: (@finite_summation_zero R I S hS) => x; exact: big_nil.
- have hj : forall x, 0 <= F j x by apply: hF; rewrite in_cons eqxx.
  have hs : forall k, k \in s -> forall x, 0 <= F k x.
    move=> k hk; apply: hF; by rewrite in_cons hk orbT.
  have he : (fun x => \sum_(k <- j::s) F k x) =
      (fun x => F j x + \sum_(k <- s) F k x).
    by apply: funext=> x; rewrite big_cons.
  rewrite he big_cons (finite_summation_add hS) //.
  + by rewrite ih.
  + move=> x; rewrite big_seq; apply: sume_ge0=> k hk; exact: (hs k hk x).
Qed.

(** Source for [finite_nonnegative_summation_unique]: Federer 2.1.1, p. 52,
    paragraph before (1); every operator satisfying the laws agrees with
    finite summation on every nonnegative function. *)
Theorem finite_nonnegative_summation_unique (R : realType) (I : finType)
    (S : (I -> \bar R) -> \bar R) (hS : is_finite_nonnegative_summation S)
    (f : I -> \bar R) : (forall x, 0 <= f x) -> S f = \sum_x f x.
Proof.
move=> hf; pose F j x := if j == x then f j else 0.
have he : f = (fun x => \sum_(j <- enum I) F j x).
  apply: funext=> x; rewrite big_enum /F -big_mkcond big_pred1_eq; by [].
have hF : forall j, j \in enum I -> forall x, 0 <= F j x.
  move=> j _ x; rewrite /F; case: ifP=> _; [exact: hf | exact: lexx].
rewrite {1}he (finite_summation_sequence hS hF) big_enum.
apply: eq_bigr=> j _.
have h := @finite_summation_single R I S hS (F j) j.
rewrite /F eqxx in h; apply: h (hf j) _ => x hx; by rewrite eq_sym (negbTE hx).
Qed.
