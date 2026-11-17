(** Supporting algebra for Federer (1969), 3.4.8(5),
    p. 328: sums of ideals use the existing opaque
    least-ideal interface. The membership formula supports
    the expanded ideal-closedness argument. Source:
    Bourbaki, Commutative Algebra (1972), Chapter III,
    section 3, no. 2, Proposition 5, pp. 200–201. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets.
From Federer Require Import CommutativeIdealUP CommutativeIdealSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [commutative_ideal_sum_membership]: an
    element of the sum of two ideals is a sum
    of their elements, supporting the cited intersection
    theorem and Federer 3.4.8(5), p. 328. *)
Lemma commutative_ideal_sum_membership (A:comNzRingType) (I J:set A)
  (hI:is_commutative_ideal I) (hJ:is_commutative_ideal J) t:
  @GeneratedCommutativeIdeal.value A (I `|` J) t <->
    exists a b,I a /\J b /\t = a+b.
Proof.
pose S:set A:=fun x=>exists a b,I a /\J b /\x = a+b.
have hS:is_commutative_ideal S.
  constructor.
  - exists 0,0;split;first exact:commutative_ideal_zero hI.
    split;first exact:commutative_ideal_zero hJ.
    by rewrite addr0.
  - move=>x y [a [b [ha [hb ->]]]] [c [d [hc [hd ->]]]].
    exists (a+c),(b+d);split;first exact:(@commutative_ideal_add A I hI a c ha hc).
    split;first exact:(@commutative_ideal_add A J hJ b d hb hd).
    exact:addrACA.
  - move=>x [a [b [ha [hb ->]]]];exists (-a),(-b);split.
    + exact:(@commutative_ideal_opp A I hI a ha).
    + split;first exact:(@commutative_ideal_opp A J hJ b hb).
      exact:opprD.
  - move=>u x [a [b [ha [hb ->]]]];exists (u*a),(u*b);split.
    + exact:(@commutative_ideal_mul A I hI u a ha).
    + split;first exact:(@commutative_ideal_mul A J hJ u b hb).
      exact:mulrDr.
have hContains:I `|` J `<=` S.
  move=>x [hx|hx].
  - exists x,0;split=>//;split;first exact:commutative_ideal_zero hJ.
    by rewrite addr0.
  - exists 0,x;split;first exact:commutative_ideal_zero hI.
    by split=>//;rewrite add0r.
split;first exact:(@generated_commutative_ideal_minimal A (I `|` J) (@GeneratedCommutativeIdeal.value A (I `|` J)) (@GeneratedCommutativeIdeal.laws A (I `|` J)) S hS hContains t).
move=>[a [b [ha [hb ->]]]].
have hL:=@GeneratedCommutativeIdeal.laws A (I `|` J).
apply:(commutative_ideal_add (generated_commutative_ideal_laws hL)).
- apply:(generated_commutative_ideal_contains hL);by left.
- apply:(generated_commutative_ideal_contains hL);by right.
Qed.
