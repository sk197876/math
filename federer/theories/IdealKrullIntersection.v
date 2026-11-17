(** Supporting algebra for Federer (1969), 3.4.8(5),
    p. 328: every ideal of a Noetherian ring is
    closed for powers of an ideal whose one-minus
    elements are units. The proof uses the project's
    Artin–Rees and finite-generator arguments. Source:
    Bourbaki, Commutative Algebra (1972), Chapter III,
    section 3, no. 2, Proposition 5, p. 200, and
    no. 3, Proposition 6, p. 201. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets.
From Federer Require Import CommutativeIdealUP CommutativeIdealSealed
  CommutativeFactorizationUP CommutativeIdealSumLaws
  CommutativeIdealProductSealed CommutativeIdealProductLaws
  CommutativeIdealPowersSealed CommutativeIdealPowersLaws
  IdealArtinRees FiniteIdealNakayama.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [ideal_krull_intersection_modulo]: the
    intersection of J plus every power of I is J
    under the original Noetherian and unit conditions.
    This is the ideal instance of the cited closedness
    theorem, used to prove actual analytic ideal closedness
    for 3.4.8(5), p. 328. No intersection equality
    or adic closedness is assumed. *)
Theorem ideal_krull_intersection_modulo (A:comNzRingType) (I J:set A)
  (hNoetherian:is_noetherian_commutative_ring A)
  (hI:is_commutative_ideal I) (hJ:is_commutative_ideal J)
  (hUnit:forall a,I a ->is_commutative_unit (1-a)) x:
  (forall k,@GeneratedCommutativeIdeal.value A
    (J `|` @CommutativeIdealPowers.value A I k) x) <->J x.
Proof.
pose P:=@CommutativeIdealPowers.value A I.
pose S:=fun k=>@GeneratedCommutativeIdeal.value A (J `|` P k).
pose N:set A:=fun z=>forall k,S k z.
have hS:forall k,is_commutative_ideal (S k).
  move=>k;exact:(generated_commutative_ideal_laws (@GeneratedCommutativeIdeal.laws A (J `|` P k))).
have hN:is_commutative_ideal N.
  constructor.
  - move=>k;exact:commutative_ideal_zero (hS k).
  - move=>a b ha hb k;exact:(@commutative_ideal_add A (S k) (hS k) a b (ha k) (hb k)).
  - move=>a ha k;exact:(@commutative_ideal_opp A (S k) (hS k) a (ha k)).
  - move=>a b hb k;exact:(@commutative_ideal_mul A (S k) (hS k) a b (hb k)).
have hJN:J `<=` N.
  move=>z hz k;apply:(generated_commutative_ideal_contains (@GeneratedCommutativeIdeal.laws A (J `|` P k))).
  by left.
have [d hArtin]:=@ideal_artin_rees A I N hNoetherian hI hN.
have hDecompose:forall z,N z ->exists j w,J j /\@CommutativeIdealProduct.value A I N w /\z = j+w.
  move=>z hz.
  have [j [w [hj [hw hEquation]]]]:=(@commutative_ideal_sum_membership A J (P d.+1)
    hJ (@commutative_ideal_power_is_ideal A I d.+1) z).1 (hz d.+1).
  have hNw:N w.
    have hMinus:=@commutative_ideal_add A N hN z (-j) hz
      (@commutative_ideal_opp A N hN j (hJN j hj)).
    by rewrite hEquation [j+w]addrC addrK in hMinus.
  have hProduct:@CommutativeIdealProduct.value A I (N `&` P d) w.
    rewrite hArtin //;by split.
  exists j,w;split=>//;split=>//.
  apply:(@commutative_ideal_product_monotone A I (N `&` P d) I N _ _ w hProduct).
  - by move=>a ha.
  - by move=>a [ha _].
have [F hF]:=hNoetherian N hN.
have hWide:is_generated_commutative_ideal (J `|` [set z|z\in F]) N.
  constructor=>//.
  - move=>z [hz|hz];first exact:hJN z hz.
    exact:(@generated_commutative_ideal_contains A [set z|z\in F] N hF z hz).
  - move=>L hL hContains.
    apply:(generated_commutative_ideal_minimal hF hL).
    move=>z hz;apply:hContains;by right.
split;last exact:hJN x.
exact:(@finite_ideal_nakayama_modulo A I J N hI hJ hUnit hDecompose F hWide x).
Qed.
