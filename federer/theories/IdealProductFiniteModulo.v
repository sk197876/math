(** Supporting algebra for Federer (1969), 3.4.8(5),
    p. 328: coefficients in an ideal represent its
    product with a finitely generated ideal, modulo an
    original ideal. This supports the finite-generator
    Nakayama argument in Bourbaki, Commutative Algebra
    (1972), Chapter III, section 3,
    no. 2, Proposition 5, pp. 200–201. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets.
From Federer Require Import CommutativeIdealUP CommutativeIdealProductSealed
  CommutativeIdealProductLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [ideal_product_finite_modulo]: the original
    ideal product has finite coefficients from its first
    factor, modulo the original ideal. This expands the
    supporting Nakayama step cited above; no coefficient
    representation is part of the ideal specification. *)
Lemma ideal_product_finite_modulo (A:comNzRingType) (I J N:set A) (F:seq A)
  (hI:is_commutative_ideal I) (hJ:is_commutative_ideal J)
  (hN:is_generated_commutative_ideal (J `|` [set x|x\in F]) N) x:
  @CommutativeIdealProduct.value A I N x ->
  exists (c:'I_(size F)->A) j,
    (forall i,I (c i)) /\J j /\x = j+\sum_(i<size F) c i*nth 0 F i.
Proof.
pose K:set A:=fun x=>exists (c:'I_(size F)->A) j,
  (forall i,I (c i)) /\J j /\x = j+\sum_(i<size F) c i*nth 0 F i.
have hZeroSum:(\sum_(i<size F) (0:A)*nth 0 F i) = 0 by apply:big1=>i _;exact:mul0r.
have hJK:J `<=` K.
  move=>j hj;exists (fun _=>0),j;split;first by move=>i;exact:(@commutative_ideal_zero A I hI).
  by split=>//;rewrite hZeroSum addr0.
have hK:is_commutative_ideal K.
  constructor.
  - exact:hJK 0 (commutative_ideal_zero hJ).
  - move=>a b [c [j [hc [hj ->]]]] [d [k [hd [hk ->]]]].
    exists (fun i=>c i+d i),(j+k);split.
    + move=>i;exact:(@commutative_ideal_add A I hI (c i) (d i) (hc i) (hd i)).
    + split;first exact:(@commutative_ideal_add A J hJ j k hj hk).
      have hSum:(\sum_(i<size F) (c i+d i)*nth 0 F i) =
        (\sum_(i<size F) c i*nth 0 F i)+(\sum_(i<size F) d i*nth 0 F i).
        rewrite -big_split;apply:eq_bigr=>i _;exact:mulrDl.
      by rewrite hSum addrACA.
  - move=>a [c [j [hc [hj ->]]]];exists (fun i=>-c i),(-j);split.
    + move=>i;exact:(@commutative_ideal_opp A I hI (c i) (hc i)).
    + split;first exact:(@commutative_ideal_opp A J hJ j hj).
      rewrite opprD;congr (_+_);rewrite -sumrN;apply:eq_bigr=>i _;exact:esym (mulNr _ _).
  - move=>u a [c [j [hc [hj ->]]]];exists (fun i=>u*c i),(u*j);split.
    + move=>i;exact:(@commutative_ideal_mul A I hI u (c i) (hc i)).
    + split;first exact:(@commutative_ideal_mul A J hJ u j hj).
      rewrite mulrDr;congr (_+_);rewrite mulr_sumr;apply:eq_bigr=>i _;exact:mulrA.
have hProducts:forall a b,I a ->N b ->K (a*b).
  move=>a b ha hb.
  have hPre:=@commutative_ideal_multiplier_preimage A K a hK.
  apply:(@generated_commutative_ideal_minimal A (J `|` [set x|x\in F]) N hN (fun x=>K (a*x)) hPre _ b hb).
  move=>f [hf|hf].
  - apply:hJK;exact:(@commutative_ideal_mul A J hJ a f hf).
  - have hBound:(index f F<size F)%N by rewrite index_mem.
    pose j:'I_(size F):=Ordinal hBound.
    exists (fun i=>if i==j then a else 0),0;split.
    + move=>i;case:ifP=>_=>//;exact:commutative_ideal_zero hI.
    + split;first exact:commutative_ideal_zero hJ.
      rewrite add0r (bigD1 j) //= eqxx /j /= (nth_index 0 hf).
      have hRest:(\sum_(i<size F|i!=j) (if i==j then a else 0)*nth 0 F i) = 0.
        apply:big1=>i hi;by rewrite (negbTE hi) mul0r.
      by rewrite hRest addr0.
exact:(@commutative_ideal_product_minimal A I N K hK hProducts x).
Qed.
