(** Supporting algebra for Federer (1969), 3.4.8(5), p. 328.
    Reuse the proved ideal Artin--Rees theorem to control the
    filtration shift under multiplication by a nonzero original
    coefficient. No Taylor-product-order theorem is assumed or redone. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets.
From Federer Require Import CommutativeIdealUP CommutativeDomainUP CommutativeDomainCancellation
  CommutativeIdealProductSealed CommutativeIdealProductLaws
  CommutativeIdealPowersSealed CommutativeIdealPowersLaws IdealArtinRees.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [nonzero_principal_adic_shift]: supporting coefficient
    filtration comparison for the auxiliary sentence in Federer
    3.4.8(5), p. 328. For an original nonzero scalar delta there is
    one finite shift r such that delta*a in I^(r+l) implies a in I^l.
    The original Noetherian and domain laws suffice. *)
Theorem nonzero_principal_adic_shift (A:comNzRingType) (I:set A) (delta:A):
  is_noetherian_commutative_ring A ->is_commutative_integral_domain A ->
  is_commutative_ideal I ->delta<>0 ->
  exists r,forall l a,@CommutativeIdealPowers.value A I (r+l)%N (delta*a) ->
    @CommutativeIdealPowers.value A I l a.
Proof.
move=>hNoetherian hDomain hI hDelta.
pose P:=@CommutativeIdealPowers.value A I.
pose T (j:nat):set A:=fun z=>exists a:A,P j a /\z = delta*a.
have hT j:is_commutative_ideal (T j).
  constructor.
  - exists 0;split;first exact:commutative_ideal_zero (commutative_ideal_power_is_ideal I j).
    by rewrite mulr0.
  - move=>x y [a [ha ->]] [b [hb ->]];exists (a+b);split.
    + exact:(@commutative_ideal_add A (P j) (commutative_ideal_power_is_ideal I j) a b ha hb).
    + exact:esym (mulrDr delta a b).
  - move=>x [a [ha ->]];exists (-a);split.
    + exact:(@commutative_ideal_opp A (P j) (commutative_ideal_power_is_ideal I j) a ha).
    + exact:esym (mulrN delta a).
  - move=>x y [a [ha ->]];exists (x*a);split.
    + exact:(@commutative_ideal_mul A (P j) (commutative_ideal_power_is_ideal I j) x a ha).
    + exact:mulrCA x delta a.
have [r hArtin]:=@ideal_artin_rees A I (T 0%N) hNoetherian hI (hT 0%N).
have hFiltered l:(T 0%N `&` P (r+l)%N) `<=` T l.
  elim:l=>[|l ih];first by move=>z [hz _].
  rewrite addnS -(@hArtin (r+l)%N (leq_addr l r)).
  apply:commutative_ideal_product_minimal;first exact:hT l.+1.
  move=>a b ha hb;have [c [hc hB]]:=ih b hb.
  exists (a*c);split.
  - rewrite /P commutative_ideal_power_successorE.
    exact:(@commutative_ideal_product_contains A I (P l) a c ha hc).
  - by rewrite hB mulrCA.
exists r=>l a hA.
have hMember:T 0%N (delta*a).
  exists a;split=>//;by rewrite /P commutative_ideal_power_zeroE.
have [b [hB hEquation]]:=hFiltered l (delta*a) (conj hMember hA).
have hEqual:a = b:=@commutative_domain_cancel_left A hDomain delta a b hDelta hEquation.
by rewrite hEqual.
Qed.
