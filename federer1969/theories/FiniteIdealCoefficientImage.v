(** Federer (1969), 3.4.8(5), p. 328:
    a finitely generated ideal is the image of a
    finite coefficient map. The original least-ideal laws
    precede this representation, which serves only as an
    existence proof for the compact-cover argument. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets.
From Federer Require Import CommutativeIdealUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [finite_ideal_coefficient_image]: the
    finite coefficient map covers exactly the original
    ideal, expanding the continuous-image observation in
    3.4.8(5), p. 328. The generator list may be empty. *)
Theorem finite_ideal_coefficient_image (A:comNzRingType) (I:set A) (F:seq A):
  is_generated_commutative_ideal [set x|x\in F] I ->
  forall x:A,I x <->exists c:'I_(size F)->A,
    x = \sum_(i<size F) c i*nth 0 F i.
Proof.
move=>hI.
pose J:set A:=fun x=>exists c:'I_(size F)->A,x = \sum_(i<size F) c i*nth 0 F i.
have hJ:is_commutative_ideal J.
  constructor.
  - exists (fun _=>0);symmetry;apply:big1=>i _;exact:mul0r.
  - move=>x y [c ->] [d ->];exists (fun i=>c i+d i).
    rewrite -big_split;apply:eq_bigr=>i _;exact:esym (mulrDl _ _ _).
  - move=>x [c ->];exists (fun i=>-c i).
    rewrite -sumrN;apply:eq_bigr=>i _;exact:esym (mulNr _ _).
  - move=>a x [c ->];exists (fun i=>a*c i).
    rewrite mulr_sumr;apply:eq_bigr=>i _;exact:(mulrA _ _ _).
have hGenerators:[set x|x\in F] `<=` J.
  move=>x hx.
  have hBound:(index x F<size F)%N by rewrite index_mem.
  pose j:'I_(size F):=Ordinal hBound.
  exists (fun i=>if i==j then 1 else 0).
  rewrite (bigD1 j) //= eqxx mul1r /j /= (nth_index 0 hx).
  have hRest:(\sum_(i<size F|i!=j) (if i==j then (1:A) else 0)*nth 0 F i) = 0.
    apply:big1=>i hi;by rewrite (negbTE hi) mul0r.
  by rewrite hRest addr0.
move=>x;split;first exact:(@generated_commutative_ideal_minimal A [set z|z\in F] I hI J hJ hGenerators x).
move=>[c ->];apply:(big_ind I).
- exact:commutative_ideal_zero (generated_commutative_ideal_laws hI).
- move=>a b ha hb;exact:(commutative_ideal_add (generated_commutative_ideal_laws hI) ha hb).
- move=>i _;apply:(commutative_ideal_mul (generated_commutative_ideal_laws hI)).
  apply:(generated_commutative_ideal_contains hI).
  exact:(mem_nth 0 (ltn_ord i)).
Qed.
