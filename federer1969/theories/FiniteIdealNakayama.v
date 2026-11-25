(** Supporting algebra for Federer (1969), 3.4.8(5),
    p. 328: a finite-generator Nakayama argument modulo
    an original ideal. The proof removes one generator
    at a time using an actual inverse of one minus
    its coefficient. Source: the finite-module step in
    Bourbaki, Commutative Algebra (1972), Chapter III,
    section 3, no. 2, Proposition 5, p. 200.
    No quotient ring or determinant theorem is imported. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets.
From Federer Require Import CommutativeIdealUP CommutativeIdealSealed
  CommutativeFactorizationUP CommutativeIdealProductSealed
  IdealProductFiniteModulo.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [finite_ideal_nakayama_modulo]: a finitely
    generated ideal N with N contained in J+IN lies
    in J when every one minus an element of I
    is a unit. This proves the finite-module step
    needed for the cited intersection theorem, supporting
    3.4.8(5), p. 328. The original J and N remain. *)
Theorem finite_ideal_nakayama_modulo (A:comNzRingType) (I J N:set A)
  (hI:is_commutative_ideal I) (hJ:is_commutative_ideal J)
  (hUnit:forall a,I a ->is_commutative_unit (1-a))
  (hDecompose:forall x,N x ->exists j z,J j /\
    @CommutativeIdealProduct.value A I N z /\x = j+z):
  forall F:seq A,is_generated_commutative_ideal (J `|` [set x|x\in F]) N ->N `<=` J.
Proof.
elim=>[|t F ih] hN.
- apply:(generated_commutative_ideal_minimal hN hJ).
  move=>x [hx|hx]=>//;by rewrite in_nil in hx.
- pose K:=@GeneratedCommutativeIdeal.value A (J `|` [set x|x\in F]).
  have hK:=@GeneratedCommutativeIdeal.laws A (J `|` [set x|x\in F]).
  have hKIdeal:=generated_commutative_ideal_laws hK.
  have hJK:J `<=` K.
    move=>x hx;apply:(generated_commutative_ideal_contains hK);by left.
  have hTail:forall x,x\in F ->K x.
    move=>x hx;apply:(generated_commutative_ideal_contains hK);by right.
  have ht:N t.
    apply:(generated_commutative_ideal_contains hN);right;change (is_true (t\in t::F));by rewrite in_cons eqxx.
  have [j [z [hj [hz htz]]]]:=hDecompose t ht.
  have [c [j2 [hc [hj2 hzc]]]]:=@ideal_product_finite_modulo A I J N (t::F) hI hJ hN z hz.
  pose S:=\sum_(i<size F) c (lift ord0 i)*nth 0 F i.
  have hEquation:t = (j+j2)+(c ord0*t+S).
    rewrite {1}htz hzc big_ord_recl /= /S addrA;reflexivity.
  have hKS:K S.
    apply:(big_ind K).
    + exact:commutative_ideal_zero hKIdeal.
    + move=>a b ha hb;exact:(@commutative_ideal_add A K hKIdeal a b ha hb).
    + move=>i _;apply:(@commutative_ideal_mul A K hKIdeal (c (lift ord0 i)) (nth 0 F i)).
      exact:hTail _ (mem_nth 0 (ltn_ord i)).
  have hScaled:K ((1-c ord0)*t).
    have hIdentity:(1-c ord0)*t = (j+j2)+S.
      rewrite mulrBl mul1r {1}hEquation [c ord0*t+S]addrC addrA addrK.
      reflexivity.
    rewrite hIdentity;apply:(@commutative_ideal_add A K hKIdeal (j+j2) S _ hKS).
    apply:hJK;exact:(@commutative_ideal_add A J hJ j j2 hj hj2).
  have [u hu]:=hUnit (c ord0) (hc ord0).
  have hKt:K t.
    have hProduct:=@commutative_ideal_mul A K hKIdeal u ((1-c ord0)*t) hScaled.
    by rewrite mulrA hu mul1r in hProduct.
  have hNInK:N `<=` K.
    apply:(generated_commutative_ideal_minimal hN hKIdeal).
    move=>x [hx|hx];first exact:hJK x hx.
    change (is_true (x\in t::F)) in hx.
    move:hx;rewrite in_cons;move/orP=>[/eqP ->|hx];first exact:hKt.
    exact:hTail x hx.
  have hNew:is_generated_commutative_ideal (J `|` [set x|x\in F]) N.
    constructor.
    + exact:generated_commutative_ideal_laws hN.
    + move=>x [hx|hx];apply:(generated_commutative_ideal_contains hN).
      * by left.
      * right;change (is_true (x\in t::F));by rewrite in_cons hx orbT.
    + move=>L hL hContains x hx.
      apply:(@generated_commutative_ideal_minimal A (J `|` [set x|x\in F]) K hK L hL hContains x).
      exact:hNInK x hx.
  exact:ih hNew.
Qed.
