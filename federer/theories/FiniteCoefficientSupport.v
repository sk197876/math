(** Federer (1969), 3.4.7, p. 325: finite support
    supplies a concrete existence witness for the independently
    specified polynomial algebra. Later proofs use its sealed laws. *)
From mathcomp Require Import all_boot all_order ssralg boolp.
From Federer Require Import NaturalConvolution.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [has_finite_coefficient_support]: the finite
    coefficient condition for the polynomial expressions in
    3.4.7, p. 325; this is construction infrastructure. *)
Definition has_finite_coefficient_support (A:comNzRingType) (f:nat->A):Prop:=
  exists N,forall i,(N<=i)%N ->f i = 0.

(** Source for [finite_coefficient_zero_support]: the zero
    expression has finite support, supporting 3.4.7, p. 325. *)
Lemma finite_coefficient_zero_support (A:comNzRingType):
  @has_finite_coefficient_support A (fun _=>0).
Proof. by exists 0%N. Qed.

(** Source for [finite_coefficient_delta_support]: every single
    monomial has finite support, supporting 3.4.7, p. 325. *)
Lemma finite_coefficient_delta_support (A:comNzRingType) d (a:A):
  has_finite_coefficient_support (fun i=>if i==d then a else 0).
Proof.
exists d.+1=>i hi;case:ifP=>// /eqP h.
by rewrite h ltnn in hi.
Qed.

(** Source for [finite_coefficient_add_support]: finite support
    is preserved by addition, supporting 3.4.7, p. 325. *)
Lemma finite_coefficient_add_support (A:comNzRingType) (f g:nat->A):
  has_finite_coefficient_support f ->has_finite_coefficient_support g ->
  has_finite_coefficient_support (fun i=>f i+g i).
Proof.
move=>[N hN] [M hM];exists (maxn N M)=>i hi.
have hNi:(N<=i)%N:=leq_trans (leq_maxl N M) hi.
have hMi:(M<=i)%N:=leq_trans (leq_maxr N M) hi.
by rewrite (hN i hNi) (hM i hMi) add0r.
Qed.

(** Source for [finite_coefficient_opp_support]: finite support
    is preserved by negation, supporting 3.4.7, p. 325. *)
Lemma finite_coefficient_opp_support (A:comNzRingType) (f:nat->A):
  has_finite_coefficient_support f ->
  has_finite_coefficient_support (fun i=> -f i).
Proof. move=>[N hN];exists N=>i hi;by rewrite hN // oppr0. Qed.

(** Source for [finite_coefficient_multiply_support]: convolution
    preserves finite support, supporting the polynomial-ring
    existence proof for 3.4.7, p. 325. *)
Lemma finite_coefficient_multiply_support (A:comNzRingType) (f g:nat->A):
  has_finite_coefficient_support f ->has_finite_coefficient_support g ->
  has_finite_coefficient_support (natural_coefficient_convolution f g).
Proof.
move=>[N hN] [M hM];exists (N+M)%N=>n hn.
rewrite /natural_coefficient_convolution big_nat_cond;apply:big1=>i /andP[/andP[_ hi] _].
case:(leqP N i)=>hNi;first by rewrite hN // mul0r.
have hiN:(i<=n)%N by move:hi;rewrite ltnS.
have hMi:(M<=n-i)%N.
  rewrite (@leq_subRL i M n hiN).
  exact:leq_trans (leq_add (ltnW hNi) (leqnn M)) hn.
by rewrite hM // mulr0.
Qed.
