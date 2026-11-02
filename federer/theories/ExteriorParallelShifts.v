(** Exterior algebra behind the shifted endpoint calculation in Federer
    (1969), 2.10.32, pp. 196–197. A product already containing u is
    unchanged when any other factor is shifted by a multiple of u: the
    repeated-u terms vanish by the square-zero laws of 1.3.1, p. 13. These
    supporting identities are derived from the public sealed
    exterior-algebra laws, without choosing an exterior-algebra
    construction. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import Bilinear ExteriorAlgebra.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [exterior_generator_prefix_swap]: supporting
    interchange of the first two factors in
    the expansion of 2.10.32, pp. 196–197,
    using the signed interchange in 1.3.1, p. 13.
    The statement also holds in characteristic two. *)
Lemma exterior_generator_prefix_swap (K : fieldType) (V : lmodType K)
    (u v : V) (z : exterior_space V) :
  wedge (exterior_generator u) (wedge (exterior_generator v) z)=
    -wedge (exterior_generator v) (wedge (exterior_generator u) z).
Proof.
rewrite (@wedge_assoc K V (exterior_generator u) (exterior_generator v) z)
  (@wedge_assoc K V (exterior_generator v) (exterior_generator u) z)
  (@exterior_generator_skew K V u v).
by rewrite -[-wedge (exterior_generator v) (exterior_generator u)]sub0r
  (bilBl (wedge_bilinear V)) (bil0l (wedge_bilinear V)) sub0r.
Qed.

(** Source for [exterior_parallel_shift_prefix]: supporting
    cancellation of the repeated-u terms in the
    three exterior-product expansions of 2.10.32,
    pp. 196–197. No hypothesis about the other
    factors, their dimension or their distinctness is
    required for this algebraic identity. *)
Theorem exterior_parallel_shift_prefix (K : fieldType) (V : lmodType K)
    (I : Type) (s : seq I) (v : I -> V) (a : I -> K) (u : V) :
  wedge (exterior_generator u) (exterior_word [seq v i+a i*:u | i <- s])=
    wedge (exterior_generator u) (exterior_word [seq v i | i <- s]).
Proof.
elim: s=> [|i s IH] //=.
rewrite !exterior_word_cons linearD linearZ
  (bilDl (wedge_bilinear V)) (bilZl (wedge_bilinear V))
  (bilDr (wedge_bilinear V)) (bilZr (wedge_bilinear V))
  [wedge (exterior_generator u) (wedge (exterior_generator u) _)]wedge_assoc
  exterior_generator_square (bil0l (wedge_bilinear V)) scaler0 addr0
  !(@exterior_generator_prefix_swap K V u (v i)) IH.
by [].
Qed.

(** Source for [exterior_parallel_shift_cons]: supporting
    one-factor expansion of the three shifted
    products in 2.10.32, pp. 196–197.
    After choosing the u term in this factor,
    all other parallel shifts disappear by the
    preceding repeated-factor identity. *)
Lemma exterior_parallel_shift_cons (K : fieldType) (V : lmodType K)
    (I : Type) (i : I) (s : seq I) (v : I -> V) (a : I -> K) (u : V) :
  exterior_word [seq v j+a j*:u | j <- i::s]=
    wedge (exterior_generator (v i)) (exterior_word [seq v j+a j*:u | j <- s])+
    a i*:wedge (exterior_generator u) (exterior_word [seq v j | j <- s]).
Proof.
rewrite /= exterior_word_cons linearD linearZ
  (bilDl (wedge_bilinear V)) (bilZl (wedge_bilinear V)).
by rewrite exterior_parallel_shift_prefix.
Qed.

