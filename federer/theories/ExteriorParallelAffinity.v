(** Affine dependence on parallel normal shifts in Federer (1969), 2.10.32,
    pp. 196–197. The product of v_i+a_i u is affine jointly in the scalar
    family a: every term with two occurrences of u vanishes. Prove this
    directly from the square-zero and bilinear laws. This supports the
    printed three-product comparison without assuming a determinant identity
    from an external algebra library. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import Bilinear ExteriorAlgebra ExteriorParallelShifts.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [exterior_parallel_shift_additive]: supporting
    joint affine expansion of the three products
    in 2.10.32, pp. 196–197. The constant
    unshifted product is retained at this stage;
    its top-degree hyperplane vanishing is separate. *)
Theorem exterior_parallel_shift_additive (K : fieldType) (V : lmodType K)
    (I : Type) (s : seq I) (v : I -> V) (a b : I -> K) (u : V) :
  exterior_word [seq v i+(a i+b i)*:u | i <- s]=
    exterior_word [seq v i+a i*:u | i <- s]+
    exterior_word [seq v i+b i*:u | i <- s]-
    exterior_word [seq v i | i <- s].
Proof.
elim: s=> [|i s IH]; first by rewrite /= addrK.
rewrite !exterior_parallel_shift_cons IH
  (bilBr (wedge_bilinear V)) (bilDr (wedge_bilinear V)) scalerDl.
rewrite exterior_word_cons.
pose x := wedge (exterior_generator (v i)) (exterior_word [seq v j+a j*:u | j <- s]).
pose y := wedge (exterior_generator (v i)) (exterior_word [seq v j+b j*:u | j <- s]).
pose z := wedge (exterior_generator (v i)) (exterior_word [seq v j | j <- s]).
pose p := a i*:wedge (exterior_generator u) (exterior_word [seq v j | j <- s]).
pose q := b i*:wedge (exterior_generator u) (exterior_word [seq v j | j <- s]).
change (x+y-z+(p+q)=x+p+(y+q)-z).
by rewrite (addrACA x p y q) (addrAC (x+y) (-z) (p+q)).
Qed.

(** Source for [exterior_parallel_shift_double_difference]: supporting
    difference of the two original endpoint products
    in 2.10.32, p. 197. Subtracting the
    product shifted by gamma from that shifted by
    gamma+2 alpha gives twice the alpha-shifted
    product minus its unshifted constant term. *)
Theorem exterior_parallel_shift_double_difference (K : fieldType) (V : lmodType K)
    (I : Type) (s : seq I) (v : I -> V) (a g : I -> K) (u : V) :
  exterior_word [seq v i+(g i+2*a i)*:u | i <- s]-
    exterior_word [seq v i+g i*:u | i <- s]=
  2*:(exterior_word [seq v i+a i*:u | i <- s]-exterior_word [seq v i | i <- s]).
Proof.
have he : [seq v i+(g i+2*a i)*:u | i <- s]=
    [seq v i+(g i+(a i+a i))*:u | i <- s].
  apply: eq_map=> i; congr (v i+_*:u); congr (g i+_).
  by change ((1+1)*a i=a i+a i); rewrite mulrDl !mul1r.
rewrite he (@exterior_parallel_shift_additive K V I s v g (fun i=>a i+a i) u)
  (@exterior_parallel_shift_additive K V I s v a a u).
pose x := exterior_word [seq v i+a i*:u | i <- s].
pose y := exterior_word [seq v i+g i*:u | i <- s].
pose z := exterior_word [seq v i | i <- s].
change ((y+(x+x-z)-z)-y=(1+1)*:(x-z)).
rewrite scalerDl !scale1r (addrAC (y+(x+x-z)) (-z) (-y))
  (addrAC y (x+x-z) (-y)) subrr add0r (addrACA x (-z) x (-z)).
by rewrite addrA.
Qed.
