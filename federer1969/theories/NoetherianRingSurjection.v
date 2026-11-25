(** Federer (1969), 3.4.7, p. 325: the
    change of centre and transverse ring identifications
    preserve the Noetherian assertion. These supporting
    algebraic proofs use actual ring homomorphisms. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets.
From Federer Require Import CommutativeIdealUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [commutative_ideal_ring_preimage]: ideals
    pull back under ring homomorphisms, supporting the
    original ring identifications in 3.4.7, p. 325. *)
Lemma commutative_ideal_ring_preimage (A B:comNzRingType)
    (f:{rmorphism A->B}) (I:set B):
  is_commutative_ideal I ->is_commutative_ideal (f @^-1` I).
Proof.
move=>hI;constructor.
- change (I (f 0));rewrite rmorph0;exact:commutative_ideal_zero hI.
- move=>x y hx hy;change (I (f (x+y)));rewrite rmorphD.
  exact:(@commutative_ideal_add B I hI (f x) (f y) hx hy).
- move=>x hx;change (I (f (-x)));rewrite rmorphN.
  exact:(@commutative_ideal_opp B I hI (f x) hx).
- move=>x y hy;change (I (f (x*y)));rewrite rmorphM.
  exact:(@commutative_ideal_mul B I hI (f x) (f y) hy).
Qed.

(** Source for [noetherian_ring_surjective_image]: the
    Noetherian property transfers through an actual
    surjective ring map, supporting translation of the
    germ centre in 3.4.7, p. 325. *)
Theorem noetherian_ring_surjective_image (A B:comNzRingType) (f:{rmorphism A->B}):
  (forall y,exists x,f x = y) ->is_noetherian_commutative_ring A ->
  is_noetherian_commutative_ring B.
Proof.
move=>hSurjective hA I hI.
have [F hF]:=hA (f @^-1` I) (commutative_ideal_ring_preimage f hI).
exists (map f F);constructor;first exact:hI.
- move=>y /mapP [x hx ->];exact:(@generated_commutative_ideal_contains A _ _ hF x hx).
- move=>J hJ hGenerators y hy.
  have hPre:=commutative_ideal_ring_preimage f hJ.
  have hContain:f @^-1` I `<=` f @^-1` J.
    apply:(generated_commutative_ideal_minimal hF hPre)=>x hx.
    apply:hGenerators;apply/mapP;by exists x.
  have [x hxy]:=hSurjective y.
  have hx:(f @^-1` I) x by change (I (f x));rewrite hxy.
  have hh:=hContain x hx;change (J (f x)) in hh;by rewrite hxy in hh.
Qed.
