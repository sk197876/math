(** Supporting algebra for Federer (1969), 3.4.8(8),
    p. 329: the image of an original
    ring homomorphism has exactly its original
    quotient kernel. Apply the sealed subring
    realisation and existing homomorphism lift. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets.
From Federer Require Import CommutativeSubringUP CommutativeSubringRealisationUP
  CommutativeSubringLiftExistence CommutativeQuotientUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [commutative_ring_image_subring]: the
    original p(Q_j) is a subring, as
    used in 3.4.8(8), p. 329. Its
    membership is exactly the original ring-map image. *)
Lemma commutative_ring_image_subring (A C:comNzRingType) (f:{rmorphism A->C}):
  is_commutative_subring (fun y:C=>exists a:A,y = f a).
Proof.
constructor.
- exists 0;by rewrite rmorph0.
- exists 1;by rewrite rmorph1.
- move=>x y [a ->] [b ->];exists (a+b);by rewrite rmorphD.
- move=>x [a ->];exists (-a);by rewrite rmorphN.
- move=>x y [a ->] [b ->];exists (a*b);by rewrite rmorphM.
Qed.

(** Source for [commutative_ring_image_quotient]: the
    actual image carrier is a quotient by
    the original map kernel, the p(Q_j)
    identification used in 3.4.8(8), p. 329.
    Its surjection and exact kernel are
    proved through the independent image laws. *)
Theorem commutative_ring_image_quotient (A C D:comNzRingType) (f:{rmorphism A->C})
  (inclusion:{rmorphism D->C}):
  is_commutative_subring_realisation (fun y:C=>exists a:A,y = f a) inclusion ->
  exists projection:{rmorphism A->D},
    (forall a:A,inclusion (projection a) = f a) /\
    is_commutative_ideal_quotient (fun a:A=>f a = 0) projection.
Proof.
move=>hImage.
have hOriginal a:exists x:A,f a = f x by exists a.
have [projection hProjection]:=@commutative_subring_ring_lift_exists A C D
  (fun y:C=>exists a:A,y = f a) inclusion hImage f hOriginal.
have hInjective:=commutative_subring_inclusion_injective hImage.
exists projection;split;first exact:hProjection.
constructor.
- move=>d.
  have hMember:(exists a:A,inclusion d = f a).
    apply:(commutative_subring_inclusion_image hImage (inclusion d)).2;by exists d.
  have [a hA]:=hMember;exists a;apply:hInjective.
  by rewrite hProjection -hA.
- move=>a;split.
  + move=>hZero;by rewrite -(hProjection a) hZero rmorph0.
  + move=>hZero;apply:hInjective;by rewrite hProjection hZero rmorph0.
Qed.
