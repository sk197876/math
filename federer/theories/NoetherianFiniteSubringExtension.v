(** Supporting algebra for Federer (1969), 3.4.8(5),
    p. 328: an abstract carrier of a finitely generated
    subalgebra of a Noetherian coefficient ring is
    Noetherian. The actual inclusion and lift transfer
    the proved finite-algebra theorem. Source: Bourbaki,
    Commutative Algebra (1972), Chapter III, section 2,
    no. 10, Corollary 3, p. 184, and section 3,
    no. 1, Lemma 1, p. 197. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets functions.
From Federer Require Import CommutativeIdealUP CommutativeSubringUP
  CommutativeSubringRealisationUP CommutativeSubringLiftExistence NoetherianFiniteAlgebra.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [noetherian_finite_subring_extension]: the
    original finitely generated subalgebra is Noetherian,
    supporting the cited Rees-ring Lemma 1. Its carrier
    need only satisfy the independent exact inclusion laws. *)
Theorem noetherian_finite_subring_extension (A B C:comNzRingType)
    (phi:{rmorphism A->B}) (F:seq B) (S:set B) (inclusion:{rmorphism C->B})
    (hC:is_commutative_subring_realisation S inclusion):
  is_noetherian_commutative_ring A ->
  is_generated_commutative_subring
    [set x:B|(exists a:A,x=phi a) \/x \in F] S ->is_noetherian_commutative_ring C.
Proof.
move=>hNoetherian hGenerated.
have hConstants a:S (phi a).
  apply:(generated_commutative_subring_contains hGenerated);left;by exists a.
have [lift hLift]:=@commutative_subring_ring_lift_exists A B C S inclusion hC phi hConstants.
have hEach (i:'I_(size F)):exists c:C,inclusion c=nth 0 F i.
  apply:(@commutative_subring_inclusion_image B S C inclusion hC (nth 0 F i)).1.
  apply:(generated_commutative_subring_contains hGenerated);right;exact:(mem_nth 0 (ltn_ord i)).
have [v hV]:=choice hEach.
pose generators:=map v (enum 'I_(size F)).
apply:(@noetherian_finitely_generated_algebra C generators A lift hNoetherian).
constructor;first by constructor.
- by move=>c hc.
- move=>T hT hContains c _.
  pose image:set B:=fun b=>exists d:C,T d /\inclusion d=b.
  have hImage:is_commutative_subring image.
    constructor.
    + exists 0;split;[exact:commutative_subring_zero hT|exact:rmorph0].
    + exists 1;split;[exact:commutative_subring_one hT|exact:rmorph1].
    + move=>x y [a [ha <-]] [b [hb <-]];exists (a+b);split.
      * exact:(@commutative_subring_add C T hT a b ha hb).
      * exact:rmorphD.
    + move=>x [a [ha <-]];exists (-a);split.
      * exact:(@commutative_subring_opp C T hT a ha).
      * exact:rmorphN.
    + move=>x y [a [ha <-]] [b [hb <-]];exists (a*b);split.
      * exact:(@commutative_subring_multiply C T hT a b ha hb).
      * exact:rmorphM.
  have hGeneratorImages:forall x:B,(exists a:A,x=phi a) \/x \in F ->image x.
    move=>x [[a ->]|hF].
    + exists (lift a);split;last exact:hLift.
      apply:hContains;left;by exists a.
    + have hIndex:(index x F<size F)%N by rewrite index_mem.
      pose i:'I_(size F):=Ordinal hIndex.
      exists (v i);split.
      * apply:hContains;right;apply/mapP;exists i;last reflexivity.
        exact:mem_enum.
      * rewrite (hV i) /i /=;exact:(nth_index 0 hF).
  have hContained:=generated_commutative_subring_minimal hGenerated hImage hGeneratorImages.
  have hMember:S (inclusion c).
    apply:(@commutative_subring_inclusion_image B S C inclusion hC (inclusion c)).2.
    by exists c.
  have [d [hTD hEqual]]:=hContained (inclusion c) hMember.
  have hSame:d=c:=@commutative_subring_inclusion_injective B S C inclusion hC d c hEqual.
  by rewrite -hSame.
Qed.
