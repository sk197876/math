(** Supporting algebra for Federer (1969), 3.4.8(5),
    p. 328: the actual Rees ring of an ideal
    in a Noetherian ring is Noetherian. Finite ideal
    generators, the exact Rees generation theorem and the
    project's Hilbert argument prove the conclusion.
    Source: Bourbaki, Commutative Algebra (1972),
    Chapter III, section 3, no. 1, Lemma 1, p. 197. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets functions.
From Federer Require Import CommutativeIdealUP CommutativeSubringUP
  CommutativePolynomialUP CommutativeSubringRealisationUP
  ReesSubringUP ReesSubringSealed ReesSubringGenerators NoetherianFiniteSubringExtension.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [rees_ring_noetherian]: the original Rees
    subring is Noetherian, the complete assertion of the
    cited Lemma 1 supporting the expanded algebra of
    3.4.8(5), p. 328. Neither finite Rees generators
    nor Rees Noetherianity is supplied as a hypothesis. *)
Theorem rees_ring_noetherian (A B C:comNzRingType)
    (embed:{rmorphism A->B}) (variable:B) (coefficient:B->nat->A)
    (hP:is_commutative_polynomial_ring embed variable coefficient)
    (I:set A) (inclusion:{rmorphism C->B})
    (hC:is_commutative_subring_realisation (@ReesSubring.value A B coefficient I) inclusion):
  is_noetherian_commutative_ring A ->is_commutative_ideal I ->
  is_noetherian_commutative_ring C.
Proof.
move=>hNoetherian hI.
have [F hF]:=hNoetherian I hI.
have hGenerated:=@rees_subring_generated A B embed variable coefficient hP I F hF.
pose generators:=map (fun a:A=>embed a*variable) F.
have hSame:
  [set P:B|(exists a:A,P=embed a) \/exists f:A,f \in F /\P=embed f*variable]=
  [set P:B|(exists a:A,P=embed a) \/P \in generators].
  apply/seteqP;split=>P [hConstant|hOther];first by left.
  - right;have [f [hf ->]]:=hOther;apply/mapP;by exists f.
  - by left.
  - right;move/mapP:hOther=>[f hf ->];exists f;by split.
rewrite hSame in hGenerated.
exact:(@noetherian_finite_subring_extension A B C embed generators
  (@ReesSubring.value A B coefficient I) inclusion hC hNoetherian hGenerated).
Qed.
