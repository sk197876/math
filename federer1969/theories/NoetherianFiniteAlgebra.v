(** Supporting algebra for Federer (1969), 3.4.8(5),
    p. 328: a finitely generated commutative algebra over
    a Noetherian ring is Noetherian. Iterated opaque
    polynomial extensions prove this without choosing a
    polynomial representation of the original algebra.
    Source: Bourbaki, Commutative Algebra (1972), Chapter III,
    section 2, no. 10, Corollary 3, p. 184. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets.
From Federer Require Import CommutativeIdealUP CommutativeSubringUP
  CommutativePolynomialUP CommutativePolynomialSealed CommutativePolynomialEvaluationUP
  CommutativePolynomialEvaluationSealed CommutativePolynomialHilbertBasis NoetherianRingSurjection.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [noetherian_finitely_generated_algebra]:
    Bourbaki (1972), Chapter III, section 2, no. 10,
    Corollary 3, p. 184. This supports the expanded
    ideal-closure algebra for 3.4.8(5), p. 328.
    Only the independent least-subring generation law
    and finitely many original generators are assumed. *)
Theorem noetherian_finitely_generated_algebra (C:comNzRingType) (F:seq C):
  forall (A:comNzRingType) (phi:{rmorphism A->C}),
  is_noetherian_commutative_ring A ->
  is_generated_commutative_subring
    (fun x:C=>(exists a:A,x=phi a) \/x \in F) setT ->
  is_noetherian_commutative_ring C.
Proof.
elim:F=>[|c F ih] A phi hNoetherian hGenerated.
- have hImage:is_commutative_subring (fun x:C=>exists a:A,x=phi a).
    constructor.
    + exists 0;by rewrite rmorph0.
    + exists 1;by rewrite rmorph1.
    + move=>x y [a ->] [b ->];exists (a+b);by rewrite rmorphD.
    + move=>x [a ->];exists (-a);by rewrite rmorphN.
    + move=>x y [a ->] [b ->];exists (a*b);by rewrite rmorphM.
  have hOnto:forall y:C,exists a:A,phi a=y.
    move=>y.
    have hContained:setT `<=` (fun x:C=>exists a:A,x=phi a).
      apply:(generated_commutative_subring_minimal hGenerated hImage)=>x [h|h];first exact:h.
      by rewrite in_nil in h.
    have [a hA]:=hContained y Logic.I;exists a;exact:esym hA.
  exact:(@noetherian_ring_surjective_image A C phi hOnto hNoetherian).
- pose P:=CommutativePolynomial.space A.
  pose embed:=CommutativePolynomial.embed A.
  pose variable:=CommutativePolynomial.variable A.
  pose coefficient:=@CommutativePolynomial.coefficient A.
  have hP:=CommutativePolynomial.laws A.
  pose E:=@CommutativePolynomialEvaluation.map A P C embed variable coefficient hP phi c.
  have hE:=@CommutativePolynomialEvaluation.laws A P C embed variable coefficient hP phi c.
  have hNoetherianP:is_noetherian_commutative_ring P:=
    @commutative_polynomial_ring_noetherian A P embed variable coefficient hP hNoetherian.
  apply:(ih P E hNoetherianP).
  constructor.
  + by constructor.
  + by move=>x hx.
  + move=>S hS hContains.
    apply:(generated_commutative_subring_minimal hGenerated hS)=>x [[a ->]|hMem].
    * apply:hContains;left;exists (embed a).
      exact:esym (@polynomial_evaluation_constants A P C embed variable phi c E hE a).
    * move:hMem;rewrite in_cons;move/orP=>[/eqP ->|hF].
      -- apply:hContains;left;exists variable.
         exact:esym (@polynomial_evaluation_variable A P C embed variable phi c E hE).
      -- apply:hContains;by right.
Qed.
