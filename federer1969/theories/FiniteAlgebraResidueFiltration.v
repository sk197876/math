(** Supporting algebra for Federer (1969), 3.4.8(5), p. 328:
    finite original coefficient modules give comparable maximal-ideal
    filtrations. Construct the original residue quotient internally,
    then apply the proved finite residue-fibre nilpotence connection. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets.
From Federer Require Import RingScalarRestriction RingSubmoduleUP CommutativeIdealUP
  CommutativeFactorizationUP CommutativePrimeTransport CommutativeQuotientUP CommutativeQuotientSealed
  AnalyticRotatedIdealUP AnalyticIdealImageLaws CommutativeIdealPowersSealed CommutativeIdealPowersLaws
  FiniteAlgebraResidueFieldModule FiniteFieldAlgebraNilpotentIdeal IdealPowerRingMap.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [finite_algebra_residue_filtration]: supporting
    original coefficient comparison for the auxiliary sentence in
    Federer 3.4.8(5), p. 328. A finite coefficient module and the
    original residue-field triangle imply M^K subset J for some
    positive K. The residue quotient, finiteness and nilpotence are
    constructed and proved, not added as premises. *)
Theorem finite_algebra_residue_filtration (K:fieldType) (A C:comNzRingType)
    (constants:{rmorphism K->A}) (residue:{rmorphism A->K})
    (phi:{rmorphism A->C}) (scalar:{rmorphism K->C})
    (I:set A) (M J:set C):
  (forall c:K,residue (constants c) = c) ->
  (forall c:K,phi (constants c) = scalar c) ->
  (forall a:A,I a <->residue a = 0) ->
  is_commutative_ideal M ->~M 1 ->
  (forall c:C,M c ->is_commutative_unit (1-c)) ->
  (forall a:A,I a ->M (phi a)) ->
  is_generated_commutative_ideal (phi @` I) J ->
  is_finitely_generated_ring_submodule
    (setT:set [the lmodType A of ring_restricted_space phi C^o]) ->
  exists k,(0<k)%N /\@CommutativeIdealPowers.value C M k `<=` J.
Proof.
move=>hResidueConstants hConstants hI hM hProper hUnit hIM hJ hFinite.
have hJIdeal:=generated_commutative_ideal_laws hJ.
have hJM:J `<=` M.
  apply:(generated_commutative_ideal_minimal hJ hM)=>c [a ha <-];exact:hIM a ha.
have hJProper:~J 1 by move=>h;apply:hProper;exact:hJM 1 h.
pose Q:=@CommutativeIdealQuotient.space K C scalar J hJIdeal hJProper.
pose rho:=@CommutativeIdealQuotient.projection K C scalar J hJIdeal hJProper.
have hRho:=@CommutativeIdealQuotient.laws K C scalar J hJIdeal hJProper.
pose sigma:=GRing.RMorphism.clone K Q (rho \o scalar) _.
have hTriangle a:sigma (residue a) = rho (phi a).
  have hDifference:I (a-constants (residue a)).
    apply:(hI _).2;by rewrite rmorphB hResidueConstants subrr.
  have hJDifference:J (phi (a-constants (residue a))).
    apply:(generated_commutative_ideal_contains hJ);by exists (a-constants (residue a)).
  have hZero:rho (phi (a-constants (residue a))) = 0:=
    (commutative_quotient_kernel hRho _).2 hJDifference.
  rewrite !rmorphB hConstants in hZero.
  apply:esym;exact:subr0_eq hZero.
have hOnto q:exists c:C,rho c = q:=commutative_quotient_surjective hRho q.
have hFiniteQ:=@finite_algebra_residue_field_module A C Q K phi rho residue sigma
  hOnto hTriangle hFinite.
pose N:set Q:=rho @` M.
have hImage:is_analytic_ideal_image rho M N.
  move=>q;split.
  - move=>[c hc hC];exists c;by split.
  - move=>[c [hc hC]];by exists c.
have hNIdeal:=@analytic_ideal_image_ideal C Q rho M N hImage hOnto hM.
have hNUnit q:N q ->is_commutative_unit (1-q).
  move=>[c hc <-].
  have hh:=@commutative_ring_map_unit C Q rho (1-c) (hUnit c hc).
  by rewrite rmorphB rmorph1 in hh.
have [r hNilpotent]:=@finite_field_algebra_nilpotent_ideal K Q sigma N hFiniteQ hNIdeal hNUnit.
exists r.+1;split;first exact:ltn0Sn.
move=>c hC;apply:(commutative_quotient_kernel hRho c).1.
apply:hNilpotent.
apply:(@commutative_ideal_power_decreases Q N r (rho c)).
apply:(@commutative_ideal_power_ring_map C Q rho M N _ r.+1 c hC)=>a ha.
by exists a.
Qed.
