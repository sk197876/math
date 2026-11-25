(** Supporting algebra for Federer (1969), 3.4.8(8), p. 329,
    used for the auxiliary coefficient argument in (5), p. 328.
    A single original denominator clears a field functional on a
    finite free module. Reuse the original fraction laws, finite
    denominator theorem and the Chapter 1 coordinate basis. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets.
From Federer Require Import Hom LinearBasis FiniteCoordinates RingFiniteSynthesis
  FractionFieldUP CommutativeDomainUP FiniteFractionDenominators FractionFreeKernel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [fraction_free_functional_denominator]: supporting
    coefficient descent for Federer 3.4.8(8), p. 329 and (5), p. 328.
    One nonzero original denominator makes every value of a field
    functional on embedded original vectors an original scalar.
    No torsion-free hypothesis on a later quotient is assumed. *)
Theorem fraction_free_functional_denominator (A:comNzRingType) (K:fieldType)
    (embed:{rmorphism A->K}) n (ell:Hom {ffun 'I_n->K^o} K^o):
  is_commutative_fraction_field embed ->is_commutative_integral_domain A ->
  exists d:A,exists h:{linear {ffun 'I_n->A^o}->A^o},
    d<>0 /\forall a:{ffun 'I_n->A^o},
      embed (h a) = embed d*ell (fraction_free_coordinates embed a).
Proof.
move=>hField hDomain.
pose e:=@coordinate_basis K n.
pose c (i:nat):K:=oapp (fun j:'I_n=>ell (e j)) 0 (insub i).
have hC (i:'I_n):c i = ell (e i) by rewrite /c valK /=.
have [d [hd hD]]:=@finite_fraction_denominators A K embed hField hDomain n c.
have hEach (i:'I_n):exists a:A,embed d*ell (e i) = embed a.
  have [a ha]:=hD i (ltn_ord i);exists a;by rewrite hC in ha.
have [coefficient hCoefficient]:=choice hEach.
pose h:{linear {ffun 'I_n->A^o}->A^o}:=GRing.Linear.clone _ _ _ _
  (@ring_finite_synthesis A A^o n coefficient) _.
pose q:{linear {ffun 'I_n->K^o}->K^o}:=GRing.Linear.clone _ _ _ _
  (@ring_finite_synthesis K K^o n (fun i=>ell (e i))) _.
have hExpansion v:ell v = q v.
  apply:(@basis_linear_ext K [the finType of 'I_n] [the lmodType K of {ffun 'I_n->K^o}]
    e (@coordinate_basisP K n) K^o (hom_as_linear ell) q)=>i.
  change (ell (e i) = ring_finite_synthesis (fun j=>ell (e j)) (e i)).
  by rewrite /e /coordinate_basis ring_finite_synthesis_generator.
exists d,h;split=>// a.
rewrite hExpansion /q /ring_finite_synthesis mulr_sumr.
change (embed (\sum_(i<n) a i*coefficient i) =
  \sum_(i<n) embed d*(fraction_free_coordinates embed a i*ell (e i))).
rewrite rmorph_sum;apply:eq_bigr=>i _.
rewrite rmorphM /fraction_free_coordinates ffunE -hCoefficient.
by rewrite mulrCA.
Qed.
