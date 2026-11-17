(** Federer (1969), 3.4.12, p. 339, extending 3.4.7, p. 325: the
    finite-dimensional analytic germ ring has unique
    factorization. The original induction uses the actual
    transverse space and its strictly smaller basis. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import ScalarRestriction ComplexScalarSealed ComplexNormUP ComplexModulus ComplexScalarNorm HolomorphicLinear HolomorphicGermArithmeticRepresentatives HolomorphicGermOperationsUP Hom RealNormUP LinearBasis HolomorphicGermRepresentatives HolomorphicGermUP
  HolomorphicGermRingLaws HolomorphicGermRing HolomorphicGermUnits HolomorphicGermDomain
  HolomorphicGermZerothVanishing HolomorphicGermRegularDirection HolomorphicGermTrivialSource
  CommutativeFactorizationUP ComplexWeierstrassRegularUP ComplexWeierstrassRegularProperties
  ComplexWeierstrassDirectionFunctional ComplexWeierstrassTransverseSealed ComplexWeierstrassTransverseBasis
  ComplexWeierstrassHolomorphicFactorization.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [finite_holomorphic_germ_factorization_at_origin]:
    the unique-factorization assertion of 3.4.7, p. 325,
    at the origin of every finite-dimensional normed source.
    The original actual analytic germ is retained. No
    direction, preparation, coefficient factorization, or analytic
    prime is an additional premise. Dimension zero remains. *)
Theorem finite_holomorphic_germ_factorization_at_origin (R:realType) n:
  forall (X:lmodType (ComplexScalars.C R)) (NX:X->R) (hNX:is_complex_norm NX) (e:'I_n->X),
    is_basis e ->is_unique_factorization_commutative_domain
      [the comNzRingType of (@holomorphic_germ_ring R X NX (complex_norm_real hNX) 0)].
Proof.
elim:n=>[|n ih] X NX hNX e he.
- apply:(@holomorphic_germ_trivial_source_factorization R X NX (complex_norm_real hNX) 0)=>x.
  move:x;apply:(@basis_induction (ComplexScalars.C R) (Choice.clone 'I_0 _) X e he (fun x=>x = 0))
    =>[|x y hx hy|a x hx|i].
  + reflexivity.
  + by rewrite hx hy add0r.
  + by rewrite hx scaler0.
  + by have:=ltn_ord i;rewrite ltn0.
- split.
  + move=>alpha beta hProduct;exact:(@holomorphic_germ_no_zero_divisors R X NX (complex_norm_real hNX) 0 alpha beta hProduct).
  + move=>Phi hNonzero.
    case:(pselect (is_commutative_unit Phi))=>[hUnit|hNonunit].
    * exists Phi,[::];split;first exact:hUnit.
      split;first by move=>p;rewrite in_nil.
      by rewrite big_nil mulr1.
    * have [f hRep]:=@holomorphic_germ_has_representative R X NX (complex_norm_real hNX) 0 Phi.
      have hValueZero:holomorphic_representative_value f 0 = 0.
        apply:contrapT=>hn;apply:hNonunit.
        rewrite -hRep;exact:(@holomorphic_germ_unit_iff_nonzero_value R X NX (complex_norm_real hNX) 0 f).2 hn.
      have hZeroth:=(@holomorphic_germ_zeroth_vanishing R X NX (complex_norm_real hNX) 0 f).1 hValueZero.
      rewrite hRep in hZeroth.
      have [k [v hRegular]]:=@holomorphic_germ_regular_direction_exists R X NX hNX Phi hNonzero hZeroth.
      have hV:=@complex_weierstrass_regular_direction_nonzero R X NX hNX Phi k v hRegular.
      have [xi [hXi hUnit]]:=@complex_weierstrass_direction_functional_exists R X NX hNX v hV.
      pose K:=@ComplexWeierstrassTransverse.space R X NX hNX v xi hXi hUnit.
      pose NK:=@ComplexWeierstrassTransverse.norm R X NX hNX v xi hXi hUnit.
      pose hNK:=@ComplexWeierstrassTransverse.norm_laws R X NX hNX v xi hXi hUnit.
      pose inclusion:=@ComplexWeierstrassTransverse.inclusion R X NX hNX v xi hXi hUnit.
      pose projection:=@ComplexWeierstrassTransverse.projection R X NX hNX v xi hXi hUnit.
      have hSplit:=@ComplexWeierstrassTransverse.laws R X NX hNX v xi hXi hUnit.
      have [eK hEK]:=@complex_weierstrass_transverse_basis_exists R X K NX NK v xi inclusion projection n e he hSplit.
      have hKernel:=ih K NK hNK eK hEK.
      have hA:is_unique_factorization_commutative_domain
          [the comNzRingType of (@holomorphic_germ_ring R K NK (complex_norm_real hNK) (projection 0))].
        by rewrite (linear0 projection).
      exact:(@complex_weierstrass_holomorphic_prime_factorization R X K NX NK hNX hNK v xi inclusion projection hSplit
        k Phi hXi hA hRegular).
Qed.
