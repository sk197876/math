(** Federer (1969), 3.4.7, p. 325: the
    finite-dimensional analytic germ ring is Noetherian.
    This is the original induction at the origin;
    translation to arbitrary centres is proved separately.
    The original division theorem supplies every remainder. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP LinearBasis AnalyticGermRepresentatives AnalyticGermUP
  AnalyticGermRingLaws AnalyticGermRing AnalyticGermUnits AnalyticGermZerothVanishing
  AnalyticGermRegularDirection AnalyticGermTrivialSource CommutativeFactorizationUP
  CommutativeIdealUP CommutativeIdealTrivial WeierstrassRegularUP WeierstrassRegularProperties
  WeierstrassDirectionFunctional WeierstrassTransverseSealed WeierstrassTransverseBasis
  WeierstrassNoetherianIdeal.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [finite_analytic_germ_noetherian_at_origin]:
    the Noetherian assertion of 3.4.7, p. 325,
    at the origin of any original finite-dimensional
    normed source. The actual kernel has one fewer
    basis vector, so the theorem assumes neither a
    Noetherian kernel ring nor a chosen regular divisor. *)
Theorem finite_analytic_germ_noetherian_at_origin (R:realType) n:
  forall (X:lmodType R) (NX:X->R) (hNX:is_real_norm NX) (e:'I_n->X),
    is_basis e ->is_noetherian_commutative_ring
      [the comNzRingType of (@analytic_germ_ring R X NX hNX 0)].
Proof.
elim:n=>[|n ih] X NX hNX e he.
- apply:(@analytic_germ_trivial_source_noetherian R X NX hNX 0)=>x.
  move:x;apply:(@basis_induction R (Choice.clone 'I_0 _) X e he (fun x=>x = 0))
    =>[|x y hx hy|a x hx|i].
  + reflexivity.
  + by rewrite hx hy add0r.
  + by rewrite hx scaler0.
  + by have:=ltn_ord i;rewrite ltn0.
- move=>I hI.
  pose B:=[the comNzRingType of (@analytic_germ_ring R X NX hNX 0)].
  case:(pselect (I 1))=>[hOne|hProper].
  + exact:commutative_ideal_one_finite hI hOne.
  case:(pselect (exists Phi:B,I Phi /\Phi<>0))=>[[Phi [hPhi hNonzero]]|hOnlyZero].
  + have [f hRep]:=@analytic_germ_has_representative R X NX hNX 0 Phi.
    have hValueZero:analytic_representative_value f 0 = 0.
      apply:contrapT=>hn.
      have hUnit:is_commutative_unit Phi.
        rewrite -hRep;exact:(@analytic_germ_unit_iff_nonzero_value R X NX hNX 0 f).2 hn.
      apply:hProper;exact:(@commutative_ideal_unit_contains_one B I hI Phi hPhi hUnit).
    have hZeroth:=(@analytic_germ_zeroth_vanishing R X NX hNX 0 f).1 hValueZero.
    rewrite hRep in hZeroth.
    have [k [v hRegular]]:=@analytic_germ_regular_direction_exists R X NX hNX Phi hNonzero hZeroth.
    have hV:=@weierstrass_regular_direction_nonzero R X NX hNX Phi k v hRegular.
    have [xi [hXi hUnit]]:=@weierstrass_direction_functional_exists R X NX hNX v hV.
    pose K:=@WeierstrassTransverse.space R X NX hNX v xi hXi hUnit.
    pose NK:=@WeierstrassTransverse.norm R X NX hNX v xi hXi hUnit.
    pose hNK:=@WeierstrassTransverse.norm_laws R X NX hNX v xi hXi hUnit.
    pose inclusion:=@WeierstrassTransverse.inclusion R X NX hNX v xi hXi hUnit.
    pose projection:=@WeierstrassTransverse.projection R X NX hNX v xi hXi hUnit.
    have hSplit:=@WeierstrassTransverse.laws R X NX hNX v xi hXi hUnit.
    have [fK hFK]:=@weierstrass_transverse_basis_exists R X K NX NK v xi inclusion projection n e he hSplit.
    have hKernel:=ih K NK hNK fK hFK.
    have hA:is_noetherian_commutative_ring
        [the comNzRingType of (@analytic_germ_ring R K NK hNK (projection 0))].
      by rewrite (linear0 projection).
    exact:(@weierstrass_noetherian_ideal R X K NX NK hNX hNK v xi inclusion projection hSplit
      k Phi I hXi hA hI hPhi hRegular).
  + apply:(commutative_ideal_zero_finite hI)=>Phi hPhi.
    apply:contrapT=>hn;apply:hOnlyZero;by exists Phi.
Qed.
