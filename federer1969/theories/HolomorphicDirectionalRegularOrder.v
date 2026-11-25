(** Federer (1969), 3.4.12, p. 339, extending 3.4.8(8),
    p. 329: an actual positive complex directional derivative
    gives a first nonzero order along that same direction. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import Hom RealNormUP ScalarRestriction ComplexScalarSealed ComplexNormUP
  SymmetricForms ContinuousMultilinearUP ContinuousMultilinearSealed HolomorphicGermUP
  HolomorphicGermJetsSealed HolomorphicGermFormsUP HolomorphicGermFormsSealed
  HolomorphicReductionLociUP ComplexWeierstrassRegularUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [holomorphic_directional_regular_order_exists]:
    the original r(j) along the prescribed complex coordinate,
    3.4.12, p. 339. The zeroth actual jet vanishes. *)
Theorem holomorphic_directional_regular_order_exists (R:realType) (X:lmodType (ComplexScalars.C R))
    (NX:X->R) (hNX:is_complex_norm NX) (alpha:holomorphic_germ_space (complex_norm_real hNX) (0:X)) (v:X):
  @HolomorphicGermJets.value R X NX (complex_norm_real hNX) 0 0%N alpha=0 ->
  has_nonzero_holomorphic_directional_jet hNX alpha v ->
  exists k,is_complex_weierstrass_regular_germ hNX alpha k v.
Proof.
move=>hZeroth [j [hPositive hJ]].
pose value k:=@HolomorphicGermForms.value R X NX hNX 0 k alpha [tuple v|_<k].
have hExists:exists k,value k!=0 by exists j;apply/eqP;exact:hJ.
have [k hK hMinimal]:=ex_minnP hExists.
have hKPositive:(0<k)%N.
  case:k hK hMinimal=>[|k] hK hMinimal;last exact:ltn0Sn.
  by rewrite /value (@HolomorphicGermForms.laws R X NX hNX 0 0%N alpha) hZeroth linear0 eqxx in hK.
exists k;split;first exact:hKPositive.
split;last by apply/eqP;exact:hK.
move=>i hi;case:(eqVneq (value i) 0)=>[hZero|hNonzero];first exact:hZero.
have hKI:=hMinimal i hNonzero.
have hFalse:=leq_ltn_trans hKI hi;by rewrite ltnn in hFalse.
Qed.
