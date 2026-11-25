(** Federer (1969), 4.1.18, p. 375: the
    mass of each original-U density-current error
    is bounded by the literal ambient L1 field
    error. Open restriction can only decrease mass;
    no finite-mass assertion about q is needed. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals constructive_ereal topology.
From Federer Require Import Hom Bilinear RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  CurrentDomain CurrentSpaces CurrentMassSealed CurrentOpenRestriction CurrentOpenRestrictionMass
  CompactSummableMultivectors CompactSummableMultivectorDensity CompactSummableMultivectorAmbient
  CompactSummableMultivectorDifference CompactSummableCurrentZeroExtension.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [compact_summable_open_density_mass_error]:
    the L1 errors control the two mass pieces
    in the first proposition of Federer 4.1.18,
    p. 375. All exterior degrees, including zero,
    use the same original mass law. *)
Theorem compact_summable_open_density_mass_error (R:realType) (h2:(1+1:R)!=0) n m
    (U:set (R_n R n))
    (hU:forall x,U x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) U x)
    (xi:@compact_summable_multivector_space R h2 n m U hU)
    (xiFull zeta:@compact_summable_multivector_space R h2 n m (fun _=>True)
      (fun x _=>norm_full_domain_interior
        (inner_norm (@euclidean_inner_productP R n)) x)):
  @compact_summable_multivector_value R h2 n m (fun _=>True)
    (fun x _=>norm_full_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) x) xiFull=
    (fun x:current_domain R n (fun _=>True)=>
      @compact_summable_multivector_ambient_value R h2 n m U hU xi (set_val x))->
  let Full:=fun _:R_n R n=>True in
  let hFull:=fun (x:R_n R n) (_:True)=>norm_full_domain_interior
    (inner_norm (@euclidean_inner_productP R n)) x in
  let AF:=@compact_summable_multivector_current R h2 n m Full hFull in
  let restriction:=@current_open_restriction R h2 n m U Full hU hFull
    (fun _ _=>Logic.I) in
  (@CurrentMass.value R h2 n m U hU
    (@compact_summable_multivector_current R h2 n m U hU xi-restriction (AF zeta))<=
    (@compact_summable_multivector_size R h2 n m Full hFull (xiFull-zeta))%:E)%E.
Proof.
move=>hValue.
pose Full:=fun _:R_n R n=>True.
pose hFull:=fun (x:R_n R n) (_:True)=>norm_full_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) x.
pose AF:=@compact_summable_multivector_current R h2 n m Full hFull.
pose restriction:=@current_open_restriction R h2 n m U Full hU hFull
  (fun _ _=>Logic.I).
change ((@CurrentMass.value R h2 n m U hU
  ((@compact_summable_multivector_current R h2 n m U hU xi-
    restriction (AF zeta))%R)<=
  (@compact_summable_multivector_size R h2 n m Full hFull ((xiFull-zeta)%R))%:E)%E).
have hOriginal:=@compact_summable_current_zero_extension R h2 n m U hU xi xiFull hValue.
rewrite hOriginal -(Bilinear.linB (hom_linear restriction)).
have hBound:=@current_open_restriction_mass_bound R h2 n m U Full hU hFull
  (fun _ _=>Logic.I) (AF xiFull-AF zeta).
rewrite (@compact_summable_multivector_current_difference_mass R h2 n m Full hFull
  xiFull zeta) in hBound.
exact:hBound.
Qed.
