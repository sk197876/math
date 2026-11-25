(** Federer (1969), 3.4.12, pp. 338–339: complex extension
    of the passages identified below. Earlier real and algebraic
    source locators are retained for the results reused here. *)
(** Federer (1969), 3.4.10, p. 337:
    translate a local Hausdorff mass bound back
    to its original centre. The set need
    not be holomorphic. Reuse the project's proved
    invariance under an isometric bijection. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import FiniteCoordinates StandardHermitian StandardHermitian HermitianUP HermitianRealImaginary HermitianComplexNorm UnitaryGroup ScalarRestriction ComplexScalarSealed ComplexNormUP ComplexModulus ComplexScalarNorm ComplexOrderedBases HolomorphicCoordinateNorm HolomorphicLinear HolomorphicUP RealNormUP NormMetric NormClosureLaws GrassmannAbbreviations
  EuclideanInnerProduct InnerNorm InnerMetric HilbertFormCompactness
  HausdorffMeasure HausdorffIsometricBijection.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [holomorphic_local_mass_translation]: the
    change of centre in the compact-mass assertions
    of 3.4.10, p. 337. The
    original set and measure degree are retained;
    no local holomorphicity is needed for this connection. *)
Theorem holomorphic_local_mass_translation (R:realType) n
    (A:set (coordinate_space (ComplexScalars.C R) n)) (a:coordinate_space (ComplexScalars.C R) n) k:
  let hB:=hermitian_real_inner_product (@standard_hermitian_productP R n) in
  let hNX:=complex_norm_real (@holomorphic_coordinate_norm_laws R n) in
  let T:=Topological.clone (real_norm_metric_space hNX) _ in
  (exists O:set (coordinate_space (ComplexScalars.C R) n),@open T O /\O 0 /\
    (@hausdorff_measure R (inner_metric_space hB) k
      ([set x:coordinate_space (ComplexScalars.C R) n|A ((a+x)%R)] `&` O)< +oo)%E) ->
  exists W:set (coordinate_space (ComplexScalars.C R) n),@open T W /\W a /\
    (@hausdorff_measure R (inner_metric_space hB) k (A `&` W)< +oo)%E.
Proof.
move=>hB hNX T [O [hO [hO0 hMass]]].
pose E:=inner_metric_space hB.
pose u:=fun x:T=>(a+x:T).
pose v:=fun x:T=>(x-a:T).
have hV:continuous v.
  have hSame:v=(fun x:T=>(-a+x:T)) by apply:funext=>x;rewrite /v addrC.
  rewrite hSame;exact:real_norm_metric_translate_continuous.
have hVU:cancel u v by move=>x;rewrite /u /v addrAC subrr add0r.
have hUV:cancel v u by move=>x;rewrite /u /v addrC subrK.
exists (v @^-1` O);split.
- exact:(@open_comp T T v O (fun x _=>hV x) hO).
split;first by change (O (a-a));rewrite subrr.
have hDistance (x y:E):@mdist R E (u x) (u y)=@mdist R E x y.
  rewrite !inner_metric_distanceE.
  by rewrite /u opprD addrACA subrr add0r.
have hImage:u @` ([set x|A (a+x)] `&` O)=A `&` (v @^-1` O).
  apply/seteqP;split.
  + move=>x [y [hyA hyO] <-];split;first exact:hyA.
    by change (O (v (u y)));rewrite hVU.
  + move=>x [hxA hxO];exists (v x);last exact:hUV x.
    split;last exact:hxO;by change (A (u (v x)));rewrite hUV.
rewrite -hImage (@hausdorff_bijective_isometry_invariance R E E u v hVU hUV hDistance).
exact:hMass.
Qed.
